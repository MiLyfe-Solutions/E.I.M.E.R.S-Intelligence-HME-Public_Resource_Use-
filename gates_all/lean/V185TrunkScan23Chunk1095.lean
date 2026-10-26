import V185TrunkScan23Chunk1094

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6482674 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_6482674 : Nat := 118140960795 + 6482674 * 2 ^ 59
def prefixEnd_6482674 : Nat := 4983230072969 + 3 ^ 40 * 6482674 * 2
def baseEnd_6482674 : Nat := 3328727688404874741861731

theorem tailTrace_6482674 : CollatzResearch.WordTrace tailWord_6482674 prefixEnd_6482674 3328727688404874741861731 := by
  unfold tailWord_6482674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59110636329096681354847769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157628363544257816946260717 59110636329096681354847769)
  ·
    refine ⟨44332977246822511016135827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59110636329096681354847769 44332977246822511016135827)
    ·
      refine ⟨66499465870233766524203741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44332977246822511016135827 66499465870233766524203741)
      ·
        refine ⟨24937299701337662446576403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66499465870233766524203741 24937299701337662446576403)
        ·
          refine ⟨37405949552006493669864605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24937299701337662446576403 37405949552006493669864605)
          ·
            refine ⟨14027231082002435126199227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37405949552006493669864605 14027231082002435126199227)
            ·
              refine ⟨21040846623003652689298841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14027231082002435126199227 21040846623003652689298841)
              ·
                refine ⟨15780634967252739516974131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21040846623003652689298841 15780634967252739516974131)
                ·
                  refine ⟨23670952450879109275461197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15780634967252739516974131 23670952450879109275461197)
                  ·
                    refine ⟨8876607169079665978297949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23670952450879109275461197 8876607169079665978297949)
                    ·
                      refine ⟨3328727688404874741861731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876607169079665978297949 3328727688404874741861731)
                      ·
                        rfl

theorem cell23_6482674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_6482674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482674 prefixEnd_6482674 := by exact prefixLift 6482674
  have htrace : WordTrace (prefixWord ++ tailWord_6482674) baseStart_6482674 baseEnd_6482674 := by
    simpa [prefixWord, tailWord_6482674, baseEnd_6482674] using wordTrace_append hprefix tailTrace_6482674
  have hstable : (prefixWord ++ tailWord_6482674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482674).length < 2 ^ (prefixWord ++ tailWord_6482674).sum := by decide
  have hdescent : baseEnd_6482674 < baseStart_6482674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482742 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6482742 : Nat := 118140960795 + 6482742 * 2 ^ 59
def prefixEnd_6482742 : Nat := 4983230072969 + 3 ^ 40 * 6482742 * 2
def baseEnd_6482742 : Nat := 3328762605089380475811419

theorem tailTrace_6482742 : CollatzResearch.WordTrace tailWord_6482742 prefixEnd_6482742 3328762605089380475811419 := by
  unfold tailWord_6482742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14777814092508773314554155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157630016986760248688577653 14777814092508773314554155)
  ·
    refine ⟨22166721138763159971831233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14777814092508773314554155 22166721138763159971831233)
    ·
      refine ⟨16625040854072369978873425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22166721138763159971831233 16625040854072369978873425)
      ·
        refine ⟨12468780640554277484155069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16625040854072369978873425 12468780640554277484155069)
        ·
          refine ⟨4675792740207854056558151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12468780640554277484155069 4675792740207854056558151)
          ·
            refine ⟨7013689110311781084837227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4675792740207854056558151 7013689110311781084837227)
            ·
              refine ⟨10520533665467671627255841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013689110311781084837227 10520533665467671627255841)
              ·
                refine ⟨7890400249100753720441881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10520533665467671627255841 7890400249100753720441881)
                ·
                  refine ⟨5917800186825565290331411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7890400249100753720441881 5917800186825565290331411)
                  ·
                    refine ⟨8876700280238347935497117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5917800186825565290331411 8876700280238347935497117)
                    ·
                      refine ⟨3328762605089380475811419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876700280238347935497117 3328762605089380475811419)
                      ·
                        rfl

theorem cell23_6482742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6482742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482742 prefixEnd_6482742 := by exact prefixLift 6482742
  have htrace : WordTrace (prefixWord ++ tailWord_6482742) baseStart_6482742 baseEnd_6482742 := by
    simpa [prefixWord, tailWord_6482742, baseEnd_6482742] using wordTrace_append hprefix tailTrace_6482742
  have hstable : (prefixWord ++ tailWord_6482742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482742).length < 2 ^ (prefixWord ++ tailWord_6482742).sum := by decide
  have hdescent : baseEnd_6482742 < baseStart_6482742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482764 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_6482764 : Nat := 118140960795 + 6482764 * 2 ^ 59
def prefixEnd_6482764 : Nat := 4983230072969 + 3 ^ 40 * 6482764 * 2
def baseEnd_6482764 : Nat := 3328773901663779389736317

theorem tailTrace_6482764 : CollatzResearch.WordTrace tailWord_6482764 prefixEnd_6482764 3328773901663779389736317 := by
  unfold tailWord_6482764
  simp only [CollatzResearch.WordTrace]
  refine ⟨118222913943030335395083673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157630551924040447193444897 118222913943030335395083673)
  ·
    refine ⟨88667185457272751546312755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118222913943030335395083673 88667185457272751546312755)
    ·
      refine ⟨133000778185909127319469133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88667185457272751546312755 133000778185909127319469133)
      ·
        refine ⟨49875291819715922744800925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133000778185909127319469133 49875291819715922744800925)
        ·
          refine ⟨18703234432393471029300347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49875291819715922744800925 18703234432393471029300347)
          ·
            refine ⟨28054851648590206543950521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18703234432393471029300347 28054851648590206543950521)
            ·
              refine ⟨21041138736442654907962891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28054851648590206543950521 21041138736442654907962891)
              ·
                refine ⟨31561708104663982361944337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21041138736442654907962891 31561708104663982361944337)
                ·
                  refine ⟨23671281078497986771458253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31561708104663982361944337 23671281078497986771458253)
                  ·
                    refine ⟨8876730404436745039296845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23671281078497986771458253 8876730404436745039296845)
                    ·
                      refine ⟨3328773901663779389736317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876730404436745039296845 3328773901663779389736317)
                      ·
                        rfl

theorem cell23_6482764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_6482764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482764 prefixEnd_6482764 := by exact prefixLift 6482764
  have htrace : WordTrace (prefixWord ++ tailWord_6482764) baseStart_6482764 baseEnd_6482764 := by
    simpa [prefixWord, tailWord_6482764, baseEnd_6482764] using wordTrace_append hprefix tailTrace_6482764
  have hstable : (prefixWord ++ tailWord_6482764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482764).length < 2 ^ (prefixWord ++ tailWord_6482764).sum := by decide
  have hdescent : baseEnd_6482764 < baseStart_6482764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482765 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6482765 : Nat := 118140960795 + 6482765 * 2 ^ 59
def prefixEnd_6482765 : Nat := 4983230072969 + 3 ^ 40 * 6482765 * 2
def baseEnd_6482765 : Nat := 3328774415144433885823813

theorem tailTrace_6482765 : CollatzResearch.WordTrace tailWord_6482765 prefixEnd_6482765 3328774415144433885823813 := by
  unfold tailWord_6482765
  simp only [CollatzResearch.WordTrace]
  refine ⟨236445864359057047960953749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157630576239371365307302499 236445864359057047960953749)
  ·
    refine ⟨11083399891830799123169707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236445864359057047960953749 11083399891830799123169707)
    ·
      refine ⟨16625099837746198684754561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11083399891830799123169707 16625099837746198684754561)
      ·
        refine ⟨12468824878309649013565921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16625099837746198684754561 12468824878309649013565921)
        ·
          refine ⟨9351618658732236760174441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12468824878309649013565921 9351618658732236760174441)
          ·
            refine ⟨7013713994049177570130831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9351618658732236760174441 7013713994049177570130831)
            ·
              refine ⟨10520570991073766355196247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013713994049177570130831 10520570991073766355196247)
              ·
                refine ⟨15780856486610649532794371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10520570991073766355196247 15780856486610649532794371)
                ·
                  refine ⟨23671284729915974299191557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15780856486610649532794371 23671284729915974299191557)
                  ·
                    refine ⟨4438365886859245181098417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23671284729915974299191557 4438365886859245181098417)
                    ·
                      refine ⟨3328774415144433885823813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438365886859245181098417 3328774415144433885823813)
                      ·
                        rfl

theorem cell23_6482765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6482765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482765 prefixEnd_6482765 := by exact prefixLift 6482765
  have htrace : WordTrace (prefixWord ++ tailWord_6482765) baseStart_6482765 baseEnd_6482765 := by
    simpa [prefixWord, tailWord_6482765, baseEnd_6482765] using wordTrace_append hprefix tailTrace_6482765
  have hstable : (prefixWord ++ tailWord_6482765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482765).length < 2 ^ (prefixWord ++ tailWord_6482765).sum := by decide
  have hdescent : baseEnd_6482765 < baseStart_6482765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482888 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_6482888 : Nat := 118140960795 + 6482888 * 2 ^ 59
def prefixEnd_6482888 : Nat := 4983230072969 + 3 ^ 40 * 6482888 * 2
def baseEnd_6482888 : Nat := 3328837573264936904585747

theorem tailTrace_6482888 : CollatzResearch.WordTrace tailWord_6482888 prefixEnd_6482888 3328837573264936904585747 := by
  unfold tailWord_6482888
  simp only [CollatzResearch.WordTrace]
  refine ⟨118225175268805719983840659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157633567025074293311787545 118225175268805719983840659)
  ·
    refine ⟨177337762903208579975760989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118225175268805719983840659 177337762903208579975760989)
    ·
      refine ⟨66501661088703217490910371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177337762903208579975760989 66501661088703217490910371)
      ·
        refine ⟨99752491633054826236365557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66501661088703217490910371 99752491633054826236365557)
        ·
          refine ⟨9351796090598889959659271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99752491633054826236365557 9351796090598889959659271)
          ·
            refine ⟨14027694135898334939488907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9351796090598889959659271 14027694135898334939488907)
            ·
              refine ⟨21041541203847502409233361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14027694135898334939488907 21041541203847502409233361)
              ·
                refine ⟨15781155902885626806925021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21041541203847502409233361 15781155902885626806925021)
                ·
                  refine ⟨5917933463582110052596883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15781155902885626806925021 5917933463582110052596883)
                  ·
                    refine ⟨8876900195373165078895325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5917933463582110052596883 8876900195373165078895325)
                    ·
                      refine ⟨3328837573264936904585747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876900195373165078895325 3328837573264936904585747)
                      ·
                        rfl

theorem cell23_6482888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_6482888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482888 prefixEnd_6482888 := by exact prefixLift 6482888
  have htrace : WordTrace (prefixWord ++ tailWord_6482888) baseStart_6482888 baseEnd_6482888 := by
    simpa [prefixWord, tailWord_6482888, baseEnd_6482888] using wordTrace_append hprefix tailTrace_6482888
  have hstable : (prefixWord ++ tailWord_6482888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482888).length < 2 ^ (prefixWord ++ tailWord_6482888).sum := by decide
  have hdescent : baseEnd_6482888 < baseStart_6482888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482898 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6482898 : Nat := 118140960795 + 6482898 * 2 ^ 59
def prefixEnd_6482898 : Nat := 4983230072969 + 3 ^ 40 * 6482898 * 2
def baseEnd_6482898 : Nat := 3328842708071481865460701

theorem tailTrace_6482898 : CollatzResearch.WordTrace tailWord_6482898 prefixEnd_6482898 3328842708071481865460701 := by
  unfold tailWord_6482898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59112678816893802918886337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157633810178383474450363565 59112678816893802918886337)
  ·
    refine ⟨44334509112670352189164753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59112678816893802918886337 44334509112670352189164753)
    ·
      refine ⟨33250881834502764141873565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44334509112670352189164753 33250881834502764141873565)
      ·
        refine ⟨12469080687938536553202587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33250881834502764141873565 12469080687938536553202587)
        ·
          refine ⟨18703621031907804829803881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12469080687938536553202587 18703621031907804829803881)
          ·
            refine ⟨14027715773930853622352911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18703621031907804829803881 14027715773930853622352911)
            ·
              refine ⟨21041573660896280433529367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14027715773930853622352911 21041573660896280433529367)
              ·
                refine ⟨31562360491344420650294051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21041573660896280433529367 31562360491344420650294051)
                ·
                  refine ⟨47343540737016630975441077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31562360491344420650294051 47343540737016630975441077)
                  ·
                    refine ⟨4438456944095309153947601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47343540737016630975441077 4438456944095309153947601)
                    ·
                      refine ⟨3328842708071481865460701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438456944095309153947601 3328842708071481865460701)
                      ·
                        rfl

theorem cell23_6482898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6482898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482898 prefixEnd_6482898 := by exact prefixLift 6482898
  have htrace : WordTrace (prefixWord ++ tailWord_6482898) baseStart_6482898 baseEnd_6482898 := by
    simpa [prefixWord, tailWord_6482898, baseEnd_6482898] using wordTrace_append hprefix tailTrace_6482898
  have hstable : (prefixWord ++ tailWord_6482898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482898).length < 2 ^ (prefixWord ++ tailWord_6482898).sum := by decide
  have hdescent : baseEnd_6482898 < baseStart_6482898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482904 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 1, 6]
def baseStart_6482904 : Nat := 118140960795 + 6482904 * 2 ^ 59
def prefixEnd_6482904 : Nat := 4983230072969 + 3 ^ 40 * 6482904 * 2
def baseEnd_6482904 : Nat := 1109615262985136280661891

theorem tailTrace_6482904 : CollatzResearch.WordTrace tailWord_6482904 prefixEnd_6482904 1109615262985136280661891 := by
  unfold tailWord_6482904
  simp only [CollatzResearch.WordTrace]
  refine ⟨118225467052776737350131883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157633956070368983133509177 118225467052776737350131883)
  ·
    refine ⟨177338200579165106025197825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118225467052776737350131883 177338200579165106025197825)
    ·
      refine ⟨133003650434373829518898369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177338200579165106025197825 133003650434373829518898369)
      ·
        refine ⟨99752737825780372139173777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133003650434373829518898369 99752737825780372139173777)
        ·
          refine ⟨74814553369335279104380333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99752737825780372139173777 74814553369335279104380333)
          ·
            refine ⟨28055457513500729664142625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74814553369335279104380333 28055457513500729664142625)
            ·
              refine ⟨21041593135125547248106969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28055457513500729664142625 21041593135125547248106969)
              ·
                refine ⟨15781194851344160436080227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21041593135125547248106969 15781194851344160436080227)
                ·
                  refine ⟨23671792277016240654120341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15781194851344160436080227 23671792277016240654120341)
                  ·
                    refine ⟨1109615262985136280661891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23671792277016240654120341 1109615262985136280661891)
                    ·
                      rfl

theorem cell23_6482904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_6482904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482904 prefixEnd_6482904 := by exact prefixLift 6482904
  have htrace : WordTrace (prefixWord ++ tailWord_6482904) baseStart_6482904 baseEnd_6482904 := by
    simpa [prefixWord, tailWord_6482904, baseEnd_6482904] using wordTrace_append hprefix tailTrace_6482904
  have hstable : (prefixWord ++ tailWord_6482904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482904).length < 2 ^ (prefixWord ++ tailWord_6482904).sum := by decide
  have hdescent : baseEnd_6482904 < baseStart_6482904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482905 : List Nat := [1, 2, 1, 2, 5, 2, 2, 3, 1, 1, 3]
def baseStart_6482905 : Nat := 118140960795 + 6482905 * 2 ^ 59
def prefixEnd_6482905 : Nat := 4983230072969 + 3 ^ 40 * 6482905 * 2
def baseEnd_6482905 : Nat := 3328846302436063338073169

theorem tailTrace_6482905 : CollatzResearch.WordTrace tailWord_6482905 prefixEnd_6482905 3328846302436063338073169 := by
  unfold tailWord_6482905
  simp only [CollatzResearch.WordTrace]
  refine ⟨236450970578549851871050169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157633980385699901247366779 236450970578549851871050169)
  ·
    refine ⟨177338227933912388903287627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236450970578549851871050169 177338227933912388903287627)
    ·
      refine ⟨266007341900868583354931441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177338227933912388903287627 266007341900868583354931441)
      ·
        refine ⟨199505506425651437516198581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266007341900868583354931441 199505506425651437516198581)
        ·
          refine ⟨18703641227404822267143617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199505506425651437516198581 18703641227404822267143617)
          ·
            refine ⟨14027730920553616700357713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18703641227404822267143617 14027730920553616700357713)
            ·
              refine ⟨10520798190415212525268285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14027730920553616700357713 10520798190415212525268285)
              ·
                refine ⟨3945299321405704696975607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10520798190415212525268285 3945299321405704696975607)
                ·
                  refine ⟨5917948982108557045463411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945299321405704696975607 5917948982108557045463411)
                  ·
                    refine ⟨8876923473162835568195117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5917948982108557045463411 8876923473162835568195117)
                    ·
                      refine ⟨3328846302436063338073169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876923473162835568195117 3328846302436063338073169)
                      ·
                        rfl

theorem cell23_6482905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_6482905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482905 prefixEnd_6482905 := by exact prefixLift 6482905
  have htrace : WordTrace (prefixWord ++ tailWord_6482905) baseStart_6482905 baseEnd_6482905 := by
    simpa [prefixWord, tailWord_6482905, baseEnd_6482905] using wordTrace_append hprefix tailTrace_6482905
  have hstable : (prefixWord ++ tailWord_6482905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482905).length < 2 ^ (prefixWord ++ tailWord_6482905).sum := by decide
  have hdescent : baseEnd_6482905 < baseStart_6482905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482978 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_6482978 : Nat := 118140960795 + 6482978 * 2 ^ 59
def prefixEnd_6482978 : Nat := 4983230072969 + 3 ^ 40 * 6482978 * 2
def baseEnd_6482978 : Nat := 3328883786523841552460333

theorem tailTrace_6482978 : CollatzResearch.WordTrace tailWord_6482978 prefixEnd_6482978 3328883786523841552460333 := by
  unfold tailWord_6482978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59113408276821346334614397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157635755404856923558971725 59113408276821346334614397)
  ·
    refine ⟨22167528103808004875480399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59113408276821346334614397 22167528103808004875480399)
    ·
      refine ⟨33251292155712007313220599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22167528103808004875480399 33251292155712007313220599)
      ·
        refine ⟨49876938233568010969830899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33251292155712007313220599 49876938233568010969830899)
        ·
          refine ⟨74815407350352016454746349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49876938233568010969830899 74815407350352016454746349)
          ·
            refine ⟨28055777756382006170529881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74815407350352016454746349 28055777756382006170529881)
            ·
              refine ⟨21041833317286504627897411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28055777756382006170529881 21041833317286504627897411)
              ·
                refine ⟨31562749975929756941846117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21041833317286504627897411 31562749975929756941846117)
                ·
                  refine ⟨5918015620486829426596147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31562749975929756941846117 5918015620486829426596147)
                  ·
                    refine ⟨8877023430730244139894221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5918015620486829426596147 8877023430730244139894221)
                    ·
                      refine ⟨3328883786523841552460333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8877023430730244139894221 3328883786523841552460333)
                      ·
                        rfl

theorem cell23_6482978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_6482978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482978 prefixEnd_6482978 := by exact prefixLift 6482978
  have htrace : WordTrace (prefixWord ++ tailWord_6482978) baseStart_6482978 baseEnd_6482978 := by
    simpa [prefixWord, tailWord_6482978, baseEnd_6482978] using wordTrace_append hprefix tailTrace_6482978
  have hstable : (prefixWord ++ tailWord_6482978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482978).length < 2 ^ (prefixWord ++ tailWord_6482978).sum := by decide
  have hdescent : baseEnd_6482978 < baseStart_6482978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482994 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_6482994 : Nat := 118140960795 + 6482994 * 2 ^ 59
def prefixEnd_6482994 : Nat := 4983230072969 + 3 ^ 40 * 6482994 * 2
def baseEnd_6482994 : Nat := 1109630667404771163286753

theorem tailTrace_6482994 : CollatzResearch.WordTrace tailWord_6482994 prefixEnd_6482994 1109630667404771163286753 := by
  unfold tailWord_6482994
  simp only [CollatzResearch.WordTrace]
  refine ⟨59113554168806855017760009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157636144450151613380693357 59113554168806855017760009)
  ·
    refine ⟨44335165626605141263320007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59113554168806855017760009 44335165626605141263320007)
    ·
      refine ⟨66502748439907711894980011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44335165626605141263320007 66502748439907711894980011)
      ·
        refine ⟨99754122659861567842470017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66502748439907711894980011 99754122659861567842470017)
        ·
          refine ⟨74815591994896175881852513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99754122659861567842470017 74815591994896175881852513)
          ·
            refine ⟨56111693996172131911389385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74815591994896175881852513 56111693996172131911389385)
            ·
              refine ⟨42083770497129098933542039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56111693996172131911389385 42083770497129098933542039)
              ·
                refine ⟨63125655745693648400313059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42083770497129098933542039 63125655745693648400313059)
                ·
                  refine ⟨94688483618540472600469589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63125655745693648400313059 94688483618540472600469589)
                  ·
                    refine ⟨1109630667404771163286753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94688483618540472600469589 1109630667404771163286753)
                    ·
                      rfl

theorem cell23_6482994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_6482994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482994 prefixEnd_6482994 := by exact prefixLift 6482994
  have htrace : WordTrace (prefixWord ++ tailWord_6482994) baseStart_6482994 baseEnd_6482994 := by
    simpa [prefixWord, tailWord_6482994, baseEnd_6482994] using wordTrace_append hprefix tailTrace_6482994
  have hstable : (prefixWord ++ tailWord_6482994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482994).length < 2 ^ (prefixWord ++ tailWord_6482994).sum := by decide
  have hdescent : baseEnd_6482994 < baseStart_6482994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483005 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_6483005 : Nat := 118140960795 + 6483005 * 2 ^ 59
def prefixEnd_6483005 : Nat := 4983230072969 + 3 ^ 40 * 6483005 * 2
def baseEnd_6483005 : Nat := 3328897650501512946822709

theorem tailTrace_6483005 : CollatzResearch.WordTrace tailWord_6483005 prefixEnd_6483005 3328897650501512946822709 := by
  unfold tailWord_6483005
  simp only [CollatzResearch.WordTrace]
  refine ⟨236454617878187568949690469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157636411918791712633126979 236454617878187568949690469)
  ·
    refine ⟨44335240852160169178066963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236454617878187568949690469 44335240852160169178066963)
    ·
      refine ⟨66502861278240253767100445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44335240852160169178066963 66502861278240253767100445)
      ·
        refine ⟨24938572979340095162662667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66502861278240253767100445 24938572979340095162662667)
        ·
          refine ⟨37407859469010142743994001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24938572979340095162662667 37407859469010142743994001)
          ·
            refine ⟨28055894601757607057995501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37407859469010142743994001 28055894601757607057995501)
            ·
              refine ⟨10520960475659102646748313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28055894601757607057995501 10520960475659102646748313)
              ·
                refine ⟨7890720356744326985061235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10520960475659102646748313 7890720356744326985061235)
                ·
                  refine ⟨11836080535116490477591853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7890720356744326985061235 11836080535116490477591853)
                  ·
                    refine ⟨4438530200668683929096945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11836080535116490477591853 4438530200668683929096945)
                    ·
                      refine ⟨3328897650501512946822709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438530200668683929096945 3328897650501512946822709)
                      ·
                        rfl

theorem cell23_6483005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_6483005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483005 prefixEnd_6483005 := by exact prefixLift 6483005
  have htrace : WordTrace (prefixWord ++ tailWord_6483005) baseStart_6483005 baseEnd_6483005 := by
    simpa [prefixWord, tailWord_6483005, baseEnd_6483005] using wordTrace_append hprefix tailTrace_6483005
  have hstable : (prefixWord ++ tailWord_6483005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483005).length < 2 ^ (prefixWord ++ tailWord_6483005).sum := by decide
  have hdescent : baseEnd_6483005 < baseStart_6483005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483018 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_6483018 : Nat := 118140960795 + 6483018 * 2 ^ 59
def prefixEnd_6483018 : Nat := 4983230072969 + 3 ^ 40 * 6483018 * 2
def baseEnd_6483018 : Nat := 3328904325750021395960149

theorem tailTrace_6483018 : CollatzResearch.WordTrace tailWord_6483018 prefixEnd_6483018 3328904325750021395960149 := by
  unfold tailWord_6483018
  simp only [CollatzResearch.WordTrace]
  refine ⟨59113773006785118042478427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157636728018093648113275805 59113773006785118042478427)
  ·
    refine ⟨88670659510177677063717641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59113773006785118042478427 88670659510177677063717641)
    ·
      refine ⟨66502994632633257797788231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88670659510177677063717641 66502994632633257797788231)
      ·
        refine ⟨99754491948949886696682347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66502994632633257797788231 99754491948949886696682347)
        ·
          refine ⟨149631737923424830045023521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99754491948949886696682347 149631737923424830045023521)
          ·
            refine ⟨112223803442568622533767641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149631737923424830045023521 112223803442568622533767641)
            ·
              refine ⟨84167852581926466900325731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112223803442568622533767641 84167852581926466900325731)
              ·
                refine ⟨126251778872889700350488597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84167852581926466900325731 126251778872889700350488597)
                ·
                  refine ⟨5918052134666704703929153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126251778872889700350488597 5918052134666704703929153)
                  ·
                    refine ⟨4438539101000028527946865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5918052134666704703929153 4438539101000028527946865)
                    ·
                      refine ⟨3328904325750021395960149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438539101000028527946865 3328904325750021395960149)
                      ·
                        rfl

theorem cell23_6483018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_6483018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483018 prefixEnd_6483018 := by exact prefixLift 6483018
  have htrace : WordTrace (prefixWord ++ tailWord_6483018) baseStart_6483018 baseEnd_6483018 := by
    simpa [prefixWord, tailWord_6483018, baseEnd_6483018] using wordTrace_append hprefix tailTrace_6483018
  have hstable : (prefixWord ++ tailWord_6483018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483018).length < 2 ^ (prefixWord ++ tailWord_6483018).sum := by decide
  have hdescent : baseEnd_6483018 < baseStart_6483018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483030 : List Nat := [5, 2, 2, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6483030 : Nat := 118140960795 + 6483030 * 2 ^ 59
def prefixEnd_6483030 : Nat := 4983230072969 + 3 ^ 40 * 6483030 * 2
def baseEnd_6483030 : Nat := 3328910487517875349010095

theorem tailTrace_6483030 : CollatzResearch.WordTrace tailWord_6483030 prefixEnd_6483030 3328910487517875349010095 := by
  unfold tailWord_6483030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14778470606443562388709409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157637019802064665479567029 14778470606443562388709409)
  ·
    refine ⟨11083852954832671791532057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14778470606443562388709409 11083852954832671791532057)
    ·
      refine ⟨8312889716124503843649043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11083852954832671791532057 8312889716124503843649043)
      ·
        refine ⟨12469334574186755765473565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312889716124503843649043 12469334574186755765473565)
        ·
          refine ⟨4676000465320033412052587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12469334574186755765473565 4676000465320033412052587)
          ·
            refine ⟨7014000697980050118078881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676000465320033412052587 7014000697980050118078881)
            ·
              refine ⟨5260500523485037588559161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7014000697980050118078881 5260500523485037588559161)
              ·
                refine ⟨3945375392613778191419371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5260500523485037588559161 3945375392613778191419371)
                ·
                  refine ⟨5918063088920667287129057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945375392613778191419371 5918063088920667287129057)
                  ·
                    refine ⟨4438547316690500465346793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5918063088920667287129057 4438547316690500465346793)
                    ·
                      refine ⟨3328910487517875349010095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438547316690500465346793 3328910487517875349010095)
                      ·
                        rfl

theorem cell23_6483030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6483030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483030 prefixEnd_6483030 := by exact prefixLift 6483030
  have htrace : WordTrace (prefixWord ++ tailWord_6483030) baseStart_6483030 baseEnd_6483030 := by
    simpa [prefixWord, tailWord_6483030, baseEnd_6483030] using wordTrace_append hprefix tailTrace_6483030
  have hstable : (prefixWord ++ tailWord_6483030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483030).length < 2 ^ (prefixWord ++ tailWord_6483030).sum := by decide
  have hdescent : baseEnd_6483030 < baseStart_6483030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483044 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_6483044 : Nat := 118140960795 + 6483044 * 2 ^ 59
def prefixEnd_6483044 : Nat := 4983230072969 + 3 ^ 40 * 6483044 * 2
def baseEnd_6483044 : Nat := 3328917676247038294235029

theorem tailTrace_6483044 : CollatzResearch.WordTrace tailWord_6483044 prefixEnd_6483044 3328917676247038294235029 := by
  unfold tailWord_6483044
  simp only [CollatzResearch.WordTrace]
  refine ⟨118228020162523139305180093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157637360216697519073573457 118228020162523139305180093)
  ·
    refine ⟨44335507560946177239442535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118228020162523139305180093 44335507560946177239442535)
    ·
      refine ⟨66503261341419265859163803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44335507560946177239442535 66503261341419265859163803)
      ·
        refine ⟨99754892012128898788745705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66503261341419265859163803 99754892012128898788745705)
        ·
          refine ⟨74816169009096674091559279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99754892012128898788745705 74816169009096674091559279)
          ·
            refine ⟨112224253513645011137338919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74816169009096674091559279 112224253513645011137338919)
            ·
              refine ⟨168336380270467516706008379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112224253513645011137338919 168336380270467516706008379)
              ·
                refine ⟨252504570405701275059012569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168336380270467516706008379 252504570405701275059012569)
                ·
                  refine ⟨189378427804275956294259427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252504570405701275059012569 189378427804275956294259427)
                  ·
                    refine ⟨284067641706413934441389141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189378427804275956294259427 284067641706413934441389141)
                    ·
                      refine ⟨3328917676247038294235029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 284067641706413934441389141 3328917676247038294235029)
                      ·
                        rfl

theorem cell23_6483044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_6483044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483044 prefixEnd_6483044 := by exact prefixLift 6483044
  have htrace : WordTrace (prefixWord ++ tailWord_6483044) baseStart_6483044 baseEnd_6483044 := by
    simpa [prefixWord, tailWord_6483044, baseEnd_6483044] using wordTrace_append hprefix tailTrace_6483044
  have hstable : (prefixWord ++ tailWord_6483044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483044).length < 2 ^ (prefixWord ++ tailWord_6483044).sum := by decide
  have hdescent : baseEnd_6483044 < baseStart_6483044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483064 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_6483064 : Nat := 118140960795 + 6483064 * 2 ^ 59
def prefixEnd_6483064 : Nat := 4983230072969 + 3 ^ 40 * 6483064 * 2
def baseEnd_6483064 : Nat := 3328927945860128215984937

theorem tailTrace_6483064 : CollatzResearch.WordTrace tailWord_6483064 prefixEnd_6483064 3328927945860128215984937 := by
  unfold tailWord_6483064
  simp only [CollatzResearch.WordTrace]
  refine ⟨118228384892486911013044123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157637846523315881350725497 118228384892486911013044123)
  ·
    refine ⟨177342577338730366519566185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118228384892486911013044123 177342577338730366519566185)
    ·
      refine ⟨133006933004047774889674639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177342577338730366519566185 133006933004047774889674639)
      ·
        refine ⟨199510399506071662334511959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133006933004047774889674639 199510399506071662334511959)
        ·
          refine ⟨299265599259107493501767939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199510399506071662334511959 299265599259107493501767939)
          ·
            refine ⟨448898398888661240252651909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299265599259107493501767939 448898398888661240252651909)
            ·
              refine ⟨84168449791623982547372233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 448898398888661240252651909 84168449791623982547372233)
              ·
                refine ⟨63126337343717986910529175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84168449791623982547372233 63126337343717986910529175)
                ·
                  refine ⟨94689506015576980365793763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63126337343717986910529175 94689506015576980365793763)
                  ·
                    refine ⟨142034259023365470548690645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94689506015576980365793763 142034259023365470548690645)
                    ·
                      refine ⟨3328927945860128215984937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142034259023365470548690645 3328927945860128215984937)
                      ·
                        rfl

theorem cell23_6483064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_6483064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483064 prefixEnd_6483064 := by exact prefixLift 6483064
  have htrace : WordTrace (prefixWord ++ tailWord_6483064) baseStart_6483064 baseEnd_6483064 := by
    simpa [prefixWord, tailWord_6483064, baseEnd_6483064] using wordTrace_append hprefix tailTrace_6483064
  have hstable : (prefixWord ++ tailWord_6483064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483064).length < 2 ^ (prefixWord ++ tailWord_6483064).sum := by decide
  have hdescent : baseEnd_6483064 < baseStart_6483064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483084 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_6483084 : Nat := 118140960795 + 6483084 * 2 ^ 59
def prefixEnd_6483084 : Nat := 4983230072969 + 3 ^ 40 * 6483084 * 2
def baseEnd_6483084 : Nat := 1109646071824406045911615

theorem tailTrace_6483084 : CollatzResearch.WordTrace tailWord_6483084 prefixEnd_6483084 1109646071824406045911615 := by
  unfold tailWord_6483084
  simp only [CollatzResearch.WordTrace]
  refine ⟨118228749622450682720908153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157638332829934243627877537 118228749622450682720908153)
  ·
    refine ⟨88671562216838012040681115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118228749622450682720908153 88671562216838012040681115)
    ·
      refine ⟨133007343325257018061021673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88671562216838012040681115 133007343325257018061021673)
      ·
        refine ⟨99755507493942763545766255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133007343325257018061021673 99755507493942763545766255)
        ·
          refine ⟨149633261240914145318649383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99755507493942763545766255 149633261240914145318649383)
          ·
            refine ⟨224449891861371217977974075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149633261240914145318649383 224449891861371217977974075)
            ·
              refine ⟨336674837792056826966961113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224449891861371217977974075 336674837792056826966961113)
              ·
                refine ⟨252506128344042620225220835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336674837792056826966961113 252506128344042620225220835)
                ·
                  refine ⟨378759192516063930337831253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252506128344042620225220835 378759192516063930337831253)
                  ·
                    refine ⟨1109646071824406045911615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 378759192516063930337831253 1109646071824406045911615)
                    ·
                      rfl

theorem cell23_6483084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_6483084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483084 prefixEnd_6483084 := by exact prefixLift 6483084
  have htrace : WordTrace (prefixWord ++ tailWord_6483084) baseStart_6483084 baseEnd_6483084 := by
    simpa [prefixWord, tailWord_6483084, baseEnd_6483084] using wordTrace_append hprefix tailTrace_6483084
  have hstable : (prefixWord ++ tailWord_6483084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483084).length < 2 ^ (prefixWord ++ tailWord_6483084).sum := by decide
  have hdescent : baseEnd_6483084 < baseStart_6483084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483091 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 4]
def baseStart_6483091 : Nat := 118140960795 + 6483091 * 2 ^ 59
def prefixEnd_6483091 : Nat := 4983230072969 + 3 ^ 40 * 6483091 * 2
def baseEnd_6483091 : Nat := 3328941809837799610347313

theorem tailTrace_6483091 : CollatzResearch.WordTrace tailWord_6483091 prefixEnd_6483091 3328941809837799610347313 := by
  unfold tailWord_6483091
  simp only [CollatzResearch.WordTrace]
  refine ⟨236457754555876005637321127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157638503037250670424880751 236457754555876005637321127)
  ·
    refine ⟨354686631833814008455981691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236457754555876005637321127 354686631833814008455981691)
    ·
      refine ⟨532029947750721012683972537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354686631833814008455981691 532029947750721012683972537)
      ·
        refine ⟨399022460813040759512979403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532029947750721012683972537 399022460813040759512979403)
        ·
          refine ⟨598533691219561139269469105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399022460813040759512979403 598533691219561139269469105)
          ·
            refine ⟨448900268414670854452101829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598533691219561139269469105 448900268414670854452101829)
            ·
              refine ⟨84168800327750785209769093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 448900268414670854452101829 84168800327750785209769093)
              ·
                refine ⟨15781650061453272226831705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84168800327750785209769093 15781650061453272226831705)
                ·
                  refine ⟨11836237546089954170123779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15781650061453272226831705 11836237546089954170123779)
                  ·
                    refine ⟨17754356319134931255185669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11836237546089954170123779 17754356319134931255185669)
                    ·
                      refine ⟨3328941809837799610347313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17754356319134931255185669 3328941809837799610347313)
                      ·
                        rfl

theorem cell23_6483091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_6483091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483091 prefixEnd_6483091 := by exact prefixLift 6483091
  have htrace : WordTrace (prefixWord ++ tailWord_6483091) baseStart_6483091 baseEnd_6483091 := by
    simpa [prefixWord, tailWord_6483091, baseEnd_6483091] using wordTrace_append hprefix tailTrace_6483091
  have hstable : (prefixWord ++ tailWord_6483091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483091).length < 2 ^ (prefixWord ++ tailWord_6483091).sum := by decide
  have hdescent : baseEnd_6483091 < baseStart_6483091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483126 : List Nat := [5, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_6483126 : Nat := 118140960795 + 6483126 * 2 ^ 59
def prefixEnd_6483126 : Nat := 4983230072969 + 3 ^ 40 * 6483126 * 2
def baseEnd_6483126 : Nat := 369884420184522997045517

theorem tailTrace_6483126 : CollatzResearch.WordTrace tailWord_6483126 prefixEnd_6483126 369884420184522997045517 := by
  unfold tailWord_6483126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14778689444421825413427827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157639354073832804409896821 14778689444421825413427827)
  ·
    refine ⟨22168034166632738120141741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14778689444421825413427827 22168034166632738120141741)
    ·
      refine ⟨8313012812487276795053153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22168034166632738120141741 8313012812487276795053153)
      ·
        refine ⟨6234759609365457596289865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8313012812487276795053153 6234759609365457596289865)
        ·
          refine ⟨4676069707024093197217399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6234759609365457596289865 4676069707024093197217399)
          ·
            refine ⟨7014104560536139795826099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676069707024093197217399 7014104560536139795826099)
            ·
              refine ⟨10521156840804209693739149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014104560536139795826099 10521156840804209693739149)
              ·
                refine ⟨3945433815301578635152181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10521156840804209693739149 3945433815301578635152181)
                ·
                  refine ⟨369884420184522997045517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3945433815301578635152181 369884420184522997045517)
                  ·
                    rfl

theorem cell23_6483126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_6483126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483126 prefixEnd_6483126 := by exact prefixLift 6483126
  have htrace : WordTrace (prefixWord ++ tailWord_6483126) baseStart_6483126 baseEnd_6483126 := by
    simpa [prefixWord, tailWord_6483126, baseEnd_6483126] using wordTrace_append hprefix tailTrace_6483126
  have hstable : (prefixWord ++ tailWord_6483126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483126).length < 2 ^ (prefixWord ++ tailWord_6483126).sum := by decide
  have hdescent : baseEnd_6483126 < baseStart_6483126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483135 : List Nat := [1, 1, 2, 2, 2, 2, 5, 3, 1, 4]
def baseStart_6483135 : Nat := 118140960795 + 6483135 * 2 ^ 59
def prefixEnd_6483135 : Nat := 4983230072969 + 3 ^ 40 * 6483135 * 2
def baseEnd_6483135 : Nat := 1109654800995532479399037

theorem tailTrace_6483135 : CollatzResearch.WordTrace tailWord_6483135 prefixEnd_6483135 1109654800995532479399037 := by
  unfold tailWord_6483135
  simp only [CollatzResearch.WordTrace]
  refine ⟨236459359367716601151922859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157639572911811067434615239 236459359367716601151922859)
  ·
    refine ⟨354689039051574901727884289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236459359367716601151922859 354689039051574901727884289)
    ·
      refine ⟨266016779288681176295913217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354689039051574901727884289 266016779288681176295913217)
      ·
        refine ⟨199512584466510882221934913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266016779288681176295913217 199512584466510882221934913)
        ·
          refine ⟨149634438349883161666451185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199512584466510882221934913 149634438349883161666451185)
          ·
            refine ⟨112225828762412371249838389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149634438349883161666451185 112225828762412371249838389)
            ·
              refine ⟨10521171446476159804672349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112225828762412371249838389 10521171446476159804672349)
              ·
                refine ⟨3945439292428559926752131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10521171446476159804672349 3945439292428559926752131)
                ·
                  refine ⟨5918158938642839890128197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945439292428559926752131 5918158938642839890128197)
                  ·
                    refine ⟨1109654800995532479399037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5918158938642839890128197 1109654800995532479399037)
                    ·
                      rfl

theorem cell23_6483135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 4].length) (baseStart_6483135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483135 prefixEnd_6483135 := by exact prefixLift 6483135
  have htrace : WordTrace (prefixWord ++ tailWord_6483135) baseStart_6483135 baseEnd_6483135 := by
    simpa [prefixWord, tailWord_6483135, baseEnd_6483135] using wordTrace_append hprefix tailTrace_6483135
  have hstable : (prefixWord ++ tailWord_6483135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483135).length < 2 ^ (prefixWord ++ tailWord_6483135).sum := by decide
  have hdescent : baseEnd_6483135 < baseStart_6483135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483161 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 3, 5]
def baseStart_6483161 : Nat := 118140960795 + 6483161 * 2 ^ 59
def prefixEnd_6483161 : Nat := 4983230072969 + 3 ^ 40 * 6483161 * 2
def baseEnd_6483161 : Nat := 1109659251161204778823997

theorem tailTrace_6483161 : CollatzResearch.WordTrace tailWord_6483161 prefixEnd_6483161 1109659251161204778823997 := by
  unfold tailWord_6483161
  simp only [CollatzResearch.WordTrace]
  refine ⟨236460307665622407592369337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157640205110414938394912891 236460307665622407592369337)
  ·
    refine ⟨177345230749216805694277003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236460307665622407592369337 177345230749216805694277003)
    ·
      refine ⟨266017846123825208541415505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177345230749216805694277003 266017846123825208541415505)
      ·
        refine ⟨199513384592868906406061629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266017846123825208541415505 199513384592868906406061629)
        ·
          refine ⟨74817519222325839902273111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199513384592868906406061629 74817519222325839902273111)
          ·
            refine ⟨112226278833488759853409667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74817519222325839902273111 112226278833488759853409667)
            ·
              refine ⟨168339418250233139780114501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112226278833488759853409667 168339418250233139780114501)
              ·
                refine ⟨31563640921918713708771469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168339418250233139780114501 31563640921918713708771469)
                ·
                  refine ⟨11836365345719517640789301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31563640921918713708771469 11836365345719517640789301)
                  ·
                    refine ⟨1109659251161204778823997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11836365345719517640789301 1109659251161204778823997)
                    ·
                      rfl

theorem cell23_6483161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_6483161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483161 prefixEnd_6483161 := by exact prefixLift 6483161
  have htrace : WordTrace (prefixWord ++ tailWord_6483161) baseStart_6483161 baseEnd_6483161 := by
    simpa [prefixWord, tailWord_6483161, baseEnd_6483161] using wordTrace_append hprefix tailTrace_6483161
  have hstable : (prefixWord ++ tailWord_6483161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483161).length < 2 ^ (prefixWord ++ tailWord_6483161).sum := by decide
  have hdescent : baseEnd_6483161 < baseStart_6483161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483165 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 6]
def baseStart_6483165 : Nat := 118140960795 + 6483165 * 2 ^ 59
def prefixEnd_6483165 : Nat := 4983230072969 + 3 ^ 40 * 6483165 * 2
def baseEnd_6483165 : Nat := 369886645267359146757997

theorem tailTrace_6483165 : CollatzResearch.WordTrace tailWord_6483165 prefixEnd_6483165 369886645267359146757997 := by
  unfold tailWord_6483165
  simp only [CollatzResearch.WordTrace]
  refine ⟨236460453557607916275514949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157640302371738610850343299 236460453557607916275514949)
  ·
    refine ⟨44336335042051484301659053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236460453557607916275514949 44336335042051484301659053)
    ·
      refine ⟨16626125640769306613122145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44336335042051484301659053 16626125640769306613122145)
      ·
        refine ⟨12469594230576979959841609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16626125640769306613122145 12469594230576979959841609)
        ·
          refine ⟨9352195672932734969881207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12469594230576979959841609 9352195672932734969881207)
          ·
            refine ⟨14028293509399102454821811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9352195672932734969881207 14028293509399102454821811)
            ·
              refine ⟨21042440264098653682232717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14028293509399102454821811 21042440264098653682232717)
              ·
                refine ⟨7890915099036995130837269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21042440264098653682232717 7890915099036995130837269)
                ·
                  refine ⟨369886645267359146757997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7890915099036995130837269 369886645267359146757997)
                  ·
                    rfl

theorem cell23_6483165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_6483165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483165 prefixEnd_6483165 := by exact prefixLift 6483165
  have htrace : WordTrace (prefixWord ++ tailWord_6483165) baseStart_6483165 baseEnd_6483165 := by
    simpa [prefixWord, tailWord_6483165, baseEnd_6483165] using wordTrace_append hprefix tailTrace_6483165
  have hstable : (prefixWord ++ tailWord_6483165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483165).length < 2 ^ (prefixWord ++ tailWord_6483165).sum := by decide
  have hdescent : baseEnd_6483165 < baseStart_6483165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483178 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_6483178 : Nat := 118140960795 + 6483178 * 2 ^ 59
def prefixEnd_6483178 : Nat := 4983230072969 + 3 ^ 40 * 6483178 * 2
def baseEnd_6483178 : Nat := 1109662160884913589986471

theorem tailTrace_6483178 : CollatzResearch.WordTrace tailWord_6483178 prefixEnd_6483178 1109662160884913589986471 := by
  unfold tailWord_6483178
  simp only [CollatzResearch.WordTrace]
  refine ⟨59115231926640204873934547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157640618471040546330492125 59115231926640204873934547)
  ·
    refine ⟨88672847889960307310901821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59115231926640204873934547 88672847889960307310901821)
    ·
      refine ⟨33252317958735115241588183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88672847889960307310901821 33252317958735115241588183)
      ·
        refine ⟨49878476938102672862382275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33252317958735115241588183 49878476938102672862382275)
        ·
          refine ⟨74817715407154009293573413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49878476938102672862382275 74817715407154009293573413)
          ·
            refine ⟨14028321638841376742545015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74817715407154009293573413 14028321638841376742545015)
            ·
              refine ⟨21042482458262065113817523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14028321638841376742545015 21042482458262065113817523)
              ·
                refine ⟨31563723687393097670726285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21042482458262065113817523 31563723687393097670726285)
                ·
                  refine ⟨11836396382772411626522357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31563723687393097670726285 11836396382772411626522357)
                  ·
                    refine ⟨1109662160884913589986471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11836396382772411626522357 1109662160884913589986471)
                    ·
                      rfl

theorem cell23_6483178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_6483178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483178 prefixEnd_6483178 := by exact prefixLift 6483178
  have htrace : WordTrace (prefixWord ++ tailWord_6483178) baseStart_6483178 baseEnd_6483178 := by
    simpa [prefixWord, tailWord_6483178, baseEnd_6483178] using wordTrace_append hprefix tailTrace_6483178
  have hstable : (prefixWord ++ tailWord_6483178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483178).length < 2 ^ (prefixWord ++ tailWord_6483178).sum := by decide
  have hdescent : baseEnd_6483178 < baseStart_6483178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483191 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 1, 6]
def baseStart_6483191 : Nat := 118140960795 + 6483191 * 2 ^ 59
def prefixEnd_6483191 : Nat := 4983230072969 + 3 ^ 40 * 6483191 * 2
def baseEnd_6483191 : Nat := 1109664385967749739698951

theorem tailTrace_6483191 : CollatzResearch.WordTrace tailWord_6483191 prefixEnd_6483191 1109664385967749739698951 := by
  unfold tailWord_6483191
  simp only [CollatzResearch.WordTrace]
  refine ⟨236461401855513722715961427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157640934570342481810640951 236461401855513722715961427)
  ·
    refine ⟨354692102783270584073942141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236461401855513722715961427 354692102783270584073942141)
    ·
      refine ⟨133009538543726469027728303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354692102783270584073942141 133009538543726469027728303)
      ·
        refine ⟨199514307815589703541592455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133009538543726469027728303 199514307815589703541592455)
        ·
          refine ⟨299271461723384555312388683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199514307815589703541592455 299271461723384555312388683)
          ·
            refine ⟨448907192585076832968583025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299271461723384555312388683 448907192585076832968583025)
            ·
              refine ⟨336680394438807624726437269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448907192585076832968583025 336680394438807624726437269)
              ·
                refine ⟨15781893489319107409051747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 336680394438807624726437269 15781893489319107409051747)
                ·
                  refine ⟨23672840233978661113577621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15781893489319107409051747 23672840233978661113577621)
                  ·
                    refine ⟨1109664385967749739698951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23672840233978661113577621 1109664385967749739698951)
                    ·
                      rfl

theorem cell23_6483191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_6483191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483191 prefixEnd_6483191 := by exact prefixLift 6483191
  have htrace : WordTrace (prefixWord ++ tailWord_6483191) baseStart_6483191 baseEnd_6483191 := by
    simpa [prefixWord, tailWord_6483191, baseEnd_6483191] using wordTrace_append hprefix tailTrace_6483191
  have hstable : (prefixWord ++ tailWord_6483191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483191).length < 2 ^ (prefixWord ++ tailWord_6483191).sum := by decide
  have hdescent : baseEnd_6483191 < baseStart_6483191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483228 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6483228 : Nat := 118140960795 + 6483228 * 2 ^ 59
def prefixEnd_6483228 : Nat := 4983230072969 + 3 ^ 40 * 6483228 * 2
def baseEnd_6483228 : Nat := 3329012156687465574334183

theorem tailTrace_6483228 : CollatzResearch.WordTrace tailWord_6483228 prefixEnd_6483228 3329012156687465574334183 := by
  unfold tailWord_6483228
  simp only [CollatzResearch.WordTrace]
  refine ⟨118231375678189839017529169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157641834237586452023372225 118231375678189839017529169)
  ·
    refine ⟨88673531758642379263146877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118231375678189839017529169 88673531758642379263146877)
    ·
      refine ⟨33252574409490892223680079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88673531758642379263146877 33252574409490892223680079)
      ·
        refine ⟨49878861614236338335520119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33252574409490892223680079 49878861614236338335520119)
        ·
          refine ⟨74818292421354507503280179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49878861614236338335520119 74818292421354507503280179)
          ·
            refine ⟨112227438632031761254920269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74818292421354507503280179 112227438632031761254920269)
            ·
              refine ⟨42085289487011910470595101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112227438632031761254920269 42085289487011910470595101)
              ·
                refine ⟨15781983557629466426473163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42085289487011910470595101 15781983557629466426473163)
                ·
                  refine ⟨23672975336444199639709745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15781983557629466426473163 23672975336444199639709745)
                  ·
                    refine ⟨17754731502333149729782309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23672975336444199639709745 17754731502333149729782309)
                    ·
                      refine ⟨3329012156687465574334183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17754731502333149729782309 3329012156687465574334183)
                      ·
                        rfl

theorem cell23_6483228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6483228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483228 prefixEnd_6483228 := by exact prefixLift 6483228
  have htrace : WordTrace (prefixWord ++ tailWord_6483228) baseStart_6483228 baseEnd_6483228 := by
    simpa [prefixWord, tailWord_6483228, baseEnd_6483228] using wordTrace_append hprefix tailTrace_6483228
  have hstable : (prefixWord ++ tailWord_6483228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483228).length < 2 ^ (prefixWord ++ tailWord_6483228).sum := by decide
  have hdescent : baseEnd_6483228 < baseStart_6483228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483248 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3]
def baseStart_6483248 : Nat := 118140960795 + 6483248 * 2 ^ 59
def prefixEnd_6483248 : Nat := 4983230072969 + 3 ^ 40 * 6483248 * 2
def baseEnd_6483248 : Nat := 3329022426300555496084091

theorem tailTrace_6483248 : CollatzResearch.WordTrace tailWord_6483248 prefixEnd_6483248 3329022426300555496084091 := by
  unfold tailWord_6483248
  simp only [CollatzResearch.WordTrace]
  refine ⟨118231740408153610725393199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157642320544204814300524265 118231740408153610725393199)
  ·
    refine ⟨177347610612230416088089799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118231740408153610725393199 177347610612230416088089799)
    ·
      refine ⟨266021415918345624132134699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177347610612230416088089799 266021415918345624132134699)
      ·
        refine ⟨399032123877518436198202049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266021415918345624132134699 399032123877518436198202049)
        ·
          refine ⟨299274092908138827148651537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399032123877518436198202049 299274092908138827148651537)
          ·
            refine ⟨224455569681104120361488653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299274092908138827148651537 224455569681104120361488653)
            ·
              refine ⟨84170838630414045135558245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224455569681104120361488653 84170838630414045135558245)
              ·
                refine ⟨15782032243202633462917171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84170838630414045135558245 15782032243202633462917171)
                ·
                  refine ⟨23673048364803950194375757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15782032243202633462917171 23673048364803950194375757)
                  ·
                    refine ⟨8877393136801481322890909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23673048364803950194375757 8877393136801481322890909)
                    ·
                      refine ⟨3329022426300555496084091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8877393136801481322890909 3329022426300555496084091)
                      ·
                        rfl

theorem cell23_6483248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_6483248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483248 prefixEnd_6483248 := by exact prefixLift 6483248
  have htrace : WordTrace (prefixWord ++ tailWord_6483248) baseStart_6483248 baseEnd_6483248 := by
    simpa [prefixWord, tailWord_6483248, baseEnd_6483248] using wordTrace_append hprefix tailTrace_6483248
  have hstable : (prefixWord ++ tailWord_6483248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483248).length < 2 ^ (prefixWord ++ tailWord_6483248).sum := by decide
  have hdescent : baseEnd_6483248 < baseStart_6483248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483249 : List Nat := [1, 2, 2, 3, 3, 1, 1, 5, 1, 2, 2]
def baseStart_6483249 : Nat := 118140960795 + 6483249 * 2 ^ 59
def prefixEnd_6483249 : Nat := 4983230072969 + 3 ^ 40 * 6483249 * 2
def baseEnd_6483249 : Nat := 3329022939781209992171587

theorem tailTrace_6483249 : CollatzResearch.WordTrace tailWord_6483249 prefixEnd_6483249 3329022939781209992171587 := by
  unfold tailWord_6483249
  simp only [CollatzResearch.WordTrace]
  refine ⟨236463517289303598621572801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157642344859535732414381867 236463517289303598621572801)
  ·
    refine ⟨177347637966977698966179601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236463517289303598621572801 177347637966977698966179601)
    ·
      refine ⟨133010728475233274224634701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177347637966977698966179601 133010728475233274224634701)
      ·
        refine ⟨49879023178212477834238013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133010728475233274224634701 49879023178212477834238013)
        ·
          refine ⟨18704633691829679187839255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49879023178212477834238013 18704633691829679187839255)
          ·
            refine ⟨28056950537744518781758883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18704633691829679187839255 28056950537744518781758883)
            ·
              refine ⟨42085425806616778172638325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28056950537744518781758883 42085425806616778172638325)
              ·
                refine ⟨3945508669370322953684843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42085425806616778172638325 3945508669370322953684843)
                ·
                  refine ⟨5918263004055484430527265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945508669370322953684843 5918263004055484430527265)
                  ·
                    refine ⟨4438697253041613322895449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5918263004055484430527265 4438697253041613322895449)
                    ·
                      refine ⟨3329022939781209992171587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438697253041613322895449 3329022939781209992171587)
                      ·
                        rfl

theorem cell23_6483249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_6483249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483249 prefixEnd_6483249 := by exact prefixLift 6483249
  have htrace : WordTrace (prefixWord ++ tailWord_6483249) baseStart_6483249 baseEnd_6483249 := by
    simpa [prefixWord, tailWord_6483249, baseEnd_6483249] using wordTrace_append hprefix tailTrace_6483249
  have hstable : (prefixWord ++ tailWord_6483249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483249).length < 2 ^ (prefixWord ++ tailWord_6483249).sum := by decide
  have hdescent : baseEnd_6483249 < baseStart_6483249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483252 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_6483252 : Nat := 118140960795 + 6483252 * 2 ^ 59
def prefixEnd_6483252 : Nat := 4983230072969 + 3 ^ 40 * 6483252 * 2
def baseEnd_6483252 : Nat := 3329024480223173480434073

theorem tailTrace_6483252 : CollatzResearch.WordTrace tailWord_6483252 prefixEnd_6483252 3329024480223173480434073 := by
  unfold tailWord_6483252
  simp only [CollatzResearch.WordTrace]
  refine ⟨118231813354146365066966005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157642417805528486755954673 118231813354146365066966005)
  ·
    refine ⟨11084232501951221725028063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118231813354146365066966005 11084232501951221725028063)
    ·
      refine ⟨16626348752926832587542095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11084232501951221725028063 16626348752926832587542095)
      ·
        refine ⟨24939523129390248881313143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16626348752926832587542095 24939523129390248881313143)
        ·
          refine ⟨37409284694085373321969715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24939523129390248881313143 37409284694085373321969715)
          ·
            refine ⟨56113927041128059982954573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37409284694085373321969715 56113927041128059982954573)
            ·
              refine ⟨21042722640423022493607965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56113927041128059982954573 21042722640423022493607965)
              ·
                refine ⟨7891020990158633435102987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21042722640423022493607965 7891020990158633435102987)
                ·
                  refine ⟨11836531485237950152654481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891020990158633435102987 11836531485237950152654481)
                  ·
                    refine ⟨8877398613928462614490861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11836531485237950152654481 8877398613928462614490861)
                    ·
                      refine ⟨3329024480223173480434073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8877398613928462614490861 3329024480223173480434073)
                      ·
                        rfl

theorem cell23_6483252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_6483252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483252 prefixEnd_6483252 := by exact prefixLift 6483252
  have htrace : WordTrace (prefixWord ++ tailWord_6483252) baseStart_6483252 baseEnd_6483252 := by
    simpa [prefixWord, tailWord_6483252, baseEnd_6483252] using wordTrace_append hprefix tailTrace_6483252
  have hstable : (prefixWord ++ tailWord_6483252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483252).length < 2 ^ (prefixWord ++ tailWord_6483252).sum := by decide
  have hdescent : baseEnd_6483252 < baseStart_6483252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483308 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_6483308 : Nat := 118140960795 + 6483308 * 2 ^ 59
def prefixEnd_6483308 : Nat := 4983230072969 + 3 ^ 40 * 6483308 * 2
def baseEnd_6483308 : Nat := 3329053235139825261333815

theorem tailTrace_6483308 : CollatzResearch.WordTrace tailWord_6483308 prefixEnd_6483308 3329053235139825261333815 := by
  unfold tailWord_6483308
  simp only [CollatzResearch.WordTrace]
  refine ⟨118232834598044925848985289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157643779464059901131980385 118232834598044925848985289)
  ·
    refine ⟨88674625948533694386738967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118232834598044925848985289 88674625948533694386738967)
    ·
      refine ⟨133011938922800541580108451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88674625948533694386738967 133011938922800541580108451)
      ·
        refine ⟨199517908384200812370162677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133011938922800541580108451 199517908384200812370162677)
        ·
          refine ⟨18704803911018826159702751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199517908384200812370162677 18704803911018826159702751)
          ·
            refine ⟨28057205866528239239554127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18704803911018826159702751 28057205866528239239554127)
            ·
              refine ⟨42085808799792358859331191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28057205866528239239554127 42085808799792358859331191)
              ·
                refine ⟨63128713199688538288996787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42085808799792358859331191 63128713199688538288996787)
                ·
                  refine ⟨94693069799532807433495181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63128713199688538288996787 94693069799532807433495181)
                  ·
                    refine ⟨35509901174824802787560693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94693069799532807433495181 35509901174824802787560693)
                    ·
                      refine ⟨3329053235139825261333815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35509901174824802787560693 3329053235139825261333815)
                      ·
                        rfl

theorem cell23_6483308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_6483308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483308 prefixEnd_6483308 := by exact prefixLift 6483308
  have htrace : WordTrace (prefixWord ++ tailWord_6483308) baseStart_6483308 baseEnd_6483308 := by
    simpa [prefixWord, tailWord_6483308, baseEnd_6483308] using wordTrace_append hprefix tailTrace_6483308
  have hstable : (prefixWord ++ tailWord_6483308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483308).length < 2 ^ (prefixWord ++ tailWord_6483308).sum := by decide
  have hdescent : baseEnd_6483308 < baseStart_6483308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483395 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 1, 6, 2]
def baseStart_6483395 : Nat := 118140960795 + 6483395 * 2 ^ 59
def prefixEnd_6483395 : Nat := 4983230072969 + 3 ^ 40 * 6483395 * 2
def baseEnd_6483395 : Nat := 3329097907956766420945915

theorem tailTrace_6483395 : CollatzResearch.WordTrace tailWord_6483395 prefixEnd_6483395 3329097907956766420945915 := by
  unfold tailWord_6483395
  simp only [CollatzResearch.WordTrace]
  refine ⟨236468842346774665556387639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157645894897849777037591759 236468842346774665556387639)
  ·
    refine ⟨354703263520161998334581459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236468842346774665556387639 354703263520161998334581459)
    ·
      refine ⟨532054895280242997501872189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354703263520161998334581459 532054895280242997501872189)
      ·
        refine ⟨199520585730091124063202071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532054895280242997501872189 199520585730091124063202071)
        ·
          refine ⟨299280878595136686094803107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199520585730091124063202071 299280878595136686094803107)
          ·
            refine ⟨448921317892705029142204661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299280878595136686094803107 448921317892705029142204661)
            ·
              refine ⟨42086373552441096482081687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 448921317892705029142204661 42086373552441096482081687)
              ·
                refine ⟨63129560328661644723122531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42086373552441096482081687 63129560328661644723122531)
                ·
                  refine ⟨94694340492992467084683797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63129560328661644723122531 94694340492992467084683797)
                  ·
                    refine ⟨4438797210609021894594553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94694340492992467084683797 4438797210609021894594553)
                    ·
                      refine ⟨3329097907956766420945915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438797210609021894594553 3329097907956766420945915)
                      ·
                        rfl

theorem cell23_6483395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_6483395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483395 prefixEnd_6483395 := by exact prefixLift 6483395
  have htrace : WordTrace (prefixWord ++ tailWord_6483395) baseStart_6483395 baseEnd_6483395 := by
    simpa [prefixWord, tailWord_6483395, baseEnd_6483395] using wordTrace_append hprefix tailTrace_6483395
  have hstable : (prefixWord ++ tailWord_6483395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483395).length < 2 ^ (prefixWord ++ tailWord_6483395).sum := by decide
  have hdescent : baseEnd_6483395 < baseStart_6483395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483408 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_6483408 : Nat := 118140960795 + 6483408 * 2 ^ 59
def prefixEnd_6483408 : Nat := 4983230072969 + 3 ^ 40 * 6483408 * 2
def baseEnd_6483408 : Nat := 3329104583205274870083355

theorem tailTrace_6483408 : CollatzResearch.WordTrace tailWord_6483408 prefixEnd_6483408 3329104583205274870083355 := by
  unfold tailWord_6483408
  simp only [CollatzResearch.WordTrace]
  refine ⟨118234658247863784388305439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157646210997151712517740585 118234658247863784388305439)
  ·
    refine ⟨177351987371795676582458159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118234658247863784388305439 177351987371795676582458159)
    ·
      refine ⟨266027981057693514873687239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177351987371795676582458159 266027981057693514873687239)
      ·
        refine ⟨399041971586540272310530859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266027981057693514873687239 399041971586540272310530859)
        ·
          refine ⟨598562957379810408465796289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399041971586540272310530859 598562957379810408465796289)
          ·
            refine ⟨448922218034857806349347217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598562957379810408465796289 448922218034857806349347217)
            ·
              refine ⟨336691663526143354762010413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448922218034857806349347217 336691663526143354762010413)
              ·
                refine ⟨126259373822303758035753905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336691663526143354762010413 126259373822303758035753905)
                ·
                  refine ⟨94694530366727818526815429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126259373822303758035753905 94694530366727818526815429)
                  ·
                    refine ⟨17755224443761465973777893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94694530366727818526815429 17755224443761465973777893)
                    ·
                      refine ⟨3329104583205274870083355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17755224443761465973777893 3329104583205274870083355)
                      ·
                        rfl

theorem cell23_6483408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_6483408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483408 prefixEnd_6483408 := by exact prefixLift 6483408
  have htrace : WordTrace (prefixWord ++ tailWord_6483408) baseStart_6483408 baseEnd_6483408 := by
    simpa [prefixWord, tailWord_6483408, baseEnd_6483408] using wordTrace_append hprefix tailTrace_6483408
  have hstable : (prefixWord ++ tailWord_6483408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483408).length < 2 ^ (prefixWord ++ tailWord_6483408).sum := by decide
  have hdescent : baseEnd_6483408 < baseStart_6483408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483412 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_6483412 : Nat := 118140960795 + 6483412 * 2 ^ 59
def prefixEnd_6483412 : Nat := 4983230072969 + 3 ^ 40 * 6483412 * 2
def baseEnd_6483412 : Nat := 3329106637127892854433337

theorem tailTrace_6483412 : CollatzResearch.WordTrace tailWord_6483412 prefixEnd_6483412 3329106637127892854433337 := by
  unfold tailWord_6483412
  simp only [CollatzResearch.WordTrace]
  refine ⟨118234731193856538729878245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157646308258475384973170993 118234731193856538729878245)
  ·
    refine ⟨22169012098848101011852171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118234731193856538729878245 22169012098848101011852171)
    ·
      refine ⟨33253518148272151517778257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22169012098848101011852171 33253518148272151517778257)
      ·
        refine ⟨24940138611204113638333693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33253518148272151517778257 24940138611204113638333693)
        ·
          refine ⟨9352551979201542614375135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24940138611204113638333693 9352551979201542614375135)
          ·
            refine ⟨14028827968802313921562703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9352551979201542614375135 14028827968802313921562703)
            ·
              refine ⟨21043241953203470882344055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14028827968802313921562703 21043241953203470882344055)
              ·
                refine ⟨31564862929805206323516083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21043241953203470882344055 31564862929805206323516083)
                ·
                  refine ⟨47347294394707809485274125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31564862929805206323516083 47347294394707809485274125)
                  ·
                    refine ⟨17755235398015428556977797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47347294394707809485274125 17755235398015428556977797)
                    ·
                      refine ⟨3329106637127892854433337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17755235398015428556977797 3329106637127892854433337)
                      ·
                        rfl

theorem cell23_6483412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_6483412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483412 prefixEnd_6483412 := by exact prefixLift 6483412
  have htrace : WordTrace (prefixWord ++ tailWord_6483412) baseStart_6483412 baseEnd_6483412 := by
    simpa [prefixWord, tailWord_6483412, baseEnd_6483412] using wordTrace_append hprefix tailTrace_6483412
  have hstable : (prefixWord ++ tailWord_6483412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483412).length < 2 ^ (prefixWord ++ tailWord_6483412).sum := by decide
  have hdescent : baseEnd_6483412 < baseStart_6483412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483489 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_6483489 : Nat := 118140960795 + 6483489 * 2 ^ 59
def prefixEnd_6483489 : Nat := 4983230072969 + 3 ^ 40 * 6483489 * 2
def baseEnd_6483489 : Nat := 3329146175138289053170483

theorem tailTrace_6483489 : CollatzResearch.WordTrace tailWord_6483489 prefixEnd_6483489 3329146175138289053170483 := by
  unfold tailWord_6483489
  simp only [CollatzResearch.WordTrace]
  refine ⟨236472270808434119610309521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157648180538956079740206347 236472270808434119610309521)
  ·
    refine ⟨177354203106325589707732141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236472270808434119610309521 177354203106325589707732141)
    ·
      refine ⟨66507826164872096140399553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177354203106325589707732141 66507826164872096140399553)
      ·
        refine ⟨49880869623654072105299665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66507826164872096140399553 49880869623654072105299665)
        ·
          refine ⟨37410652217740554078974749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49880869623654072105299665 37410652217740554078974749)
          ·
            refine ⟨14028994581652707779615531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37410652217740554078974749 14028994581652707779615531)
            ·
              refine ⟨21043491872479061669423297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14028994581652707779615531 21043491872479061669423297)
              ·
                refine ⟨15782618904359296252067473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21043491872479061669423297 15782618904359296252067473)
                ·
                  refine ⟨11836964178269472189050605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15782618904359296252067473 11836964178269472189050605)
                  ·
                    refine ⟨4438861566851052070893977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11836964178269472189050605 4438861566851052070893977)
                    ·
                      refine ⟨3329146175138289053170483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438861566851052070893977 3329146175138289053170483)
                      ·
                        rfl

theorem cell23_6483489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_6483489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483489 prefixEnd_6483489 := by exact prefixLift 6483489
  have htrace : WordTrace (prefixWord ++ tailWord_6483489) baseStart_6483489 baseEnd_6483489 := by
    simpa [prefixWord, tailWord_6483489, baseEnd_6483489] using wordTrace_append hprefix tailTrace_6483489
  have hstable : (prefixWord ++ tailWord_6483489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483489).length < 2 ^ (prefixWord ++ tailWord_6483489).sum := by decide
  have hdescent : baseEnd_6483489 < baseStart_6483489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483505 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_6483505 : Nat := 118140960795 + 6483505 * 2 ^ 59
def prefixEnd_6483505 : Nat := 4983230072969 + 3 ^ 40 * 6483505 * 2
def baseEnd_6483505 : Nat := 3329154390828760990570409

theorem tailTrace_6483505 : CollatzResearch.WordTrace tailWord_6483505 prefixEnd_6483505 3329154390828760990570409 := by
  unfold tailWord_6483505
  simp only [CollatzResearch.WordTrace]
  refine ⟨236472854376376154342891969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157648569584250769561927979 236472854376376154342891969)
  ·
    refine ⟨177354640782282115757168977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236472854376376154342891969 177354640782282115757168977)
    ·
      refine ⟨133015980586711586817876733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177354640782282115757168977 133015980586711586817876733)
      ·
        refine ⟨49880992720016845056703775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133015980586711586817876733 49880992720016845056703775)
        ·
          refine ⟨74821489080025267585055663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49880992720016845056703775 74821489080025267585055663)
          ·
            refine ⟨112232233620037901377583495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74821489080025267585055663 112232233620037901377583495)
            ·
              refine ⟨168348350430056852066375243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112232233620037901377583495 168348350430056852066375243)
              ·
                refine ⟨252522525645085278099562865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168348350430056852066375243 252522525645085278099562865)
                ·
                  refine ⟨189391894233813958574672149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252522525645085278099562865 189391894233813958574672149)
                  ·
                    refine ⟨8877745042210029308187757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 189391894233813958574672149 8877745042210029308187757)
                    ·
                      refine ⟨3329154390828760990570409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8877745042210029308187757 3329154390828760990570409)
                      ·
                        rfl

theorem cell23_6483505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_6483505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483505 prefixEnd_6483505 := by exact prefixLift 6483505
  have htrace : WordTrace (prefixWord ++ tailWord_6483505) baseStart_6483505 baseEnd_6483505 := by
    simpa [prefixWord, tailWord_6483505, baseEnd_6483505] using wordTrace_append hprefix tailTrace_6483505
  have hstable : (prefixWord ++ tailWord_6483505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483505).length < 2 ^ (prefixWord ++ tailWord_6483505).sum := by decide
  have hdescent : baseEnd_6483505 < baseStart_6483505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483516 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_6483516 : Nat := 118140960795 + 6483516 * 2 ^ 59
def prefixEnd_6483516 : Nat := 4983230072969 + 3 ^ 40 * 6483516 * 2
def baseEnd_6483516 : Nat := 1109720013038653482510953

theorem tailTrace_6483516 : CollatzResearch.WordTrace tailWord_6483516 prefixEnd_6483516 1109720013038653482510953 := by
  unfold tailWord_6483516
  simp only [CollatzResearch.WordTrace]
  refine ⟨118236627789668151610771201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157648837052890868814361601 118236627789668151610771201)
  ·
    refine ⟨88677470842251113708078401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118236627789668151610771201 88677470842251113708078401)
    ·
      refine ⟨66508103131688335281058801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88677470842251113708078401 66508103131688335281058801)
      ·
        refine ⟨49881077348766251460794101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66508103131688335281058801 49881077348766251460794101)
        ·
          refine ⟨4676351001446836074449447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49881077348766251460794101 4676351001446836074449447)
          ·
            refine ⟨7014526502170254111674171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676351001446836074449447 7014526502170254111674171)
            ·
              refine ⟨10521789753255381167511257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014526502170254111674171 10521789753255381167511257)
              ·
                refine ⟨7891342314941535875633443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10521789753255381167511257 7891342314941535875633443)
                ·
                  refine ⟨11837013472412303813450165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891342314941535875633443 11837013472412303813450165)
                  ·
                    refine ⟨1109720013038653482510953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11837013472412303813450165 1109720013038653482510953)
                    ·
                      rfl

theorem cell23_6483516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_6483516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483516 prefixEnd_6483516 := by exact prefixLift 6483516
  have htrace : WordTrace (prefixWord ++ tailWord_6483516) baseStart_6483516 baseEnd_6483516 := by
    simpa [prefixWord, tailWord_6483516, baseEnd_6483516] using wordTrace_append hprefix tailTrace_6483516
  have hstable : (prefixWord ++ tailWord_6483516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483516).length < 2 ^ (prefixWord ++ tailWord_6483516).sum := by decide
  have hdescent : baseEnd_6483516 < baseStart_6483516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483519 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 4]
def baseStart_6483519 : Nat := 118140960795 + 6483519 * 2 ^ 59
def prefixEnd_6483519 : Nat := 4983230072969 + 3 ^ 40 * 6483519 * 2
def baseEnd_6483519 : Nat := 3329161579557923935795345

theorem tailTrace_6483519 : CollatzResearch.WordTrace tailWord_6483519 prefixEnd_6483519 3329161579557923935795345 := by
  unfold tailWord_6483519
  simp only [CollatzResearch.WordTrace]
  refine ⟨236473364998325434733901611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157648909998883623155934407 236473364998325434733901611)
  ·
    refine ⟨354710047497488152100852417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236473364998325434733901611 354710047497488152100852417)
    ·
      refine ⟨266032535623116114075639313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354710047497488152100852417 266032535623116114075639313)
      ·
        refine ⟨199524401717337085556729485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266032535623116114075639313 199524401717337085556729485)
        ·
          refine ⟨74821650644001407083773557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199524401717337085556729485 74821650644001407083773557)
          ·
            refine ⟨7014529747875131914103771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74821650644001407083773557 7014529747875131914103771)
            ·
              refine ⟨10521794621812697871155657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014529747875131914103771 10521794621812697871155657)
              ·
                refine ⟨7891345966359523403366743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10521794621812697871155657 7891345966359523403366743)
                ·
                  refine ⟨11837018949539285105050115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891345966359523403366743 11837018949539285105050115)
                  ·
                    refine ⟨17755528424308927657575173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11837018949539285105050115 17755528424308927657575173)
                    ·
                      refine ⟨3329161579557923935795345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17755528424308927657575173 3329161579557923935795345)
                      ·
                        rfl

theorem cell23_6483519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_6483519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483519 prefixEnd_6483519 := by exact prefixLift 6483519
  have htrace : WordTrace (prefixWord ++ tailWord_6483519) baseStart_6483519 baseEnd_6483519 := by
    simpa [prefixWord, tailWord_6483519, baseEnd_6483519] using wordTrace_append hprefix tailTrace_6483519
  have hstable : (prefixWord ++ tailWord_6483519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483519).length < 2 ^ (prefixWord ++ tailWord_6483519).sum := by decide
  have hdescent : baseEnd_6483519 < baseStart_6483519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483532 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6483532 : Nat := 118140960795 + 6483532 * 2 ^ 59
def prefixEnd_6483532 : Nat := 4983230072969 + 3 ^ 40 * 6483532 * 2
def baseEnd_6483532 : Nat := 3329168254806432384932785

theorem tailTrace_6483532 : CollatzResearch.WordTrace tailWord_6483532 prefixEnd_6483532 3329168254806432384932785 := by
  unfold tailWord_6483532
  simp only [CollatzResearch.WordTrace]
  refine ⟨118236919573639168977062425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157649226098185558636083233 118236919573639168977062425)
  ·
    refine ⟨88677689680229376732796819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118236919573639168977062425 88677689680229376732796819)
    ·
      refine ⟨133016534520344065099195229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88677689680229376732796819 133016534520344065099195229)
      ·
        refine ⟨49881200445129024412198211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133016534520344065099195229 49881200445129024412198211)
        ·
          refine ⟨74821800667693536618297317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49881200445129024412198211 74821800667693536618297317)
          ·
            refine ⟨14029087625192538115930747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74821800667693536618297317 14029087625192538115930747)
            ·
              refine ⟨21043631437788807173896121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14029087625192538115930747 21043631437788807173896121)
              ·
                refine ⟨15782723578341605380422091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21043631437788807173896121 15782723578341605380422091)
                ·
                  refine ⟨23674085367512408070633137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15782723578341605380422091 23674085367512408070633137)
                  ·
                    refine ⟨17755564025634306052974853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23674085367512408070633137 17755564025634306052974853)
                    ·
                      refine ⟨3329168254806432384932785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17755564025634306052974853 3329168254806432384932785)
                      ·
                        rfl

theorem cell23_6483532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6483532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483532 prefixEnd_6483532 := by exact prefixLift 6483532
  have htrace : WordTrace (prefixWord ++ tailWord_6483532) baseStart_6483532 baseEnd_6483532 := by
    simpa [prefixWord, tailWord_6483532, baseEnd_6483532] using wordTrace_append hprefix tailTrace_6483532
  have hstable : (prefixWord ++ tailWord_6483532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483532).length < 2 ^ (prefixWord ++ tailWord_6483532).sum := by decide
  have hdescent : baseEnd_6483532 < baseStart_6483532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483536 : List Nat := [2, 1, 1, 1, 1, 3, 4, 5, 1, 2, 2]
def baseStart_6483536 : Nat := 118140960795 + 6483536 * 2 ^ 59
def prefixEnd_6483536 : Nat := 4983230072969 + 3 ^ 40 * 6483536 * 2
def baseEnd_6483536 : Nat := 3329170308729050369282767

theorem tailTrace_6483536 : CollatzResearch.WordTrace tailWord_6483536 prefixEnd_6483536 3329170308729050369282767 := by
  unfold tailWord_6483536
  simp only [CollatzResearch.WordTrace]
  refine ⟨118236992519631923318635231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157649323359509231091513641 118236992519631923318635231)
  ·
    refine ⟨177355488779447884977952847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118236992519631923318635231 177355488779447884977952847)
    ·
      refine ⟨266033233169171827466929271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177355488779447884977952847 266033233169171827466929271)
      ·
        refine ⟨399049849753757741200393907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266033233169171827466929271 399049849753757741200393907)
        ·
          refine ⟨598574774630636611800590861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399049849753757741200393907 598574774630636611800590861)
          ·
            refine ⟨224465540486488729425221573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 598574774630636611800590861 224465540486488729425221573)
            ·
              refine ⟨42087288841216636767229045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224465540486488729425221573 42087288841216636767229045)
              ·
                refine ⟨3945683328864059696927723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42087288841216636767229045 3945683328864059696927723)
                ·
                  refine ⟨5918524993296089545391585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945683328864059696927723 5918524993296089545391585)
                  ·
                    refine ⟨4438893744972067159043689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5918524993296089545391585 4438893744972067159043689)
                    ·
                      refine ⟨3329170308729050369282767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438893744972067159043689 3329170308729050369282767)
                      ·
                        rfl

theorem cell23_6483536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 2, 2].length) (baseStart_6483536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483536 prefixEnd_6483536 := by exact prefixLift 6483536
  have htrace : WordTrace (prefixWord ++ tailWord_6483536) baseStart_6483536 baseEnd_6483536 := by
    simpa [prefixWord, tailWord_6483536, baseEnd_6483536] using wordTrace_append hprefix tailTrace_6483536
  have hstable : (prefixWord ++ tailWord_6483536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483536).length < 2 ^ (prefixWord ++ tailWord_6483536).sum := by decide
  have hdescent : baseEnd_6483536 < baseStart_6483536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483555 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 2, 7]
def baseStart_6483555 : Nat := 118140960795 + 6483555 * 2 ^ 59
def prefixEnd_6483555 : Nat := 4983230072969 + 3 ^ 40 * 6483555 * 2
def baseEnd_6483555 : Nat := 1109726688287161931648393

theorem tailTrace_6483555 : CollatzResearch.WordTrace tailWord_6483555 prefixEnd_6483555 1109726688287161931648393 := by
  unfold tailWord_6483555
  simp only [CollatzResearch.WordTrace]
  refine ⟨236474678026195012882212119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157649785350796675254808079 236474678026195012882212119)
  ·
    refine ⟨354712017039292519323318179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236474678026195012882212119 354712017039292519323318179)
    ·
      refine ⟨532068025558938778984977269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354712017039292519323318179 532068025558938778984977269)
      ·
        refine ⟨49881377396150510529841619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 532068025558938778984977269 49881377396150510529841619)
        ·
          refine ⟨74822066094225765794762429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49881377396150510529841619 74822066094225765794762429)
          ·
            refine ⟨28058274785334662173035911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74822066094225765794762429 28058274785334662173035911)
            ·
              refine ⟨42087412178001993259553867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28058274785334662173035911 42087412178001993259553867)
              ·
                refine ⟨63131118267002989889330801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42087412178001993259553867 63131118267002989889330801)
                ·
                  refine ⟨47348338700252242416998101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63131118267002989889330801 47348338700252242416998101)
                  ·
                    refine ⟨1109726688287161931648393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47348338700252242416998101 1109726688287161931648393)
                    ·
                      rfl

theorem cell23_6483555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 7].length) (baseStart_6483555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483555 prefixEnd_6483555 := by exact prefixLift 6483555
  have htrace : WordTrace (prefixWord ++ tailWord_6483555) baseStart_6483555 baseEnd_6483555 := by
    simpa [prefixWord, tailWord_6483555, baseEnd_6483555] using wordTrace_append hprefix tailTrace_6483555
  have hstable : (prefixWord ++ tailWord_6483555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483555).length < 2 ^ (prefixWord ++ tailWord_6483555).sum := by decide
  have hdescent : baseEnd_6483555 < baseStart_6483555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483575 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_6483575 : Nat := 118140960795 + 6483575 * 2 ^ 59
def prefixEnd_6483575 : Nat := 4983230072969 + 3 ^ 40 * 6483575 * 2
def baseEnd_6483575 : Nat := 3329190334474575716695087

theorem tailTrace_6483575 : CollatzResearch.WordTrace tailWord_6483575 prefixEnd_6483575 3329190334474575716695087 := by
  unfold tailWord_6483575
  simp only [CollatzResearch.WordTrace]
  refine ⟨236475407486122556297940179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157650271657415037531960119 236475407486122556297940179)
  ·
    refine ⟨354713111229183834446910269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236475407486122556297940179 354713111229183834446910269)
    ·
      refine ⟨133017416710943937917591351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354713111229183834446910269 133017416710943937917591351)
      ·
        refine ⟨199526125066415906876387027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133017416710943937917591351 199526125066415906876387027)
        ·
          refine ⟨299289187599623860314580541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199526125066415906876387027 299289187599623860314580541)
          ·
            refine ⟨112233445349858947617967703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299289187599623860314580541 112233445349858947617967703)
            ·
              refine ⟨168350168024788421426951555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112233445349858947617967703 168350168024788421426951555)
              ·
                refine ⟨252525252037182632140427333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168350168024788421426951555 252525252037182632140427333)
                ·
                  refine ⟨47348484756971743526330125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252525252037182632140427333 47348484756971743526330125)
                  ·
                    refine ⟨17755681783864403822373797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47348484756971743526330125 17755681783864403822373797)
                    ·
                      refine ⟨3329190334474575716695087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17755681783864403822373797 3329190334474575716695087)
                      ·
                        rfl

theorem cell23_6483575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_6483575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483575 prefixEnd_6483575 := by exact prefixLift 6483575
  have htrace : WordTrace (prefixWord ++ tailWord_6483575) baseStart_6483575 baseEnd_6483575 := by
    simpa [prefixWord, tailWord_6483575, baseEnd_6483575] using wordTrace_append hprefix tailTrace_6483575
  have hstable : (prefixWord ++ tailWord_6483575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483575).length < 2 ^ (prefixWord ++ tailWord_6483575).sum := by decide
  have hdescent : baseEnd_6483575 < baseStart_6483575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483579 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 1, 3, 2]
def baseStart_6483579 : Nat := 118140960795 + 6483579 * 2 ^ 59
def prefixEnd_6483579 : Nat := 4983230072969 + 3 ^ 40 * 6483579 * 2
def baseEnd_6483579 : Nat := 3329192388397193701045069

theorem tailTrace_6483579 : CollatzResearch.WordTrace tailWord_6483579 prefixEnd_6483579 3329192388397193701045069 := by
  unfold tailWord_6483579
  simp only [CollatzResearch.WordTrace]
  refine ⟨236475553378108064981085791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157650368918738709987390527 236475553378108064981085791)
  ·
    refine ⟨354713330067162097471628687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236475553378108064981085791 354713330067162097471628687)
    ·
      refine ⟨532069995100743146207443031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354713330067162097471628687 532069995100743146207443031)
      ·
        refine ⟨798104992651114719311164547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532069995100743146207443031 798104992651114719311164547)
        ·
          refine ⟨1197157488976672078966746821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798104992651114719311164547 1197157488976672078966746821)
          ·
            refine ⟨224467029183126014806265029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1197157488976672078966746821 224467029183126014806265029)
            ·
              refine ⟨42087567971836127776174693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224467029183126014806265029 42087567971836127776174693)
              ·
                refine ⟨7891418994719273958032755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42087567971836127776174693 7891418994719273958032755)
                ·
                  refine ⟨11837128492078910937049133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891418994719273958032755 11837128492078910937049133)
                  ·
                    refine ⟨4438923184529591601393425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11837128492078910937049133 4438923184529591601393425)
                    ·
                      refine ⟨3329192388397193701045069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438923184529591601393425 3329192388397193701045069)
                      ·
                        rfl

theorem cell23_6483579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 3, 2].length) (baseStart_6483579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483579 prefixEnd_6483579 := by exact prefixLift 6483579
  have htrace : WordTrace (prefixWord ++ tailWord_6483579) baseStart_6483579 baseEnd_6483579 := by
    simpa [prefixWord, tailWord_6483579, baseEnd_6483579] using wordTrace_append hprefix tailTrace_6483579
  have hstable : (prefixWord ++ tailWord_6483579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483579).length < 2 ^ (prefixWord ++ tailWord_6483579).sum := by decide
  have hdescent : baseEnd_6483579 < baseStart_6483579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483595 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5]
def baseStart_6483595 : Nat := 118140960795 + 6483595 * 2 ^ 59
def prefixEnd_6483595 : Nat := 4983230072969 + 3 ^ 40 * 6483595 * 2
def baseEnd_6483595 : Nat := 3329200604087665638444995

theorem tailTrace_6483595 : CollatzResearch.WordTrace tailWord_6483595 prefixEnd_6483595 3329200604087665638444995 := by
  unfold tailWord_6483595
  simp only [CollatzResearch.WordTrace]
  refine ⟨236476136946050099713668239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157650757964033399809112159 236476136946050099713668239)
  ·
    refine ⟨354714205419075149570502359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236476136946050099713668239 354714205419075149570502359)
    ·
      refine ⟨532071308128612724355753539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354714205419075149570502359 532071308128612724355753539)
      ·
        refine ⟨798106962192919086533630309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532071308128612724355753539 798106962192919086533630309)
        ·
          refine ⟨149645055411172328725055683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 798106962192919086533630309 149645055411172328725055683)
          ·
            refine ⟨224467583116758493087583525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149645055411172328725055683 224467583116758493087583525)
            ·
              refine ⟨42087671834392217453921911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224467583116758493087583525 42087671834392217453921911)
              ·
                refine ⟨63131507751588326180882867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42087671834392217453921911 63131507751588326180882867)
                ·
                  refine ⟨94697261627382489271324301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63131507751588326180882867 94697261627382489271324301)
                  ·
                    refine ⟨35511473110268433476746613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94697261627382489271324301 35511473110268433476746613)
                    ·
                      refine ⟨3329200604087665638444995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35511473110268433476746613 3329200604087665638444995)
                      ·
                        rfl

theorem cell23_6483595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_6483595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483595 prefixEnd_6483595 := by exact prefixLift 6483595
  have htrace : WordTrace (prefixWord ++ tailWord_6483595) baseStart_6483595 baseEnd_6483595 := by
    simpa [prefixWord, tailWord_6483595, baseEnd_6483595] using wordTrace_append hprefix tailTrace_6483595
  have hstable : (prefixWord ++ tailWord_6483595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483595).length < 2 ^ (prefixWord ++ tailWord_6483595).sum := by decide
  have hdescent : baseEnd_6483595 < baseStart_6483595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483630 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6483630 : Nat := 118140960795 + 6483630 * 2 ^ 59
def prefixEnd_6483630 : Nat := 4983230072969 + 3 ^ 40 * 6483630 * 2
def baseEnd_6483630 : Nat := 3329218575910573001507335

theorem tailTrace_6483630 : CollatzResearch.WordTrace tailWord_6483630 prefixEnd_6483630 3329218575910573001507335 := by
  unfold tailWord_6483630
  simp only [CollatzResearch.WordTrace]
  refine ⟨29559676687615412586399043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157651609000615533794128229 29559676687615412586399043)
  ·
    refine ⟨44339515031423118879598565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29559676687615412586399043 44339515031423118879598565)
    ·
      refine ⟨8313659068391834789924731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44339515031423118879598565 8313659068391834789924731)
      ·
        refine ⟨12470488602587752184887097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8313659068391834789924731 12470488602587752184887097)
        ·
          refine ⟨9352866451940814138665323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12470488602587752184887097 9352866451940814138665323)
          ·
            refine ⟨14029299677911221207997985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9352866451940814138665323 14029299677911221207997985)
            ·
              refine ⟨10521974758433415905998489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14029299677911221207997985 10521974758433415905998489)
              ·
                refine ⟨7891481068825061929498867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10521974758433415905998489 7891481068825061929498867)
                ·
                  refine ⟨11837221603237592894248301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891481068825061929498867 11837221603237592894248301)
                  ·
                    refine ⟨4438958101214097335343113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11837221603237592894248301 4438958101214097335343113)
                    ·
                      refine ⟨3329218575910573001507335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438958101214097335343113 3329218575910573001507335)
                      ·
                        rfl

theorem cell23_6483630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6483630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483630 prefixEnd_6483630 := by exact prefixLift 6483630
  have htrace : WordTrace (prefixWord ++ tailWord_6483630) baseStart_6483630 baseEnd_6483630 := by
    simpa [prefixWord, tailWord_6483630, baseEnd_6483630] using wordTrace_append hprefix tailTrace_6483630
  have hstable : (prefixWord ++ tailWord_6483630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483630).length < 2 ^ (prefixWord ++ tailWord_6483630).sum := by decide
  have hdescent : baseEnd_6483630 < baseStart_6483630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483672 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6483672 : Nat := 118140960795 + 6483672 * 2 ^ 59
def prefixEnd_6483672 : Nat := 4983230072969 + 3 ^ 40 * 6483672 * 2
def baseEnd_6483672 : Nat := 3329240142098061837182141

theorem tailTrace_6483672 : CollatzResearch.WordTrace tailWord_6483672 prefixEnd_6483672 3329240142098061837182141 := by
  unfold tailWord_6483672
  simp only [CollatzResearch.WordTrace]
  refine ⟨118239472683385570932110635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157652630244514094576147513 118239472683385570932110635)
  ·
    refine ⟨177359209025078356398165953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118239472683385570932110635 177359209025078356398165953)
    ·
      refine ⟨133019406768808767298624465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177359209025078356398165953 133019406768808767298624465)
      ·
        refine ⟨99764555076606575473968349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133019406768808767298624465 99764555076606575473968349)
        ·
          refine ⟨37411708153727465802738131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99764555076606575473968349 37411708153727465802738131)
          ·
            refine ⟨56117562230591198704107197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37411708153727465802738131 56117562230591198704107197)
            ·
              refine ⟨21044085836471699514040199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56117562230591198704107197 21044085836471699514040199)
              ·
                refine ⟨31566128754707549271060299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21044085836471699514040199 31566128754707549271060299)
                ·
                  refine ⟨47349193132061323906590449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31566128754707549271060299 47349193132061323906590449)
                  ·
                    refine ⟨35511894849045992929942837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47349193132061323906590449 35511894849045992929942837)
                    ·
                      refine ⟨3329240142098061837182141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35511894849045992929942837 3329240142098061837182141)
                      ·
                        rfl

theorem cell23_6483672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6483672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483672 prefixEnd_6483672 := by exact prefixLift 6483672
  have htrace : WordTrace (prefixWord ++ tailWord_6483672) baseStart_6483672 baseEnd_6483672 := by
    simpa [prefixWord, tailWord_6483672, baseEnd_6483672] using wordTrace_append hprefix tailTrace_6483672
  have hstable : (prefixWord ++ tailWord_6483672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483672).length < 2 ^ (prefixWord ++ tailWord_6483672).sum := by decide
  have hdescent : baseEnd_6483672 < baseStart_6483672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483759 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 1, 5, 2]
def baseStart_6483759 : Nat := 118140960795 + 6483759 * 2 ^ 59
def prefixEnd_6483759 : Nat := 4983230072969 + 3 ^ 40 * 6483759 * 2
def baseEnd_6483759 : Nat := 3329284814915002996794241

theorem tailTrace_6483759 : CollatzResearch.WordTrace tailWord_6483759 prefixEnd_6483759 3329284814915002996794241 := by
  unfold tailWord_6483759
  simp only [CollatzResearch.WordTrace]
  refine ⟨236482118517455955722638331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157654745678303970481758887 236482118517455955722638331)
  ·
    refine ⟨354723177776183933583957497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236482118517455955722638331 354723177776183933583957497)
    ·
      refine ⟨266042383332137950187968123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354723177776183933583957497 266042383332137950187968123)
      ·
        refine ⟨399063574998206925281952185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266042383332137950187968123 399063574998206925281952185)
        ·
          refine ⟨299297681248655193961464139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399063574998206925281952185 299297681248655193961464139)
          ·
            refine ⟨448946521872982790942196209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299297681248655193961464139 448946521872982790942196209)
            ·
              refine ⟨336709891404737093206647157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448946521872982790942196209 336709891404737093206647157)
              ·
                refine ⟨31566552319194102488123171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336709891404737093206647157 31566552319194102488123171)
                ·
                  refine ⟨47349828478791153732184757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31566552319194102488123171 47349828478791153732184757)
                  ·
                    refine ⟨4439046419886670662392321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47349828478791153732184757 4439046419886670662392321)
                    ·
                      refine ⟨3329284814915002996794241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439046419886670662392321 3329284814915002996794241)
                      ·
                        rfl

theorem cell23_6483759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5, 2].length) (baseStart_6483759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483759 prefixEnd_6483759 := by exact prefixLift 6483759
  have htrace : WordTrace (prefixWord ++ tailWord_6483759) baseStart_6483759 baseEnd_6483759 := by
    simpa [prefixWord, tailWord_6483759, baseEnd_6483759] using wordTrace_append hprefix tailTrace_6483759
  have hstable : (prefixWord ++ tailWord_6483759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483759).length < 2 ^ (prefixWord ++ tailWord_6483759).sum := by decide
  have hdescent : baseEnd_6483759 < baseStart_6483759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483783 : List Nat := [1, 1, 4, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_6483783 : Nat := 118140960795 + 6483783 * 2 ^ 59
def prefixEnd_6483783 : Nat := 4983230072969 + 3 ^ 40 * 6483783 * 2
def baseEnd_6483783 : Nat := 3329297138450710902894131

theorem tailTrace_6483783 : CollatzResearch.WordTrace tailWord_6483783 prefixEnd_6483783 3329297138450710902894131 := by
  unfold tailWord_6483783
  simp only [CollatzResearch.WordTrace]
  refine ⟨236482993869369007821512003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157655329246246005214341335 236482993869369007821512003)
  ·
    refine ⟨354724490804053511732268005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236482993869369007821512003 354724490804053511732268005)
    ·
      refine ⟨66510842025760033449800251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354724490804053511732268005 66510842025760033449800251)
      ·
        refine ⟨99766263038640050174700377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66510842025760033449800251 99766263038640050174700377)
        ·
          refine ⟨74824697278980037631025283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99766263038640050174700377 74824697278980037631025283)
          ·
            refine ⟨112237045918470056446537925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74824697278980037631025283 112237045918470056446537925)
            ·
              refine ⟨21044446109713135583725861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112237045918470056446537925 21044446109713135583725861)
              ·
                refine ⟨3945833645571212921948599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21044446109713135583725861 3945833645571212921948599)
                ·
                  refine ⟨5918750468356819382922899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945833645571212921948599 5918750468356819382922899)
                  ·
                    refine ⟨8878125702535229074384349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5918750468356819382922899 8878125702535229074384349)
                    ·
                      refine ⟨3329297138450710902894131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8878125702535229074384349 3329297138450710902894131)
                      ·
                        rfl

theorem cell23_6483783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_6483783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483783 prefixEnd_6483783 := by exact prefixLift 6483783
  have htrace : WordTrace (prefixWord ++ tailWord_6483783) baseStart_6483783 baseEnd_6483783 := by
    simpa [prefixWord, tailWord_6483783, baseEnd_6483783] using wordTrace_append hprefix tailTrace_6483783
  have hstable : (prefixWord ++ tailWord_6483783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483783).length < 2 ^ (prefixWord ++ tailWord_6483783).sum := by decide
  have hdescent : baseEnd_6483783 < baseStart_6483783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483860 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_6483860 : Nat := 118140960795 + 6483860 * 2 ^ 59
def prefixEnd_6483860 : Nat := 4983230072969 + 3 ^ 40 * 6483860 * 2
def baseEnd_6483860 : Nat := 3329336676461107101631277

theorem tailTrace_6483860 : CollatzResearch.WordTrace tailWord_6483860 prefixEnd_6483860 3329336676461107101631277 := by
  unfold tailWord_6483860
  simp only [CollatzResearch.WordTrace]
  refine ⟨118242901145045024986032517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157657201526726699981376689 118242901145045024986032517)
  ·
    refine ⟨22170543964695942184881097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118242901145045024986032517 22170543964695942184881097)
    ·
      refine ⟨16627907973521956638660823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22170543964695942184881097 16627907973521956638660823)
      ·
        refine ⟨24941861960282934957991235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16627907973521956638660823 24941861960282934957991235)
        ·
          refine ⟨37412792940424402436986853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24941861960282934957991235 37412792940424402436986853)
          ·
            refine ⟨7014898676329575456935035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37412792940424402436986853 7014898676329575456935035)
            ·
              refine ⟨10522348014494363185402553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014898676329575456935035 10522348014494363185402553)
              ·
                refine ⟨7891761010870772389051915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10522348014494363185402553 7891761010870772389051915)
                ·
                  refine ⟨11837641516306158583577873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891761010870772389051915 11837641516306158583577873)
                  ·
                    refine ⟨8878231137229618937683405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11837641516306158583577873 8878231137229618937683405)
                    ·
                      refine ⟨3329336676461107101631277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8878231137229618937683405 3329336676461107101631277)
                      ·
                        rfl

theorem cell23_6483860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_6483860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483860 prefixEnd_6483860 := by exact prefixLift 6483860
  have htrace : WordTrace (prefixWord ++ tailWord_6483860) baseStart_6483860 baseEnd_6483860 := by
    simpa [prefixWord, tailWord_6483860, baseEnd_6483860] using wordTrace_append hprefix tailTrace_6483860
  have hstable : (prefixWord ++ tailWord_6483860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483860).length < 2 ^ (prefixWord ++ tailWord_6483860).sum := by decide
  have hdescent : baseEnd_6483860 < baseStart_6483860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483870 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6483870 : Nat := 118140960795 + 6483870 * 2 ^ 59
def prefixEnd_6483870 : Nat := 4983230072969 + 3 ^ 40 * 6483870 * 2
def baseEnd_6483870 : Nat := 3329341811267652062506231

theorem tailTrace_6483870 : CollatzResearch.WordTrace tailWord_6483870 prefixEnd_6483870 3329341811267652062506231 := by
  unfold tailWord_6483870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29560770877506727709991133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157657444680035881119952709 29560770877506727709991133)
  ·
    refine ⟨11085289079065022891246675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29560770877506727709991133 11085289079065022891246675)
    ·
      refine ⟨16627933618597534336870013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11085289079065022891246675 16627933618597534336870013)
      ·
        refine ⟨6235475106974075376326255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16627933618597534336870013 6235475106974075376326255)
        ·
          refine ⟨9353212660461113064489383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6235475106974075376326255 9353212660461113064489383)
          ·
            refine ⟨14029818990691669596734075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353212660461113064489383 14029818990691669596734075)
            ·
              refine ⟨21044728486037504395101113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14029818990691669596734075 21044728486037504395101113)
              ·
                refine ⟨15783546364528128296325835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21044728486037504395101113 15783546364528128296325835)
                ·
                  refine ⟨23675319546792192444488753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15783546364528128296325835 23675319546792192444488753)
                  ·
                    refine ⟨17756489660094144333366565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23675319546792192444488753 17756489660094144333366565)
                    ·
                      refine ⟨3329341811267652062506231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17756489660094144333366565 3329341811267652062506231)
                      ·
                        rfl

theorem cell23_6483870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6483870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483870 prefixEnd_6483870 := by exact prefixLift 6483870
  have htrace : WordTrace (prefixWord ++ tailWord_6483870) baseStart_6483870 baseEnd_6483870 := by
    simpa [prefixWord, tailWord_6483870, baseEnd_6483870] using wordTrace_append hprefix tailTrace_6483870
  have hstable : (prefixWord ++ tailWord_6483870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483870).length < 2 ^ (prefixWord ++ tailWord_6483870).sum := by decide
  have hdescent : baseEnd_6483870 < baseStart_6483870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483873 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6483873 : Nat := 118140960795 + 6483873 * 2 ^ 59
def prefixEnd_6483873 : Nat := 4983230072969 + 3 ^ 40 * 6483873 * 2
def baseEnd_6483873 : Nat := 3329343351709615550768717

theorem tailTrace_6483873 : CollatzResearch.WordTrace tailWord_6483873 prefixEnd_6483873 3329343351709615550768717 := by
  unfold tailWord_6483873
  simp only [CollatzResearch.WordTrace]
  refine ⟨236486276439042953192288273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157657517626028635461525515 236486276439042953192288273)
  ·
    refine ⟨177364707329282214894216205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236486276439042953192288273 177364707329282214894216205)
    ·
      refine ⟨66511765248480830585331077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177364707329282214894216205 66511765248480830585331077)
      ·
        refine ⟨12470955984090155734749577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66511765248480830585331077 12470955984090155734749577)
        ·
          refine ⟨9353216988067616801062183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12470955984090155734749577 9353216988067616801062183)
          ·
            refine ⟨14029825482101425201593275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353216988067616801062183 14029825482101425201593275)
            ·
              refine ⟨21044738223152137802389913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14029825482101425201593275 21044738223152137802389913)
              ·
                refine ⟨15783553667364103351792435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21044738223152137802389913 15783553667364103351792435)
                ·
                  refine ⟨23675330501046155027688653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15783553667364103351792435 23675330501046155027688653)
                  ·
                    refine ⟨8878248937892308135383245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23675330501046155027688653 8878248937892308135383245)
                    ·
                      refine ⟨3329343351709615550768717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8878248937892308135383245 3329343351709615550768717)
                      ·
                        rfl

theorem cell23_6483873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6483873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483873 prefixEnd_6483873 := by exact prefixLift 6483873
  have htrace : WordTrace (prefixWord ++ tailWord_6483873) baseStart_6483873 baseEnd_6483873 := by
    simpa [prefixWord, tailWord_6483873, baseEnd_6483873] using wordTrace_append hprefix tailTrace_6483873
  have hstable : (prefixWord ++ tailWord_6483873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483873).length < 2 ^ (prefixWord ++ tailWord_6483873).sum := by decide
  have hdescent : baseEnd_6483873 < baseStart_6483873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483896 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 3, 4, 2]
def baseStart_6483896 : Nat := 118140960795 + 6483896 * 2 ^ 59
def prefixEnd_6483896 : Nat := 4983230072969 + 3 ^ 40 * 6483896 * 2
def baseEnd_6483896 : Nat := 3329355161764668960781111

theorem tailTrace_6483896 : CollatzResearch.WordTrace tailWord_6483896 prefixEnd_6483896 3329355161764668960781111 := by
  unfold tailWord_6483896
  simp only [CollatzResearch.WordTrace]
  refine ⟨118243557658979814060187771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157658076878639752080250361 118243557658979814060187771)
  ·
    refine ⟨177365336488469721090281657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118243557658979814060187771 177365336488469721090281657)
    ·
      refine ⟨133024002366352290817711243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177365336488469721090281657 133024002366352290817711243)
      ·
        refine ⟨199536003549528436226566865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133024002366352290817711243 199536003549528436226566865)
        ·
          refine ⟨149652002662146327169925149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199536003549528436226566865 149652002662146327169925149)
          ·
            refine ⟨56119500998304872688721931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149652002662146327169925149 56119500998304872688721931)
            ·
              refine ⟨84179251497457309033082897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56119500998304872688721931 84179251497457309033082897)
              ·
                refine ⟨63134438623092981774812173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84179251497457309033082897 63134438623092981774812173)
                ·
                  refine ⟨23675414483659868165554565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63134438623092981774812173 23675414483659868165554565)
                  ·
                    refine ⟨4439140215686225281041481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23675414483659868165554565 4439140215686225281041481)
                    ·
                      refine ⟨3329355161764668960781111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439140215686225281041481 3329355161764668960781111)
                      ·
                        rfl

theorem cell23_6483896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_6483896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483896 prefixEnd_6483896 := by exact prefixLift 6483896
  have htrace : WordTrace (prefixWord ++ tailWord_6483896) baseStart_6483896 baseEnd_6483896 := by
    simpa [prefixWord, tailWord_6483896, baseEnd_6483896] using wordTrace_append hprefix tailTrace_6483896
  have hstable : (prefixWord ++ tailWord_6483896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483896).length < 2 ^ (prefixWord ++ tailWord_6483896).sum := by decide
  have hdescent : baseEnd_6483896 < baseStart_6483896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483899 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 3]
def baseStart_6483899 : Nat := 118140960795 + 6483899 * 2 ^ 59
def prefixEnd_6483899 : Nat := 4983230072969 + 3 ^ 40 * 6483899 * 2
def baseEnd_6483899 : Nat := 3329356702206632449043597

theorem tailTrace_6483899 : CollatzResearch.WordTrace tailWord_6483899 prefixEnd_6483899 3329356702206632449043597 := by
  unfold tailWord_6483899
  simp only [CollatzResearch.WordTrace]
  refine ⟨236487224736948759632734751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157658149824632506421823167 236487224736948759632734751)
  ·
    refine ⟨354730837105423139449102127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236487224736948759632734751 354730837105423139449102127)
    ·
      refine ⟨532096255658134709173653191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354730837105423139449102127 532096255658134709173653191)
      ·
        refine ⟨798144383487202063760479787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532096255658134709173653191 798144383487202063760479787)
        ·
          refine ⟨1197216575230803095640719681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798144383487202063760479787 1197216575230803095640719681)
          ·
            refine ⟨897912431423102321730539761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197216575230803095640719681 897912431423102321730539761)
            ·
              refine ⟨673434323567326741297904821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897912431423102321730539761 673434323567326741297904821)
              ·
                refine ⟨63134467834436881996678577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 673434323567326741297904821 63134467834436881996678577)
                ·
                  refine ⟨47350850875827661497508933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63134467834436881996678577 47350850875827661497508933)
                  ·
                    refine ⟨8878284539217686530782925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47350850875827661497508933 8878284539217686530782925)
                    ·
                      refine ⟨3329356702206632449043597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8878284539217686530782925 3329356702206632449043597)
                      ·
                        rfl

theorem cell23_6483899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 3].length) (baseStart_6483899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483899 prefixEnd_6483899 := by exact prefixLift 6483899
  have htrace : WordTrace (prefixWord ++ tailWord_6483899) baseStart_6483899 baseEnd_6483899 := by
    simpa [prefixWord, tailWord_6483899, baseEnd_6483899] using wordTrace_append hprefix tailTrace_6483899
  have hstable : (prefixWord ++ tailWord_6483899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483899).length < 2 ^ (prefixWord ++ tailWord_6483899).sum := by decide
  have hdescent : baseEnd_6483899 < baseStart_6483899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483919 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 7]
def baseStart_6483919 : Nat := 118140960795 + 6483919 * 2 ^ 59
def prefixEnd_6483919 : Nat := 4983230072969 + 3 ^ 40 * 6483919 * 2
def baseEnd_6483919 : Nat := 369929663535524707865945

theorem tailTrace_6483919 : CollatzResearch.WordTrace tailWord_6483919 prefixEnd_6483919 369929663535524707865945 := by
  unfold tailWord_6483919
  simp only [CollatzResearch.WordTrace]
  refine ⟨236487954196876303048462811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157658636131250868698975207 236487954196876303048462811)
  ·
    refine ⟨354731931295314454572694217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236487954196876303048462811 354731931295314454572694217)
    ·
      refine ⟨266048948471485840929520663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354731931295314454572694217 266048948471485840929520663)
      ·
        refine ⟨399073422707228761394280995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266048948471485840929520663 399073422707228761394280995)
        ·
          refine ⟨598610134060843142091421493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399073422707228761394280995 598610134060843142091421493)
          ·
            refine ⟨56119700068204044571070765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 598610134060843142091421493 56119700068204044571070765)
            ·
              refine ⟨21044887525576516714151537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56119700068204044571070765 21044887525576516714151537)
              ·
                refine ⟨15783665644182387535613653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21044887525576516714151537 15783665644182387535613653)
                ·
                  refine ⟨369929663535524707865945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15783665644182387535613653 369929663535524707865945)
                  ·
                    rfl

theorem cell23_6483919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 7].length) (baseStart_6483919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483919 prefixEnd_6483919 := by exact prefixLift 6483919
  have htrace : WordTrace (prefixWord ++ tailWord_6483919) baseStart_6483919 baseEnd_6483919 := by
    simpa [prefixWord, tailWord_6483919, baseEnd_6483919] using wordTrace_append hprefix tailTrace_6483919
  have hstable : (prefixWord ++ tailWord_6483919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483919).length < 2 ^ (prefixWord ++ tailWord_6483919).sum := by decide
  have hdescent : baseEnd_6483919 < baseStart_6483919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483946 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_6483946 : Nat := 118140960795 + 6483946 * 2 ^ 59
def prefixEnd_6483946 : Nat := 4983230072969 + 3 ^ 40 * 6483946 * 2
def baseEnd_6483946 : Nat := 3329380835797393765155881

theorem tailTrace_6483946 : CollatzResearch.WordTrace tailWord_6483946 prefixEnd_6483946 3329380835797393765155881 := by
  unfold tailWord_6483946
  simp only [CollatzResearch.WordTrace]
  refine ⟨59122234741944621664923923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157659292645185657773130461 59122234741944621664923923)
  ·
    refine ⟨88683352112916932497385885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59122234741944621664923923 88683352112916932497385885)
    ·
      refine ⟨33256257042343849686519707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88683352112916932497385885 33256257042343849686519707)
      ·
        refine ⟨49884385563515774529779561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33256257042343849686519707 49884385563515774529779561)
        ·
          refine ⟨37413289172636830897334671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49884385563515774529779561 37413289172636830897334671)
          ·
            refine ⟨56119933758955246346002007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37413289172636830897334671 56119933758955246346002007)
            ·
              refine ⟨84179900638432869519003011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56119933758955246346002007 84179900638432869519003011)
              ·
                refine ⟨126269850957649304278504517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84179900638432869519003011 126269850957649304278504517)
                ·
                  refine ⟨23675597054559244552219597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126269850957649304278504517 23675597054559244552219597)
                  ·
                    refine ⟨8878348895459716707082349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23675597054559244552219597 8878348895459716707082349)
                    ·
                      refine ⟨3329380835797393765155881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8878348895459716707082349 3329380835797393765155881)
                      ·
                        rfl

theorem cell23_6483946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_6483946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483946 prefixEnd_6483946 := by exact prefixLift 6483946
  have htrace : WordTrace (prefixWord ++ tailWord_6483946) baseStart_6483946 baseEnd_6483946 := by
    simpa [prefixWord, tailWord_6483946, baseEnd_6483946] using wordTrace_append hprefix tailTrace_6483946
  have hstable : (prefixWord ++ tailWord_6483946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483946).length < 2 ^ (prefixWord ++ tailWord_6483946).sum := by decide
  have hdescent : baseEnd_6483946 < baseStart_6483946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6483979 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 2, 8]
def baseStart_6483979 : Nat := 118140960795 + 6483979 * 2 ^ 59
def prefixEnd_6483979 : Nat := 4983230072969 + 3 ^ 40 * 6483979 * 2
def baseEnd_6483979 : Nat := 1109799260219664045347743

theorem tailTrace_6483979 : CollatzResearch.WordTrace tailWord_6483979 prefixEnd_6483979 1109799260219664045347743 := by
  unfold tailWord_6483979
  simp only [CollatzResearch.WordTrace]
  refine ⟨236490142576658933295646991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157660095051105955530431327 236490142576658933295646991)
  ·
    refine ⟨354735213864988399943470487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236490142576658933295646991 354735213864988399943470487)
    ·
      refine ⟨532102820797482599915205731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354735213864988399943470487 532102820797482599915205731)
      ·
        refine ⟨798154231196223899872808597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532102820797482599915205731 798154231196223899872808597)
        ·
          refine ⟨37413479587322995306537903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 798154231196223899872808597 37413479587322995306537903)
          ·
            refine ⟨56120219380984492959806855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37413479587322995306537903 56120219380984492959806855)
            ·
              refine ⟨84180329071476739439710283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56120219380984492959806855 84180329071476739439710283)
              ·
                refine ⟨126270493607215109159565425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84180329071476739439710283 126270493607215109159565425)
                ·
                  refine ⟨94702870205411331869674069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126270493607215109159565425 94702870205411331869674069)
                  ·
                    refine ⟨1109799260219664045347743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94702870205411331869674069 1109799260219664045347743)
                    ·
                      rfl

theorem cell23_6483979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_6483979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6483979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6483979 prefixEnd_6483979 := by exact prefixLift 6483979
  have htrace : WordTrace (prefixWord ++ tailWord_6483979) baseStart_6483979 baseEnd_6483979 := by
    simpa [prefixWord, tailWord_6483979, baseEnd_6483979] using wordTrace_append hprefix tailTrace_6483979
  have hstable : (prefixWord ++ tailWord_6483979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6483979).length < 2 ^ (prefixWord ++ tailWord_6483979).sum := by decide
  have hdescent : baseEnd_6483979 < baseStart_6483979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6483979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484063 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 4, 3, 2]
def baseStart_6484063 : Nat := 118140960795 + 6484063 * 2 ^ 59
def prefixEnd_6484063 : Nat := 4983230072969 + 3 ^ 40 * 6484063 * 2
def baseEnd_6484063 : Nat := 3329440913033969807392843

theorem tailTrace_6484063 : CollatzResearch.WordTrace tailWord_6484063 prefixEnd_6484063 3329440913033969807392843 := by
  unfold tailWord_6484063
  simp only [CollatzResearch.WordTrace]
  refine ⟨236493206308354615641704843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157662137538903077094469895 236493206308354615641704843)
  ·
    refine ⟨354739809462531923462557265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236493206308354615641704843 354739809462531923462557265)
    ·
      refine ⟨266054857096898942596917949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354739809462531923462557265 266054857096898942596917949)
      ·
        refine ⟨99770571411337103473844231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266054857096898942596917949 99770571411337103473844231)
        ·
          refine ⟨149655857117005655210766347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99770571411337103473844231 149655857117005655210766347)
          ·
            refine ⟨224483785675508482816149521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149655857117005655210766347 224483785675508482816149521)
            ·
              refine ⟨168362839256631362112112141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224483785675508482816149521 168362839256631362112112141)
              ·
                refine ⟨63136064721236760792042053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168362839256631362112112141 63136064721236760792042053)
                ·
                  refine ⟨11838012135231892648507885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63136064721236760792042053 11838012135231892648507885)
                  ·
                    refine ⟨4439254550711959743190457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11838012135231892648507885 4439254550711959743190457)
                    ·
                      refine ⟨3329440913033969807392843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439254550711959743190457 3329440913033969807392843)
                      ·
                        rfl

theorem cell23_6484063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_6484063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484063 prefixEnd_6484063 := by exact prefixLift 6484063
  have htrace : WordTrace (prefixWord ++ tailWord_6484063) baseStart_6484063 baseEnd_6484063 := by
    simpa [prefixWord, tailWord_6484063, baseEnd_6484063] using wordTrace_append hprefix tailTrace_6484063
  have hstable : (prefixWord ++ tailWord_6484063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484063).length < 2 ^ (prefixWord ++ tailWord_6484063).sum := by decide
  have hdescent : baseEnd_6484063 < baseStart_6484063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484093 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_6484093 : Nat := 118140960795 + 6484093 * 2 ^ 59
def prefixEnd_6484093 : Nat := 4983230072969 + 3 ^ 40 * 6484093 * 2
def baseEnd_6484093 : Nat := 3329456317453604690017705

theorem tailTrace_6484093 : CollatzResearch.WordTrace tailWord_6484093 prefixEnd_6484093 3329456317453604690017705 := by
  unfold tailWord_6484093
  simp only [CollatzResearch.WordTrace]
  refine ⟨236494300498245930765296933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157662866998830620510197955 236494300498245930765296933)
  ·
    refine ⟨44342681343421112018493175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236494300498245930765296933 44342681343421112018493175)
    ·
      refine ⟨66514022015131668027739763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44342681343421112018493175 66514022015131668027739763)
      ·
        refine ⟨99771033022697502041609645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66514022015131668027739763 99771033022697502041609645)
        ·
          refine ⟨37414137383511563265603617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99771033022697502041609645 37414137383511563265603617)
          ·
            refine ⟨28060603037633672449202713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37414137383511563265603617 28060603037633672449202713)
            ·
              refine ⟨21045452278225254336902035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28060603037633672449202713 21045452278225254336902035)
              ·
                refine ⟨31568178417337881505353053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21045452278225254336902035 31568178417337881505353053)
                ·
                  refine ⟨11838066906501705564507395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31568178417337881505353053 11838066906501705564507395)
                  ·
                    refine ⟨17757100359752558346761093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11838066906501705564507395 17757100359752558346761093)
                    ·
                      refine ⟨3329456317453604690017705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17757100359752558346761093 3329456317453604690017705)
                      ·
                        rfl

theorem cell23_6484093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_6484093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484093 prefixEnd_6484093 := by exact prefixLift 6484093
  have htrace : WordTrace (prefixWord ++ tailWord_6484093) baseStart_6484093 baseEnd_6484093 := by
    simpa [prefixWord, tailWord_6484093, baseEnd_6484093] using wordTrace_append hprefix tailTrace_6484093
  have hstable : (prefixWord ++ tailWord_6484093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484093).length < 2 ^ (prefixWord ++ tailWord_6484093).sum := by decide
  have hdescent : baseEnd_6484093 < baseStart_6484093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484104 : List Nat := [2, 1, 3, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6484104 : Nat := 118140960795 + 6484104 * 2 ^ 59
def prefixEnd_6484104 : Nat := 4983230072969 + 3 ^ 40 * 6484104 * 2
def baseEnd_6484104 : Nat := 3329461965740804146980155

theorem tailTrace_6484104 : CollatzResearch.WordTrace tailWord_6484104 prefixEnd_6484104 3329461965740804146980155 := by
  unfold tailWord_6484104
  simp only [CollatzResearch.WordTrace]
  refine ⟨118247350850603039821973683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157663134467470719762631577 118247350850603039821973683)
  ·
    refine ⟨177371026275904559732960525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118247350850603039821973683 177371026275904559732960525)
    ·
      refine ⟨66514134853464209899860197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177371026275904559732960525 66514134853464209899860197)
      ·
        refine ⟨12471400285024539356223787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66514134853464209899860197 12471400285024539356223787)
        ·
          refine ⟨18707100427536809034335681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471400285024539356223787 18707100427536809034335681)
          ·
            refine ⟨14030325320652606775751761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18707100427536809034335681 14030325320652606775751761)
            ·
              refine ⟨10522743990489455081813821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14030325320652606775751761 10522743990489455081813821)
              ·
                refine ⟨3946028996433545655680183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10522743990489455081813821 3946028996433545655680183)
                ·
                  refine ⟨5919043494650318483520275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946028996433545655680183 5919043494650318483520275)
                  ·
                    refine ⟨8878565241975477725280413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5919043494650318483520275 8878565241975477725280413)
                    ·
                      refine ⟨3329461965740804146980155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8878565241975477725280413 3329461965740804146980155)
                      ·
                        rfl

theorem cell23_6484104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6484104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484104 prefixEnd_6484104 := by exact prefixLift 6484104
  have htrace : WordTrace (prefixWord ++ tailWord_6484104) baseStart_6484104 baseEnd_6484104 := by
    simpa [prefixWord, tailWord_6484104, baseEnd_6484104] using wordTrace_append hprefix tailTrace_6484104
  have hstable : (prefixWord ++ tailWord_6484104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484104).length < 2 ^ (prefixWord ++ tailWord_6484104).sum := by decide
  have hdescent : baseEnd_6484104 < baseStart_6484104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484120 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 4, 4]
def baseStart_6484120 : Nat := 118140960795 + 6484120 * 2 ^ 59
def prefixEnd_6484120 : Nat := 4983230072969 + 3 ^ 40 * 6484120 * 2
def baseEnd_6484120 : Nat := 1109823393810425361460027

theorem tailTrace_6484120 : CollatzResearch.WordTrace tailWord_6484120 prefixEnd_6484120 1109823393810425361460027 := by
  unfold tailWord_6484120
  simp only [CollatzResearch.WordTrace]
  refine ⟨118247642634574057188264907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157663523512765409584353209 118247642634574057188264907)
  ·
    refine ⟨177371463951861085782397361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118247642634574057188264907 177371463951861085782397361)
    ·
      refine ⟨133028597963895814336798021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177371463951861085782397361 133028597963895814336798021)
      ·
        refine ⟨24942862118230465188149629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133028597963895814336798021 24942862118230465188149629)
        ·
          refine ⟨9353573294336424445556111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24942862118230465188149629 9353573294336424445556111)
          ·
            refine ⟨14030359941504636668334167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353573294336424445556111 14030359941504636668334167)
            ·
              refine ⟨21045539912256955002501251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14030359941504636668334167 21045539912256955002501251)
              ·
                refine ⟨31568309868385432503751877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21045539912256955002501251 31568309868385432503751877)
                ·
                  refine ⟨5919058100322268594453477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31568309868385432503751877 5919058100322268594453477)
                  ·
                    refine ⟨1109823393810425361460027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5919058100322268594453477 1109823393810425361460027)
                    ·
                      rfl

theorem cell23_6484120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_6484120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484120 prefixEnd_6484120 := by exact prefixLift 6484120
  have htrace : WordTrace (prefixWord ++ tailWord_6484120) baseStart_6484120 baseEnd_6484120 := by
    simpa [prefixWord, tailWord_6484120, baseEnd_6484120] using wordTrace_append hprefix tailTrace_6484120
  have hstable : (prefixWord ++ tailWord_6484120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484120).length < 2 ^ (prefixWord ++ tailWord_6484120).sum := by decide
  have hdescent : baseEnd_6484120 < baseStart_6484120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484127 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6484127 : Nat := 118140960795 + 6484127 * 2 ^ 59
def prefixEnd_6484127 : Nat := 4983230072969 + 3 ^ 40 * 6484127 * 2
def baseEnd_6484127 : Nat := 3329473775795857556992549

theorem tailTrace_6484127 : CollatzResearch.WordTrace tailWord_6484127 prefixEnd_6484127 3329473775795857556992549 := by
  unfold tailWord_6484127
  simp only [CollatzResearch.WordTrace]
  refine ⟨236495540580122754572034635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157663693720081836381356423 236495540580122754572034635)
  ·
    refine ⟨354743310870184131858051953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236495540580122754572034635 354743310870184131858051953)
    ·
      refine ⟨266057483152638098893538965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354743310870184131858051953 266057483152638098893538965)
      ·
        refine ⟨12471444522779910885634639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 266057483152638098893538965 12471444522779910885634639)
        ·
          refine ⟨18707166784169866328451959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471444522779910885634639 18707166784169866328451959)
          ·
            refine ⟨28060750176254799492677939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18707166784169866328451959 28060750176254799492677939)
            ·
              refine ⟨42091125264382199239016909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28060750176254799492677939 42091125264382199239016909)
              ·
                refine ⟨15784171974143324714631341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42091125264382199239016909 15784171974143324714631341)
                ·
                  refine ⟨5919064490303746767986753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15784171974143324714631341 5919064490303746767986753)
                  ·
                    refine ⟨4439298367727810075990065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919064490303746767986753 4439298367727810075990065)
                    ·
                      refine ⟨3329473775795857556992549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439298367727810075990065 3329473775795857556992549)
                      ·
                        rfl

theorem cell23_6484127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6484127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484127 prefixEnd_6484127 := by exact prefixLift 6484127
  have htrace : WordTrace (prefixWord ++ tailWord_6484127) baseStart_6484127 baseEnd_6484127 := by
    simpa [prefixWord, tailWord_6484127, baseEnd_6484127] using wordTrace_append hprefix tailTrace_6484127
  have hstable : (prefixWord ++ tailWord_6484127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484127).length < 2 ^ (prefixWord ++ tailWord_6484127).sum := by decide
  have hdescent : baseEnd_6484127 < baseStart_6484127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484130 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_6484130 : Nat := 118140960795 + 6484130 * 2 ^ 59
def prefixEnd_6484130 : Nat := 4983230072969 + 3 ^ 40 * 6484130 * 2
def baseEnd_6484130 : Nat := 3329475316237821045255035

theorem tailTrace_6484130 : CollatzResearch.WordTrace tailWord_6484130 prefixEnd_6484130 3329475316237821045255035 := by
  unfold tailWord_6484130
  simp only [CollatzResearch.WordTrace]
  refine ⟨59123912499777971521098461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157663766666074590722929229 59123912499777971521098461)
  ·
    refine ⟨22171467187416739320411923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59123912499777971521098461 22171467187416739320411923)
    ·
      refine ⟨33257200781125108980617885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22171467187416739320411923 33257200781125108980617885)
      ·
        refine ⟨12471450292921915867731707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33257200781125108980617885 12471450292921915867731707)
        ·
          refine ⟨18707175439382873801597561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471450292921915867731707 18707175439382873801597561)
          ·
            refine ⟨14030381579537155351198171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18707175439382873801597561 14030381579537155351198171)
            ·
              refine ⟨21045572369305733026797257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14030381579537155351198171 21045572369305733026797257)
              ·
                refine ⟨15784179276979299770097943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21045572369305733026797257 15784179276979299770097943)
                ·
                  refine ⟨23676268915468949655146915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15784179276979299770097943 23676268915468949655146915)
                  ·
                    refine ⟨35514403373203424482720373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23676268915468949655146915 35514403373203424482720373)
                    ·
                      refine ⟨3329475316237821045255035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35514403373203424482720373 3329475316237821045255035)
                      ·
                        rfl

theorem cell23_6484130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_6484130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484130 prefixEnd_6484130 := by exact prefixLift 6484130
  have htrace : WordTrace (prefixWord ++ tailWord_6484130) baseStart_6484130 baseEnd_6484130 := by
    simpa [prefixWord, tailWord_6484130, baseEnd_6484130] using wordTrace_append hprefix tailTrace_6484130
  have hstable : (prefixWord ++ tailWord_6484130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484130).length < 2 ^ (prefixWord ++ tailWord_6484130).sum := by decide
  have hdescent : baseEnd_6484130 < baseStart_6484130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484160 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 4, 1, 3]
def baseStart_6484160 : Nat := 118140960795 + 6484160 * 2 ^ 59
def prefixEnd_6484160 : Nat := 4983230072969 + 3 ^ 40 * 6484160 * 2
def baseEnd_6484160 : Nat := 3329490720657455927879897

theorem tailTrace_6484160 : CollatzResearch.WordTrace tailWord_6484160 prefixEnd_6484160 3329490720657455927879897 := by
  unfold tailWord_6484160
  simp only [CollatzResearch.WordTrace]
  refine ⟨118248372094501600603992967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157664496126002134138657289 118248372094501600603992967)
  ·
    refine ⟨177372558141752400905989451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118248372094501600603992967 177372558141752400905989451)
    ·
      refine ⟨266058837212628601358984177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177372558141752400905989451 266058837212628601358984177)
      ·
        refine ⟨199544127909471451019238133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266058837212628601358984177 199544127909471451019238133)
        ·
          refine ⟨18707261991512948533053575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199544127909471451019238133 18707261991512948533053575)
          ·
            refine ⟨28060892987269422799580363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18707261991512948533053575 28060892987269422799580363)
            ·
              refine ⟨42091339480904134199370545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28060892987269422799580363 42091339480904134199370545)
              ·
                refine ⟨31568504610678100649527909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42091339480904134199370545 31568504610678100649527909)
                ·
                  refine ⟨5919094614502143871786483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31568504610678100649527909 5919094614502143871786483)
                  ·
                    refine ⟨8878641921753215807679725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5919094614502143871786483 8878641921753215807679725)
                    ·
                      refine ⟨3329490720657455927879897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8878641921753215807679725 3329490720657455927879897)
                      ·
                        rfl

theorem cell23_6484160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_6484160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484160 prefixEnd_6484160 := by exact prefixLift 6484160
  have htrace : WordTrace (prefixWord ++ tailWord_6484160) baseStart_6484160 baseEnd_6484160 := by
    simpa [prefixWord, tailWord_6484160, baseEnd_6484160] using wordTrace_append hprefix tailTrace_6484160
  have hstable : (prefixWord ++ tailWord_6484160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484160).length < 2 ^ (prefixWord ++ tailWord_6484160).sum := by decide
  have hdescent : baseEnd_6484160 < baseStart_6484160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484188 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6484188 : Nat := 118140960795 + 6484188 * 2 ^ 59
def prefixEnd_6484188 : Nat := 4983230072969 + 3 ^ 40 * 6484188 * 2
def baseEnd_6484188 : Nat := 1109835032705260606109923

theorem tailTrace_6484188 : CollatzResearch.WordTrace tailWord_6484188 prefixEnd_6484188 1109835032705260606109923 := by
  unfold tailWord_6484188
  simp only [CollatzResearch.WordTrace]
  refine ⟨118248882716450880995002609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157665176955267841326670145 118248882716450880995002609)
  ·
    refine ⟨88686662037338160746251957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118248882716450880995002609 88686662037338160746251957)
    ·
      refine ⟨8314374566000452569961121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88686662037338160746251957 8314374566000452569961121)
      ·
        refine ⟨6235780924500339427470841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8314374566000452569961121 6235780924500339427470841)
        ·
          refine ⟨4676835693375254570603131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6235780924500339427470841 4676835693375254570603131)
          ·
            refine ⟨7015253540062881855904697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676835693375254570603131 7015253540062881855904697)
            ·
              refine ⟨5261440155047161391928523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7015253540062881855904697 5261440155047161391928523)
              ·
                refine ⟨7892160232570742087892785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261440155047161391928523 7892160232570742087892785)
                ·
                  refine ⟨5919120174428056565919589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7892160232570742087892785 5919120174428056565919589)
                  ·
                    refine ⟨1109835032705260606109923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5919120174428056565919589 1109835032705260606109923)
                    ·
                      rfl

theorem cell23_6484188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6484188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484188 prefixEnd_6484188 := by exact prefixLift 6484188
  have htrace : WordTrace (prefixWord ++ tailWord_6484188) baseStart_6484188 baseEnd_6484188 := by
    simpa [prefixWord, tailWord_6484188, baseEnd_6484188] using wordTrace_append hprefix tailTrace_6484188
  have hstable : (prefixWord ++ tailWord_6484188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484188).length < 2 ^ (prefixWord ++ tailWord_6484188).sum := by decide
  have hdescent : baseEnd_6484188 < baseStart_6484188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484330 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 8]
def baseStart_6484330 : Nat := 118140960795 + 6484330 * 2 ^ 59
def prefixEnd_6484330 : Nat := 4983230072969 + 3 ^ 40 * 6484330 * 2
def baseEnd_6484330 : Nat := 369953112485413362528235

theorem tailTrace_6484330 : CollatzResearch.WordTrace tailWord_6484330 prefixEnd_6484330 369953112485413362528235 := by
  unfold tailWord_6484330
  simp only [CollatzResearch.WordTrace]
  refine ⟨59125736149596830060418611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157668629732258213494449629 59125736149596830060418611)
  ·
    refine ⟨88688604224395245090627917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59125736149596830060418611 88688604224395245090627917)
    ·
      refine ⟨33258226584148216908985469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88688604224395245090627917 33258226584148216908985469)
      ·
        refine ⟨12471834969055581340869551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33258226584148216908985469 12471834969055581340869551)
        ·
          refine ⟨18707752453583372011304327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471834969055581340869551 18707752453583372011304327)
          ·
            refine ⟨28061628680375058016956491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18707752453583372011304327 28061628680375058016956491)
            ·
              refine ⟨42092443020562587025434737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28061628680375058016956491 42092443020562587025434737)
              ·
                refine ⟨31569332265421940269076053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42092443020562587025434737 31569332265421940269076053)
                ·
                  refine ⟨369953112485413362528235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31569332265421940269076053 369953112485413362528235)
                  ·
                    rfl

theorem cell23_6484330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_6484330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484330 prefixEnd_6484330 := by exact prefixLift 6484330
  have htrace : WordTrace (prefixWord ++ tailWord_6484330) baseStart_6484330 baseEnd_6484330 := by
    simpa [prefixWord, tailWord_6484330, baseEnd_6484330] using wordTrace_append hprefix tailTrace_6484330
  have hstable : (prefixWord ++ tailWord_6484330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484330).length < 2 ^ (prefixWord ++ tailWord_6484330).sum := by decide
  have hdescent : baseEnd_6484330 < baseStart_6484330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484360 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 3, 5]
def baseStart_6484360 : Nat := 118140960795 + 6484360 * 2 ^ 59
def prefixEnd_6484360 : Nat := 4983230072969 + 3 ^ 40 * 6484360 * 2
def baseEnd_6484360 : Nat := 1109864472262785048459659

theorem tailTrace_6484360 : CollatzResearch.WordTrace tailWord_6484360 prefixEnd_6484360 1109864472262785048459659 := by
  unfold tailWord_6484360
  simp only [CollatzResearch.WordTrace]
  refine ⟨118252019394139317682633267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157669359192185756910177689 118252019394139317682633267)
  ·
    refine ⟨177378029091208976523949901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118252019394139317682633267 177378029091208976523949901)
    ·
      refine ⟨66516760909203366196481213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177378029091208976523949901 66516760909203366196481213)
      ·
        refine ⟨24943785340951262323680455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66516760909203366196481213 24943785340951262323680455)
        ·
          refine ⟨37415678011426893485520683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24943785340951262323680455 37415678011426893485520683)
          ·
            refine ⟨56123517017140340228281025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37415678011426893485520683 56123517017140340228281025)
            ·
              refine ⟨42092637762855255171210769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56123517017140340228281025 42092637762855255171210769)
              ·
                refine ⟨31569478322141441378408077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42092637762855255171210769 31569478322141441378408077)
                ·
                  refine ⟨11838554370803040516903029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31569478322141441378408077 11838554370803040516903029)
                  ·
                    refine ⟨1109864472262785048459659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11838554370803040516903029 1109864472262785048459659)
                    ·
                      rfl

theorem cell23_6484360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_6484360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484360 prefixEnd_6484360 := by exact prefixLift 6484360
  have htrace : WordTrace (prefixWord ++ tailWord_6484360) baseStart_6484360 baseEnd_6484360 := by
    simpa [prefixWord, tailWord_6484360, baseEnd_6484360] using wordTrace_append hprefix tailTrace_6484360
  have hstable : (prefixWord ++ tailWord_6484360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484360).length < 2 ^ (prefixWord ++ tailWord_6484360).sum := by decide
  have hdescent : baseEnd_6484360 < baseStart_6484360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484384 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 2, 3, 2]
def baseStart_6484384 : Nat := 118140960795 + 6484384 * 2 ^ 59
def prefixEnd_6484384 : Nat := 4983230072969 + 3 ^ 40 * 6484384 * 2
def baseEnd_6484384 : Nat := 3329605740324063051478867

theorem tailTrace_6484384 : CollatzResearch.WordTrace tailWord_6484384 prefixEnd_6484384 3329605740324063051478867 := by
  unfold tailWord_6484384
  simp only [CollatzResearch.WordTrace]
  refine ⟨118252457070095843732070103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157669942760127791642760137 118252457070095843732070103)
  ·
    refine ⟨177378685605143765598105155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118252457070095843732070103 177378685605143765598105155)
    ·
      refine ⟨266068028407715648397157733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177378685605143765598105155 266068028407715648397157733)
      ·
        refine ⟨49887755326446684074467075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266068028407715648397157733 49887755326446684074467075)
        ·
          refine ⟨74831632989670026111700613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49887755326446684074467075 74831632989670026111700613)
          ·
            refine ⟨14030931185563129895943865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74831632989670026111700613 14030931185563129895943865)
            ·
              refine ⟨10523198389172347421957899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14030931185563129895943865 10523198389172347421957899)
              ·
                refine ⟨15784797583758521132936849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10523198389172347421957899 15784797583758521132936849)
                ·
                  refine ⟨11838598187818890849702637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15784797583758521132936849 11838598187818890849702637)
                  ·
                    refine ⟨4439474320432084068638489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11838598187818890849702637 4439474320432084068638489)
                    ·
                      refine ⟨3329605740324063051478867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439474320432084068638489 3329605740324063051478867)
                      ·
                        rfl

theorem cell23_6484384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_6484384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484384 prefixEnd_6484384 := by exact prefixLift 6484384
  have htrace : WordTrace (prefixWord ++ tailWord_6484384) baseStart_6484384 baseEnd_6484384 := by
    simpa [prefixWord, tailWord_6484384, baseEnd_6484384] using wordTrace_append hprefix tailTrace_6484384
  have hstable : (prefixWord ++ tailWord_6484384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484384).length < 2 ^ (prefixWord ++ tailWord_6484384).sum := by decide
  have hdescent : baseEnd_6484384 < baseStart_6484384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484407 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 2, 4]
def baseStart_6484407 : Nat := 118140960795 + 6484407 * 2 ^ 59
def prefixEnd_6484407 : Nat := 4983230072969 + 3 ^ 40 * 6484407 * 2
def baseEnd_6484407 : Nat := 1109872516793038820497087

theorem tailTrace_6484407 : CollatzResearch.WordTrace tailWord_6484407 prefixEnd_6484407 1109872516793038820497087 := by
  unfold tailWord_6484407
  simp only [CollatzResearch.WordTrace]
  refine ⟨236505753019108362392227475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157670502012738908261484983 236505753019108362392227475)
  ·
    refine ⟨354758629528662543588341213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236505753019108362392227475 354758629528662543588341213)
    ·
      refine ⟨133034486073248453845627955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354758629528662543588341213 133034486073248453845627955)
      ·
        refine ⟨199551729109872680768441933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133034486073248453845627955 199551729109872680768441933)
        ·
          refine ⟨74831898416202255288165725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199551729109872680768441933 74831898416202255288165725)
          ·
            refine ⟨28061961906075845733062147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74831898416202255288165725 28061961906075845733062147)
            ·
              refine ⟨42092942859113768599593221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28061961906075845733062147 42092942859113768599593221)
              ·
                refine ⟨7892426786083831612423729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42092942859113768599593221 7892426786083831612423729)
                ·
                  refine ⟨5919320089562873709317797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7892426786083831612423729 5919320089562873709317797)
                  ·
                    refine ⟨1109872516793038820497087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5919320089562873709317797 1109872516793038820497087)
                    ·
                      rfl

theorem cell23_6484407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_6484407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484407 prefixEnd_6484407 := by exact prefixLift 6484407
  have htrace : WordTrace (prefixWord ++ tailWord_6484407) baseStart_6484407 baseEnd_6484407 := by
    simpa [prefixWord, tailWord_6484407, baseEnd_6484407] using wordTrace_append hprefix tailTrace_6484407
  have hstable : (prefixWord ++ tailWord_6484407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484407).length < 2 ^ (prefixWord ++ tailWord_6484407).sum := by decide
  have hdescent : baseEnd_6484407 < baseStart_6484407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484437 : List Nat := [1, 3, 2, 3, 1, 3, 3, 7]
def baseStart_6484437 : Nat := 118140960795 + 6484437 * 2 ^ 59
def prefixEnd_6484437 : Nat := 4983230072969 + 3 ^ 40 * 6484437 * 2
def baseEnd_6484437 : Nat := 123319739066620420152449

theorem tailTrace_6484437 : CollatzResearch.WordTrace tailWord_6484437 prefixEnd_6484437 123319739066620420152449 := by
  unfold tailWord_6484437
  simp only [CollatzResearch.WordTrace]
  refine ⟨236506847208999677515819565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157671231472666451677213043 236506847208999677515819565)
  ·
    refine ⟨88690067703374879068432337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236506847208999677515819565 88690067703374879068432337)
    ·
      refine ⟨66517550777531159301324253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88690067703374879068432337 66517550777531159301324253)
      ·
        refine ⟨24944081541574184737996595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66517550777531159301324253 24944081541574184737996595)
        ·
          refine ⟨37416122312361277106994893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24944081541574184737996595 37416122312361277106994893)
          ·
            refine ⟨14031045867135478915123085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37416122312361277106994893 14031045867135478915123085)
            ·
              refine ⟨5261642200175804593171157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14031045867135478915123085 5261642200175804593171157)
              ·
                refine ⟨123319739066620420152449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5261642200175804593171157 123319739066620420152449)
                ·
                  rfl

theorem cell23_6484437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 7].length) (baseStart_6484437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484437 prefixEnd_6484437 := by exact prefixLift 6484437
  have htrace : WordTrace (prefixWord ++ tailWord_6484437) baseStart_6484437 baseEnd_6484437 := by
    simpa [prefixWord, tailWord_6484437, baseEnd_6484437] using wordTrace_append hprefix tailTrace_6484437
  have hstable : (prefixWord ++ tailWord_6484437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484437).length < 2 ^ (prefixWord ++ tailWord_6484437).sum := by decide
  have hdescent : baseEnd_6484437 < baseStart_6484437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484447 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 3]
def baseStart_6484447 : Nat := 118140960795 + 6484447 * 2 ^ 59
def prefixEnd_6484447 : Nat := 4983230072969 + 3 ^ 40 * 6484447 * 2
def baseEnd_6484447 : Nat := 3329638089605296304991077

theorem tailTrace_6484447 : CollatzResearch.WordTrace tailWord_6484447 prefixEnd_6484447 3329638089605296304991077 := by
  unfold tailWord_6484447
  simp only [CollatzResearch.WordTrace]
  refine ⟨236507211938963449223683595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157671474625975632815789063 236507211938963449223683595)
  ·
    refine ⟨354760817908445173835525393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236507211938963449223683595 354760817908445173835525393)
    ·
      refine ⟨266070613431333880376644045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354760817908445173835525393 266070613431333880376644045)
      ·
        refine ⟨99776480036750205141241517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266070613431333880376644045 99776480036750205141241517)
        ·
          refine ⟨37416180013781326927965569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99776480036750205141241517 37416180013781326927965569)
          ·
            refine ⟨28062135010335995195974177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37416180013781326927965569 28062135010335995195974177)
            ·
              refine ⟨21046601257751996396980633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28062135010335995195974177 21046601257751996396980633)
              ·
                refine ⟨15784950943313997297735475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21046601257751996396980633 15784950943313997297735475)
                ·
                  refine ⟨23677426414970995946603213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15784950943313997297735475 23677426414970995946603213)
                  ·
                    refine ⟨8879034905614123479976205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23677426414970995946603213 8879034905614123479976205)
                    ·
                      refine ⟨3329638089605296304991077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8879034905614123479976205 3329638089605296304991077)
                      ·
                        rfl

theorem cell23_6484447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_6484447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484447 prefixEnd_6484447 := by exact prefixLift 6484447
  have htrace : WordTrace (prefixWord ++ tailWord_6484447) baseStart_6484447 baseEnd_6484447 := by
    simpa [prefixWord, tailWord_6484447, baseEnd_6484447] using wordTrace_append hprefix tailTrace_6484447
  have hstable : (prefixWord ++ tailWord_6484447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484447).length < 2 ^ (prefixWord ++ tailWord_6484447).sum := by decide
  have hdescent : baseEnd_6484447 < baseStart_6484447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484457 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 5, 3, 2]
def baseStart_6484457 : Nat := 118140960795 + 6484457 * 2 ^ 59
def prefixEnd_6484457 : Nat := 4983230072969 + 3 ^ 40 * 6484457 * 2
def baseEnd_6484457 : Nat := 3329643224411841265866031

theorem tailTrace_6484457 : CollatzResearch.WordTrace tailWord_6484457 prefixEnd_6484457 3329643224411841265866031 := by
  unfold tailWord_6484457
  simp only [CollatzResearch.WordTrace]
  refine ⟨236507576668927220931547625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157671717779284813954365083 236507576668927220931547625)
  ·
    refine ⟨177380682501695415698660719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236507576668927220931547625 177380682501695415698660719)
    ·
      refine ⟨266071023752543123547991079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177380682501695415698660719 266071023752543123547991079)
      ·
        refine ⟨399106535628814685321986619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266071023752543123547991079 399106535628814685321986619)
        ·
          refine ⟨598659803443222027982979929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399106535628814685321986619 598659803443222027982979929)
          ·
            refine ⟨448994852582416520987234947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598659803443222027982979929 448994852582416520987234947)
            ·
              refine ⟨673492278873624781480852421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448994852582416520987234947 673492278873624781480852421)
              ·
                refine ⟨126279802288804646527659829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673492278873624781480852421 126279802288804646527659829)
                ·
                  refine ⟨11838731464575435611968109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126279802288804646527659829 11838731464575435611968109)
                  ·
                    refine ⟨4439524299215788354488041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11838731464575435611968109 4439524299215788354488041)
                    ·
                      refine ⟨3329643224411841265866031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439524299215788354488041 3329643224411841265866031)
                      ·
                        rfl

theorem cell23_6484457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 3, 2].length) (baseStart_6484457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484457 prefixEnd_6484457 := by exact prefixLift 6484457
  have htrace : WordTrace (prefixWord ++ tailWord_6484457) baseStart_6484457 baseEnd_6484457 := by
    simpa [prefixWord, tailWord_6484457, baseEnd_6484457] using wordTrace_append hprefix tailTrace_6484457
  have hstable : (prefixWord ++ tailWord_6484457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484457).length < 2 ^ (prefixWord ++ tailWord_6484457).sum := by decide
  have hdescent : baseEnd_6484457 < baseStart_6484457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484491 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 1, 3, 2]
def baseStart_6484491 : Nat := 118140960795 + 6484491 * 2 ^ 59
def prefixEnd_6484491 : Nat := 4983230072969 + 3 ^ 40 * 6484491 * 2
def baseEnd_6484491 : Nat := 3329660682754094132840875

theorem tailTrace_6484491 : CollatzResearch.WordTrace tailWord_6484491 prefixEnd_6484491 3329660682754094132840875 := by
  unfold tailWord_6484491
  simp only [CollatzResearch.WordTrace]
  refine ⟨236508816750804044738285327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157672544500536029825523551 236508816750804044738285327)
  ·
    refine ⟨354763225126206067107427991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236508816750804044738285327 354763225126206067107427991)
    ·
      refine ⟨532144837689309100661141987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354763225126206067107427991 532144837689309100661141987)
      ·
        refine ⟨798217256533963650991712981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532144837689309100661141987 798217256533963650991712981)
        ·
          refine ⟨18708216950014773070118273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 798217256533963650991712981 18708216950014773070118273)
          ·
            refine ⟨14031162712511079802588705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18708216950014773070118273 14031162712511079802588705)
            ·
              refine ⟨10523372034383309851941529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14031162712511079802588705 10523372034383309851941529)
              ·
                refine ⟨7892529025787482388956147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10523372034383309851941529 7892529025787482388956147)
                ·
                  refine ⟨11838793538681223583434221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7892529025787482388956147 11838793538681223583434221)
                  ·
                    refine ⟨4439547577005458843787833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11838793538681223583434221 4439547577005458843787833)
                    ·
                      refine ⟨3329660682754094132840875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439547577005458843787833 3329660682754094132840875)
                      ·
                        rfl

theorem cell23_6484491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 3, 2].length) (baseStart_6484491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484491 prefixEnd_6484491 := by exact prefixLift 6484491
  have htrace : WordTrace (prefixWord ++ tailWord_6484491) baseStart_6484491 baseEnd_6484491 := by
    simpa [prefixWord, tailWord_6484491, baseEnd_6484491] using wordTrace_append hprefix tailTrace_6484491
  have hstable : (prefixWord ++ tailWord_6484491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484491).length < 2 ^ (prefixWord ++ tailWord_6484491).sum := by decide
  have hdescent : baseEnd_6484491 < baseStart_6484491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484532 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6484532 : Nat := 118140960795 + 6484532 * 2 ^ 59
def prefixEnd_6484532 : Nat := 4983230072969 + 3 ^ 40 * 6484532 * 2
def baseEnd_6484532 : Nat := 3329681735460928472428187

theorem tailTrace_6484532 : CollatzResearch.WordTrace tailWord_6484532 prefixEnd_6484532 3329681735460928472428187 := by
  unfold tailWord_6484532
  simp only [CollatzResearch.WordTrace]
  refine ⟨118255156071827754370263925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157673541429103672493685233 118255156071827754370263925)
  ·
    refine ⟨11086420881733851972212243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118255156071827754370263925 11086420881733851972212243)
    ·
      refine ⟨16629631322600777958318365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11086420881733851972212243 16629631322600777958318365)
      ·
        refine ⟨6236111745975291734369387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16629631322600777958318365 6236111745975291734369387)
        ·
          refine ⟨9354167618962937601554081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236111745975291734369387 9354167618962937601554081)
          ·
            refine ⟨7015625714222203201165561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9354167618962937601554081 7015625714222203201165561)
            ·
              refine ⟨5261719285666652400874171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7015625714222203201165561 5261719285666652400874171)
              ·
                refine ⟨7892578928499978601311257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261719285666652400874171 7892578928499978601311257)
                ·
                  refine ⟨5919434196374983950983443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7892578928499978601311257 5919434196374983950983443)
                  ·
                    refine ⟨8879151294562475926475165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5919434196374983950983443 8879151294562475926475165)
                    ·
                      refine ⟨3329681735460928472428187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8879151294562475926475165 3329681735460928472428187)
                      ·
                        rfl

theorem cell23_6484532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6484532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484532 prefixEnd_6484532 := by exact prefixLift 6484532
  have htrace : WordTrace (prefixWord ++ tailWord_6484532) baseStart_6484532 baseEnd_6484532 := by
    simpa [prefixWord, tailWord_6484532, baseEnd_6484532] using wordTrace_append hprefix tailTrace_6484532
  have hstable : (prefixWord ++ tailWord_6484532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484532).length < 2 ^ (prefixWord ++ tailWord_6484532).sum := by decide
  have hdescent : baseEnd_6484532 < baseStart_6484532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484537 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6484537 : Nat := 118140960795 + 6484537 * 2 ^ 59
def prefixEnd_6484537 : Nat := 4983230072969 + 3 ^ 40 * 6484537 * 2
def baseEnd_6484537 : Nat := 3329684302864200952865663

theorem tailTrace_6484537 : CollatzResearch.WordTrace tailWord_6484537 prefixEnd_6484537 3329684302864200952865663 := by
  unfold tailWord_6484537
  simp only [CollatzResearch.WordTrace]
  refine ⟨236510494508637394594459865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157673663005758263062973243 236510494508637394594459865)
  ·
    refine ⟨177382870881478045945844899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236510494508637394594459865 177382870881478045945844899)
    ·
      refine ⟨266074306322217068918767349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177382870881478045945844899 266074306322217068918767349)
      ·
        refine ⟨24944466217707850211134439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266074306322217068918767349 24944466217707850211134439)
        ·
          refine ⟨37416699326561775316701659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24944466217707850211134439 37416699326561775316701659)
          ·
            refine ⟨56125048989842662975052489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37416699326561775316701659 56125048989842662975052489)
            ·
              refine ⟨42093786742381997231289367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56125048989842662975052489 42093786742381997231289367)
              ·
                refine ⟨63140680113572995846934051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42093786742381997231289367 63140680113572995846934051)
                ·
                  refine ⟨94711020170359493770401077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63140680113572995846934051 94711020170359493770401077)
                  ·
                    refine ⟨8879158140971202540975101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94711020170359493770401077 8879158140971202540975101)
                    ·
                      refine ⟨3329684302864200952865663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8879158140971202540975101 3329684302864200952865663)
                      ·
                        rfl

theorem cell23_6484537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6484537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484537 prefixEnd_6484537 := by exact prefixLift 6484537
  have htrace : WordTrace (prefixWord ++ tailWord_6484537) baseStart_6484537 baseEnd_6484537 := by
    simpa [prefixWord, tailWord_6484537, baseEnd_6484537] using wordTrace_append hprefix tailTrace_6484537
  have hstable : (prefixWord ++ tailWord_6484537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484537).length < 2 ^ (prefixWord ++ tailWord_6484537).sum := by decide
  have hdescent : baseEnd_6484537 < baseStart_6484537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484538 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2]
def baseStart_6484538 : Nat := 118140960795 + 6484538 * 2 ^ 59
def prefixEnd_6484538 : Nat := 4983230072969 + 3 ^ 40 * 6484538 * 2
def baseEnd_6484538 : Nat := 3329684816344855448953159

theorem tailTrace_6484538 : CollatzResearch.WordTrace tailWord_6484538 prefixEnd_6484538 3329684816344855448953159 := by
  unfold tailWord_6484538
  simp only [CollatzResearch.WordTrace]
  refine ⟨59127632745408442941311567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157673687321089181176830845 59127632745408442941311567)
  ·
    refine ⟨88691449118112664411967351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59127632745408442941311567 88691449118112664411967351)
    ·
      refine ⟨133037173677168996617951027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88691449118112664411967351 133037173677168996617951027)
      ·
        refine ⟨199555760515753494926926541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133037173677168996617951027 199555760515753494926926541)
        ·
          refine ⟨74833410193407560597597453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199555760515753494926926541 74833410193407560597597453)
          ·
            refine ⟨28062528822527835224099045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74833410193407560597597453 28062528822527835224099045)
            ·
              refine ⟨5261724154223969104518571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28062528822527835224099045 5261724154223969104518571)
              ·
                refine ⟨7892586231335953656777857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261724154223969104518571 7892586231335953656777857)
                ·
                  refine ⟨5919439673501965242583393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7892586231335953656777857 5919439673501965242583393)
                  ·
                    refine ⟨4439579755126473931937545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919439673501965242583393 4439579755126473931937545)
                    ·
                      refine ⟨3329684816344855448953159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439579755126473931937545 3329684816344855448953159)
                      ·
                        rfl

theorem cell23_6484538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_6484538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484538 prefixEnd_6484538 := by exact prefixLift 6484538
  have htrace : WordTrace (prefixWord ++ tailWord_6484538) baseStart_6484538 baseEnd_6484538 := by
    simpa [prefixWord, tailWord_6484538, baseEnd_6484538] using wordTrace_append hprefix tailTrace_6484538
  have hstable : (prefixWord ++ tailWord_6484538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484538).length < 2 ^ (prefixWord ++ tailWord_6484538).sum := by decide
  have hdescent : baseEnd_6484538 < baseStart_6484538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484542 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6484542 : Nat := 118140960795 + 6484542 * 2 ^ 59
def prefixEnd_6484542 : Nat := 4983230072969 + 3 ^ 40 * 6484542 * 2
def baseEnd_6484542 : Nat := 3329686870267473433303141

theorem tailTrace_6484542 : CollatzResearch.WordTrace tailWord_6484542 prefixEnd_6484542 3329686870267473433303141 := by
  unfold tailWord_6484542
  simp only [CollatzResearch.WordTrace]
  refine ⟨29563834609202410056048985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157673784582412853632261253 29563834609202410056048985)
  ·
    refine ⟨22172875956901807542036739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29563834609202410056048985 22172875956901807542036739)
    ·
      refine ⟨33259313935352711313055109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22172875956901807542036739 33259313935352711313055109)
      ·
        refine ⟨6236121362878633371197833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33259313935352711313055109 6236121362878633371197833)
        ·
          refine ⟨4677091022158975028398375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6236121362878633371197833 4677091022158975028398375)
          ·
            refine ⟨7015636533238462542597563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4677091022158975028398375 7015636533238462542597563)
            ·
              refine ⟨10523454799857693813896345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015636533238462542597563 10523454799857693813896345)
              ·
                refine ⟨7892591099893270360422259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10523454799857693813896345 7892591099893270360422259)
                ·
                  refine ⟨11838886649839905540633389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7892591099893270360422259 11838886649839905540633389)
                  ·
                    refine ⟨4439582493689964577737521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11838886649839905540633389 4439582493689964577737521)
                    ·
                      refine ⟨3329686870267473433303141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439582493689964577737521 3329686870267473433303141)
                      ·
                        rfl

theorem cell23_6484542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6484542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484542 prefixEnd_6484542 := by exact prefixLift 6484542
  have htrace : WordTrace (prefixWord ++ tailWord_6484542) baseStart_6484542 baseEnd_6484542 := by
    simpa [prefixWord, tailWord_6484542, baseEnd_6484542] using wordTrace_append hprefix tailTrace_6484542
  have hstable : (prefixWord ++ tailWord_6484542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484542).length < 2 ^ (prefixWord ++ tailWord_6484542).sum := by decide
  have hdescent : baseEnd_6484542 < baseStart_6484542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484578 : List Nat := [3, 3, 2, 3, 1, 1, 1, 4, 5]
def baseStart_6484578 : Nat := 118140960795 + 6484578 * 2 ^ 59
def prefixEnd_6484578 : Nat := 4983230072969 + 3 ^ 40 * 6484578 * 2
def baseEnd_6484578 : Nat := 369967261730115032494775

theorem tailTrace_6484578 : CollatzResearch.WordTrace tailWord_6484578 prefixEnd_6484578 369967261730115032494775 := by
  unfold tailWord_6484578
  simp only [CollatzResearch.WordTrace]
  refine ⟨59127997475372214649175597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157674659934325905731134925 59127997475372214649175597)
  ·
    refine ⟨22172999053264580493440849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59127997475372214649175597 22172999053264580493440849)
    ·
      refine ⟨16629749289948435370080637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22172999053264580493440849 16629749289948435370080637)
      ·
        refine ⟨6236155983730663263780239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16629749289948435370080637 6236155983730663263780239)
        ·
          refine ⟨9354233975595994895670359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236155983730663263780239 9354233975595994895670359)
          ·
            refine ⟨14031350963393992343505539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9354233975595994895670359 14031350963393992343505539)
            ·
              refine ⟨21047026445090988515258309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14031350963393992343505539 21047026445090988515258309)
              ·
                refine ⟨3946317458454560346610933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21047026445090988515258309 3946317458454560346610933)
                ·
                  refine ⟨369967261730115032494775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3946317458454560346610933 369967261730115032494775)
                  ·
                    rfl

theorem cell23_6484578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_6484578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484578 prefixEnd_6484578 := by exact prefixLift 6484578
  have htrace : WordTrace (prefixWord ++ tailWord_6484578) baseStart_6484578 baseEnd_6484578 := by
    simpa [prefixWord, tailWord_6484578, baseEnd_6484578] using wordTrace_append hprefix tailTrace_6484578
  have hstable : (prefixWord ++ tailWord_6484578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484578).length < 2 ^ (prefixWord ++ tailWord_6484578).sum := by decide
  have hdescent : baseEnd_6484578 < baseStart_6484578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484637 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_6484637 : Nat := 118140960795 + 6484637 * 2 ^ 59
def prefixEnd_6484637 : Nat := 4983230072969 + 3 ^ 40 * 6484637 * 2
def baseEnd_6484637 : Nat := 3329735650929650561615203

theorem tailTrace_6484637 : CollatzResearch.WordTrace tailWord_6484637 prefixEnd_6484637 3329735650929650561615203 := by
  unfold tailWord_6484637
  simp only [CollatzResearch.WordTrace]
  refine ⟨236514141808275111673100165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157676094538850074448733443 236514141808275111673100165)
  ·
    refine ⟨44346401589051583438706281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236514141808275111673100165 44346401589051583438706281)
    ·
      refine ⟨33259801191788687579029711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44346401589051583438706281 33259801191788687579029711)
      ·
        refine ⟨49889701787683031368544567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33259801191788687579029711 49889701787683031368544567)
        ·
          refine ⟨74834552681524547052816851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49889701787683031368544567 74834552681524547052816851)
          ·
            refine ⟨112251829022286820579225277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74834552681524547052816851 112251829022286820579225277)
            ·
              refine ⟨42094435883357557717209479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112251829022286820579225277 42094435883357557717209479)
              ·
                refine ⟨63141653825036336575814219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42094435883357557717209479 63141653825036336575814219)
                ·
                  refine ⟨94712480737554504863721329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63141653825036336575814219 94712480737554504863721329)
                  ·
                    refine ⟨71034360553165878647790997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94712480737554504863721329 71034360553165878647790997)
                    ·
                      refine ⟨3329735650929650561615203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71034360553165878647790997 3329735650929650561615203)
                      ·
                        rfl

theorem cell23_6484637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_6484637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484637 prefixEnd_6484637 := by exact prefixLift 6484637
  have htrace : WordTrace (prefixWord ++ tailWord_6484637) baseStart_6484637 baseEnd_6484637 := by
    simpa [prefixWord, tailWord_6484637, baseEnd_6484637] using wordTrace_append hprefix tailTrace_6484637
  have hstable : (prefixWord ++ tailWord_6484637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484637).length < 2 ^ (prefixWord ++ tailWord_6484637).sum := by decide
  have hdescent : baseEnd_6484637 < baseStart_6484637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484638 : List Nat := [4, 3, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_6484638 : Nat := 118140960795 + 6484638 * 2 ^ 59
def prefixEnd_6484638 : Nat := 4983230072969 + 3 ^ 40 * 6484638 * 2
def baseEnd_6484638 : Nat := 1109912054803435019234233

theorem tailTrace_6484638 : CollatzResearch.WordTrace tailWord_6484638 prefixEnd_6484638 1109912054803435019234233 := by
  unfold tailWord_6484638
  simp only [CollatzResearch.WordTrace]
  refine ⟨29564272285158936105485821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157676118854180992562591045 29564272285158936105485821)
  ·
    refine ⟨11086602106934601039557183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29564272285158936105485821 11086602106934601039557183)
    ·
      refine ⟨16629903160401901559335775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11086602106934601039557183 16629903160401901559335775)
      ·
        refine ⟨24944854740602852339003663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16629903160401901559335775 24944854740602852339003663)
        ·
          refine ⟨37417282110904278508505495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24944854740602852339003663 37417282110904278508505495)
          ·
            refine ⟨56125923166356417762758243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37417282110904278508505495 56125923166356417762758243)
            ·
              refine ⟨84188884749534626644137365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56125923166356417762758243 84188884749534626644137365)
              ·
                refine ⟨3946353972634435623943939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84188884749534626644137365 3946353972634435623943939)
                ·
                  refine ⟨5919530958951653435915909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946353972634435623943939 5919530958951653435915909)
                  ·
                    refine ⟨1109912054803435019234233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5919530958951653435915909 1109912054803435019234233)
                    ·
                      rfl

theorem cell23_6484638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_6484638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484638 prefixEnd_6484638 := by exact prefixLift 6484638
  have htrace : WordTrace (prefixWord ++ tailWord_6484638) baseStart_6484638 baseEnd_6484638 := by
    simpa [prefixWord, tailWord_6484638, baseEnd_6484638] using wordTrace_append hprefix tailTrace_6484638
  have hstable : (prefixWord ++ tailWord_6484638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484638).length < 2 ^ (prefixWord ++ tailWord_6484638).sum := by decide
  have hdescent : baseEnd_6484638 < baseStart_6484638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484695 : List Nat := [1, 1, 3, 2, 1, 5, 3, 2, 1, 1, 3]
def baseStart_6484695 : Nat := 118140960795 + 6484695 * 2 ^ 59
def prefixEnd_6484695 : Nat := 4983230072969 + 3 ^ 40 * 6484695 * 2
def baseEnd_6484695 : Nat := 3329765432807611334689937

theorem tailTrace_6484695 : CollatzResearch.WordTrace tailWord_6484695 prefixEnd_6484695 3329765432807611334689937 := by
  unfold tailWord_6484695
  simp only [CollatzResearch.WordTrace]
  refine ⟨236516257242064987578711539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157677504828043325052474359 236516257242064987578711539)
  ·
    refine ⟨354774385863097481368067309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236516257242064987578711539 354774385863097481368067309)
    ·
      refine ⟨133040394698661555513025241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354774385863097481368067309 133040394698661555513025241)
      ·
        refine ⟨99780296023996166634768931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133040394698661555513025241 99780296023996166634768931)
        ·
          refine ⟨149670444035994249952153397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99780296023996166634768931 149670444035994249952153397)
          ·
            refine ⟨14031604128374460933014381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149670444035994249952153397 14031604128374460933014381)
            ·
              refine ⟨5261851548140422849880393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14031604128374460933014381 5261851548140422849880393)
              ·
                refine ⟨3946388661105317137410295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5261851548140422849880393 3946388661105317137410295)
                ·
                  refine ⟨5919582991657975706115443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946388661105317137410295 5919582991657975706115443)
                  ·
                    refine ⟨8879374487486963559173165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5919582991657975706115443 8879374487486963559173165)
                    ·
                      refine ⟨3329765432807611334689937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8879374487486963559173165 3329765432807611334689937)
                      ·
                        rfl

theorem cell23_6484695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_6484695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484695 prefixEnd_6484695 := by exact prefixLift 6484695
  have htrace : WordTrace (prefixWord ++ tailWord_6484695) baseStart_6484695 baseEnd_6484695 := by
    simpa [prefixWord, tailWord_6484695, baseEnd_6484695] using wordTrace_append hprefix tailTrace_6484695
  have hstable : (prefixWord ++ tailWord_6484695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484695).length < 2 ^ (prefixWord ++ tailWord_6484695).sum := by decide
  have hdescent : baseEnd_6484695 < baseStart_6484695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484697 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_6484697 : Nat := 118140960795 + 6484697 * 2 ^ 59
def prefixEnd_6484697 : Nat := 4983230072969 + 3 ^ 40 * 6484697 * 2
def baseEnd_6484697 : Nat := 3329766459768920326864927

theorem tailTrace_6484697 : CollatzResearch.WordTrace tailWord_6484697 prefixEnd_6484697 3329766459768920326864927 := by
  unfold tailWord_6484697
  simp only [CollatzResearch.WordTrace]
  refine ⟨236516330188057741920284345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157677553458705161280189563 236516330188057741920284345)
  ·
    refine ⟨177387247641043306440213259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236516330188057741920284345 177387247641043306440213259)
    ·
      refine ⟨266080871461564959660319889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177387247641043306440213259 266080871461564959660319889)
      ·
        refine ⟨199560653596173719745239917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266080871461564959660319889 199560653596173719745239917)
        ·
          refine ⟨74835245098565144904464969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199560653596173719745239917 74835245098565144904464969)
          ·
            refine ⟨56126433823923858678348727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74835245098565144904464969 56126433823923858678348727)
            ·
              refine ⟨84189650735885788017523091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56126433823923858678348727 84189650735885788017523091)
              ·
                refine ⟨126284476103828682026284637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84189650735885788017523091 126284476103828682026284637)
                ·
                  refine ⟨47356678538935755759856739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126284476103828682026284637 47356678538935755759856739)
                  ·
                    refine ⟨71035017808403633639785109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47356678538935755759856739 71035017808403633639785109)
                    ·
                      refine ⟨3329766459768920326864927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71035017808403633639785109 3329766459768920326864927)
                      ·
                        rfl

theorem cell23_6484697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_6484697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484697 prefixEnd_6484697 := by exact prefixLift 6484697
  have htrace : WordTrace (prefixWord ++ tailWord_6484697) baseStart_6484697 baseEnd_6484697 := by
    simpa [prefixWord, tailWord_6484697, baseEnd_6484697] using wordTrace_append hprefix tailTrace_6484697
  have hstable : (prefixWord ++ tailWord_6484697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484697).length < 2 ^ (prefixWord ++ tailWord_6484697).sum := by decide
  have hdescent : baseEnd_6484697 < baseStart_6484697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484704 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3]
def baseStart_6484704 : Nat := 118140960795 + 6484704 * 2 ^ 59
def prefixEnd_6484704 : Nat := 4983230072969 + 3 ^ 40 * 6484704 * 2
def baseEnd_6484704 : Nat := 3329770054133501799477395

theorem tailTrace_6484704 : CollatzResearch.WordTrace tailWord_6484704 prefixEnd_6484704 3329770054133501799477395 := by
  unfold tailWord_6484704
  simp only [CollatzResearch.WordTrace]
  refine ⟨118258292749516191057894583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157677723666021588077192777 118258292749516191057894583)
  ·
    refine ⟨177387439124274286586841875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118258292749516191057894583 177387439124274286586841875)
    ·
      refine ⟨266081158686411429880262813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177387439124274286586841875 266081158686411429880262813)
      ·
        refine ⟨99780434507404286205098555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266081158686411429880262813 99780434507404286205098555)
        ·
          refine ⟨149670651761106429307647833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99780434507404286205098555 149670651761106429307647833)
          ·
            refine ⟨112252988820829821980735875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149670651761106429307647833 112252988820829821980735875)
            ·
              refine ⟨168379483231244732971103813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112252988820829821980735875 168379483231244732971103813)
              ·
                refine ⟨31571153105858387432081965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168379483231244732971103813 31571153105858387432081965)
                ·
                  refine ⟨11839182414696895287030737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31571153105858387432081965 11839182414696895287030737)
                  ·
                    refine ⟨8879386811022671465273053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11839182414696895287030737 8879386811022671465273053)
                    ·
                      refine ⟨3329770054133501799477395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8879386811022671465273053 3329770054133501799477395)
                      ·
                        rfl

theorem cell23_6484704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_6484704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484704 prefixEnd_6484704 := by exact prefixLift 6484704
  have htrace : WordTrace (prefixWord ++ tailWord_6484704) baseStart_6484704 baseEnd_6484704 := by
    simpa [prefixWord, tailWord_6484704, baseEnd_6484704] using wordTrace_append hprefix tailTrace_6484704
  have hstable : (prefixWord ++ tailWord_6484704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484704).length < 2 ^ (prefixWord ++ tailWord_6484704).sum := by decide
  have hdescent : baseEnd_6484704 < baseStart_6484704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484714 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_6484714 : Nat := 118140960795 + 6484714 * 2 ^ 59
def prefixEnd_6484714 : Nat := 4983230072969 + 3 ^ 40 * 6484714 * 2
def baseEnd_6484714 : Nat := 3329775188940046760352349

theorem tailTrace_6484714 : CollatzResearch.WordTrace tailWord_6484714 prefixEnd_6484714 3329775188940046760352349 := by
  unfold tailWord_6484714
  simp only [CollatzResearch.WordTrace]
  refine ⟨59129237557249038455913299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157677966819330769215768797 59129237557249038455913299)
  ·
    refine ⟨88693856335873557683869949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59129237557249038455913299 88693856335873557683869949)
    ·
      refine ⟨33260196125952584131451231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88693856335873557683869949 33260196125952584131451231)
      ·
        refine ⟨49890294188928876197176847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33260196125952584131451231 49890294188928876197176847)
        ·
          refine ⟨74835441283393314295765271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49890294188928876197176847 74835441283393314295765271)
          ·
            refine ⟨112253161925089971443647907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74835441283393314295765271 112253161925089971443647907)
            ·
              refine ⟨168379742887634957165471861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112253161925089971443647907 168379742887634957165471861)
              ·
                refine ⟨15785600895715777234262987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168379742887634957165471861 15785600895715777234262987)
                ·
                  refine ⟨23678401343573665851394481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15785600895715777234262987 23678401343573665851394481)
                  ·
                    refine ⟨17758801007680249388545861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23678401343573665851394481 17758801007680249388545861)
                    ·
                      refine ⟨3329775188940046760352349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17758801007680249388545861 3329775188940046760352349)
                      ·
                        rfl

theorem cell23_6484714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_6484714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484714 prefixEnd_6484714 := by exact prefixLift 6484714
  have htrace : WordTrace (prefixWord ++ tailWord_6484714) baseStart_6484714 baseEnd_6484714 := by
    simpa [prefixWord, tailWord_6484714, baseEnd_6484714] using wordTrace_append hprefix tailTrace_6484714
  have hstable : (prefixWord ++ tailWord_6484714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484714).length < 2 ^ (prefixWord ++ tailWord_6484714).sum := by decide
  have hdescent : baseEnd_6484714 < baseStart_6484714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484718 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_6484718 : Nat := 118140960795 + 6484718 * 2 ^ 59
def prefixEnd_6484718 : Nat := 4983230072969 + 3 ^ 40 * 6484718 * 2
def baseEnd_6484718 : Nat := 3329777242862664744702331

theorem tailTrace_6484718 : CollatzResearch.WordTrace tailWord_6484718 prefixEnd_6484718 3329777242862664744702331 := by
  unfold tailWord_6484718
  simp only [CollatzResearch.WordTrace]
  refine ⟨29564637015122707813349851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157678064080654441671199205 29564637015122707813349851)
  ·
    refine ⟨44346955522684061720024777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29564637015122707813349851 44346955522684061720024777)
    ·
      refine ⟨33260216642013046290018583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44346955522684061720024777 33260216642013046290018583)
      ·
        refine ⟨49890324963019569435027875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33260216642013046290018583 49890324963019569435027875)
        ·
          refine ⟨74835487444529354152541813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49890324963019569435027875 74835487444529354152541813)
          ·
            refine ⟨7015826947924626951800795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74835487444529354152541813 7015826947924626951800795)
            ·
              refine ⟨10523740421886940427701193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015826947924626951800795 10523740421886940427701193)
              ·
                refine ⟨7892805316415205320775895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10523740421886940427701193 7892805316415205320775895)
                ·
                  refine ⟨11839207974622807981163843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7892805316415205320775895 11839207974622807981163843)
                  ·
                    refine ⟨17758811961934211971745765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11839207974622807981163843 17758811961934211971745765)
                    ·
                      refine ⟨3329777242862664744702331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17758811961934211971745765 3329777242862664744702331)
                      ·
                        rfl

theorem cell23_6484718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_6484718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484718 prefixEnd_6484718 := by exact prefixLift 6484718
  have htrace : WordTrace (prefixWord ++ tailWord_6484718) baseStart_6484718 baseEnd_6484718 := by
    simpa [prefixWord, tailWord_6484718, baseEnd_6484718] using wordTrace_append hprefix tailTrace_6484718
  have hstable : (prefixWord ++ tailWord_6484718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484718).length < 2 ^ (prefixWord ++ tailWord_6484718).sum := by decide
  have hdescent : baseEnd_6484718 < baseStart_6484718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484738 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_6484738 : Nat := 118140960795 + 6484738 * 2 ^ 59
def prefixEnd_6484738 : Nat := 4983230072969 + 3 ^ 40 * 6484738 * 2
def baseEnd_6484738 : Nat := 3329787512475754666452239

theorem tailTrace_6484738 : CollatzResearch.WordTrace tailWord_6484738 prefixEnd_6484738 3329787512475754666452239 := by
  unfold tailWord_6484738
  simp only [CollatzResearch.WordTrace]
  refine ⟨59129456395227301480631717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157678550387272803948351245 59129456395227301480631717)
  ·
    refine ⟨11086773074105119027618447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59129456395227301480631717 11086773074105119027618447)
    ·
      refine ⟨16630159611157678541427671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11086773074105119027618447 16630159611157678541427671)
      ·
        refine ⟨24945239416736517812141507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16630159611157678541427671 24945239416736517812141507)
        ·
          refine ⟨37417859125104776718212261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24945239416736517812141507 37417859125104776718212261)
          ·
            refine ⟨7015848585957145634664799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37417859125104776718212261 7015848585957145634664799)
            ·
              refine ⟨10523772878935718451997199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015848585957145634664799 10523772878935718451997199)
              ·
                refine ⟨15785659318403577677995799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10523772878935718451997199 15785659318403577677995799)
                ·
                  refine ⟨23678488977605366516993699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15785659318403577677995799 23678488977605366516993699)
                  ·
                    refine ⟨35517733466408049775490549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23678488977605366516993699 35517733466408049775490549)
                    ·
                      refine ⟨3329787512475754666452239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35517733466408049775490549 3329787512475754666452239)
                      ·
                        rfl

theorem cell23_6484738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_6484738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484738 prefixEnd_6484738 := by exact prefixLift 6484738
  have htrace : WordTrace (prefixWord ++ tailWord_6484738) baseStart_6484738 baseEnd_6484738 := by
    simpa [prefixWord, tailWord_6484738, baseEnd_6484738] using wordTrace_append hprefix tailTrace_6484738
  have hstable : (prefixWord ++ tailWord_6484738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484738).length < 2 ^ (prefixWord ++ tailWord_6484738).sum := by decide
  have hdescent : baseEnd_6484738 < baseStart_6484738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484768 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6484768 : Nat := 118140960795 + 6484768 * 2 ^ 59
def prefixEnd_6484768 : Nat := 4983230072969 + 3 ^ 40 * 6484768 * 2
def baseEnd_6484768 : Nat := 3329802916895389549077101

theorem tailTrace_6484768 : CollatzResearch.WordTrace tailWord_6484768 prefixEnd_6484768 3329802916895389549077101 := by
  unfold tailWord_6484768
  simp only [CollatzResearch.WordTrace]
  refine ⟨118259459885400260523059479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157679279847200347364079305 118259459885400260523059479)
  ·
    refine ⟨177389189828100390784589219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118259459885400260523059479 177389189828100390784589219)
    ·
      refine ⟨266083784742150586176883829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177389189828100390784589219 266083784742150586176883829)
      ·
        refine ⟨24945354819576617454082859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266083784742150586176883829 24945354819576617454082859)
        ·
          refine ⟨37418032229364926181124289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24945354819576617454082859 37418032229364926181124289)
          ·
            refine ⟨28063524172023694635843217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37418032229364926181124289 28063524172023694635843217)
            ·
              refine ⟨21047643129017770976882413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28063524172023694635843217 21047643129017770976882413)
              ·
                refine ⟨7892866173381664116330905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21047643129017770976882413 7892866173381664116330905)
                ·
                  refine ⟨5919649630036248087248179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7892866173381664116330905 5919649630036248087248179)
                  ·
                    refine ⟨8879474445054372130872269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5919649630036248087248179 8879474445054372130872269)
                    ·
                      refine ⟨3329802916895389549077101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8879474445054372130872269 3329802916895389549077101)
                      ·
                        rfl

theorem cell23_6484768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6484768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484768 prefixEnd_6484768 := by exact prefixLift 6484768
  have htrace : WordTrace (prefixWord ++ tailWord_6484768) baseStart_6484768 baseEnd_6484768 := by
    simpa [prefixWord, tailWord_6484768, baseEnd_6484768] using wordTrace_append hprefix tailTrace_6484768
  have hstable : (prefixWord ++ tailWord_6484768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484768).length < 2 ^ (prefixWord ++ tailWord_6484768).sum := by decide
  have hdescent : baseEnd_6484768 < baseStart_6484768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484791 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 1, 4, 2]
def baseStart_6484791 : Nat := 118140960795 + 6484791 * 2 ^ 59
def prefixEnd_6484791 : Nat := 4983230072969 + 3 ^ 40 * 6484791 * 2
def baseEnd_6484791 : Nat := 3329814726950442959089495

theorem tailTrace_6484791 : CollatzResearch.WordTrace tailWord_6484791 prefixEnd_6484791 3329814726950442959089495 := by
  unfold tailWord_6484791
  simp only [CollatzResearch.WordTrace]
  refine ⟨236519758649717195974206227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157679839099811463982804151 236519758649717195974206227)
  ·
    refine ⟨354779637974575793961309341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236519758649717195974206227 354779637974575793961309341)
    ·
      refine ⟨133042364240465922735491003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354779637974575793961309341 133042364240465922735491003)
      ·
        refine ⟨199563546360698884103236505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133042364240465922735491003 199563546360698884103236505)
        ·
          refine ⟨149672659770524163077427379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199563546360698884103236505 149672659770524163077427379)
          ·
            refine ⟨224508989655786244616141069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149672659770524163077427379 224508989655786244616141069)
            ·
              refine ⟨84190871120919841731052901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224508989655786244616141069 84190871120919841731052901)
              ·
                refine ⟨15785788335172470324572419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84190871120919841731052901 15785788335172470324572419)
                ·
                  refine ⟨23678682502758705486858629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15785788335172470324572419 23678682502758705486858629)
                  ·
                    refine ⟨4439752969267257278785993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23678682502758705486858629 4439752969267257278785993)
                    ·
                      refine ⟨3329814726950442959089495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439752969267257278785993 3329814726950442959089495)
                      ·
                        rfl

theorem cell23_6484791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_6484791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484791 prefixEnd_6484791 := by exact prefixLift 6484791
  have htrace : WordTrace (prefixWord ++ tailWord_6484791) baseStart_6484791 baseEnd_6484791 := by
    simpa [prefixWord, tailWord_6484791, baseEnd_6484791] using wordTrace_append hprefix tailTrace_6484791
  have hstable : (prefixWord ++ tailWord_6484791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484791).length < 2 ^ (prefixWord ++ tailWord_6484791).sum := by decide
  have hdescent : baseEnd_6484791 < baseStart_6484791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484808 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_6484808 : Nat := 118140960795 + 6484808 * 2 ^ 59
def prefixEnd_6484808 : Nat := 4983230072969 + 3 ^ 40 * 6484808 * 2
def baseEnd_6484808 : Nat := 3329823456121569392576917

theorem tailTrace_6484808 : CollatzResearch.WordTrace tailWord_6484808 prefixEnd_6484808 3329823456121569392576917 := by
  unfold tailWord_6484808
  simp only [CollatzResearch.WordTrace]
  refine ⟨118260189345327803938787539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157680252460437071918383385 118260189345327803938787539)
  ·
    refine ⟨177390284017991705908181309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118260189345327803938787539 177390284017991705908181309)
    ·
      refine ⟨66521356506746889715567991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177390284017991705908181309 66521356506746889715567991)
      ·
        refine ⟨99782034760120334573351987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66521356506746889715567991 99782034760120334573351987)
        ·
          refine ⟨149673052140180501860027981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99782034760120334573351987 149673052140180501860027981)
          ·
            refine ⟨56127394552567688197510493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149673052140180501860027981 56127394552567688197510493)
            ·
              refine ⟨21047772957212883074066435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56127394552567688197510493 21047772957212883074066435)
              ·
                refine ⟨31571659435819324611099653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21047772957212883074066435 31571659435819324611099653)
                ·
                  refine ⟨5919686144216123364581185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31571659435819324611099653 5919686144216123364581185)
                  ·
                    refine ⟨4439764608162092523435889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919686144216123364581185 4439764608162092523435889)
                    ·
                      refine ⟨3329823456121569392576917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439764608162092523435889 3329823456121569392576917)
                      ·
                        rfl

theorem cell23_6484808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_6484808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484808 prefixEnd_6484808 := by exact prefixLift 6484808
  have htrace : WordTrace (prefixWord ++ tailWord_6484808) baseStart_6484808 baseEnd_6484808 := by
    simpa [prefixWord, tailWord_6484808, baseEnd_6484808] using wordTrace_append hprefix tailTrace_6484808
  have hstable : (prefixWord ++ tailWord_6484808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484808).length < 2 ^ (prefixWord ++ tailWord_6484808).sum := by decide
  have hdescent : baseEnd_6484808 < baseStart_6484808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484844 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_6484844 : Nat := 118140960795 + 6484844 * 2 ^ 59
def prefixEnd_6484844 : Nat := 4983230072969 + 3 ^ 40 * 6484844 * 2
def baseEnd_6484844 : Nat := 1109947313808377083908917

theorem tailTrace_6484844 : CollatzResearch.WordTrace tailWord_6484844 prefixEnd_6484844 1109947313808377083908917 := by
  unfold tailWord_6484844
  simp only [CollatzResearch.WordTrace]
  refine ⟨118260845859262593012942793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157681127812350124017257057 118260845859262593012942793)
  ·
    refine ⟨88695634394446944759707095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118260845859262593012942793 88695634394446944759707095)
    ·
      refine ⟨133043451591670417139560643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88695634394446944759707095 133043451591670417139560643)
      ·
        refine ⟨199565177387505625709340965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133043451591670417139560643 199565177387505625709340965)
        ·
          refine ⟨37418470760157304820501431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199565177387505625709340965 37418470760157304820501431)
          ·
            refine ⟨56127706140235957230752147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37418470760157304820501431 56127706140235957230752147)
            ·
              refine ⟨84191559210353935846128221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56127706140235957230752147 84191559210353935846128221)
              ·
                refine ⟨31571834703882725942298083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84191559210353935846128221 31571834703882725942298083)
                ·
                  refine ⟨47357752055824088913447125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31571834703882725942298083 47357752055824088913447125)
                  ·
                    refine ⟨1109947313808377083908917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47357752055824088913447125 1109947313808377083908917)
                    ·
                      rfl

theorem cell23_6484844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_6484844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484844 prefixEnd_6484844 := by exact prefixLift 6484844
  have htrace : WordTrace (prefixWord ++ tailWord_6484844) baseStart_6484844 baseEnd_6484844 := by
    simpa [prefixWord, tailWord_6484844, baseEnd_6484844] using wordTrace_append hprefix tailTrace_6484844
  have hstable : (prefixWord ++ tailWord_6484844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484844).length < 2 ^ (prefixWord ++ tailWord_6484844).sum := by decide
  have hdescent : baseEnd_6484844 < baseStart_6484844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484864 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_6484864 : Nat := 118140960795 + 6484864 * 2 ^ 59
def prefixEnd_6484864 : Nat := 4983230072969 + 3 ^ 40 * 6484864 * 2
def baseEnd_6484864 : Nat := 3329852211038221173476659

theorem tailTrace_6484864 : CollatzResearch.WordTrace tailWord_6484864 prefixEnd_6484864 3329852211038221173476659 := by
  unfold tailWord_6484864
  simp only [CollatzResearch.WordTrace]
  refine ⟨118261210589226364720806823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157681614118968486294409097 118261210589226364720806823)
  ·
    refine ⟨177391815883839547081210235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118261210589226364720806823 177391815883839547081210235)
    ·
      refine ⟨266087723825759320621815353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177391815883839547081210235 266087723825759320621815353)
      ·
        refine ⟨199565792869319490466361515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266087723825759320621815353 199565792869319490466361515)
        ·
          refine ⟨299348689303979235699542273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199565792869319490466361515 299348689303979235699542273)
          ·
            refine ⟨224511516977984426774656705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299348689303979235699542273 224511516977984426774656705)
            ·
              refine ⟨168383637733488320080992529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224511516977984426774656705 168383637733488320080992529)
              ·
                refine ⟨126287728300116240060744397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168383637733488320080992529 126287728300116240060744397)
                ·
                  refine ⟨47357898112543590022779149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126287728300116240060744397 47357898112543590022779149)
                  ·
                    refine ⟨17759211792203846258542181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47357898112543590022779149 17759211792203846258542181)
                    ·
                      refine ⟨3329852211038221173476659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17759211792203846258542181 3329852211038221173476659)
                      ·
                        rfl

theorem cell23_6484864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_6484864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484864 prefixEnd_6484864 := by exact prefixLift 6484864
  have htrace : WordTrace (prefixWord ++ tailWord_6484864) baseStart_6484864 baseEnd_6484864 := by
    simpa [prefixWord, tailWord_6484864, baseEnd_6484864] using wordTrace_append hprefix tailTrace_6484864
  have hstable : (prefixWord ++ tailWord_6484864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484864).length < 2 ^ (prefixWord ++ tailWord_6484864).sum := by decide
  have hdescent : baseEnd_6484864 < baseStart_6484864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484871 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_6484871 : Nat := 118140960795 + 6484871 * 2 ^ 59
def prefixEnd_6484871 : Nat := 4983230072969 + 3 ^ 40 * 6484871 * 2
def baseEnd_6484871 : Nat := 3329855805402802646089127

theorem tailTrace_6484871 : CollatzResearch.WordTrace tailWord_6484871 prefixEnd_6484871 3329855805402802646089127 := by
  unfold tailWord_6484871
  simp only [CollatzResearch.WordTrace]
  refine ⟨236522676489427369637118467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157681784326284913091412311 236522676489427369637118467)
  ·
    refine ⟨354784014734141054455677701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236522676489427369637118467 354784014734141054455677701)
    ·
      refine ⟨66522002762651447710439569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354784014734141054455677701 66522002762651447710439569)
      ·
        refine ⟨49891502071988585782829677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66522002762651447710439569 49891502071988585782829677)
        ·
          refine ⟨18709313276995719668561129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49891502071988585782829677 18709313276995719668561129)
          ·
            refine ⟨14031984957746789751420847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18709313276995719668561129 14031984957746789751420847)
            ·
              refine ⟨21047977436620184627131271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14031984957746789751420847 21047977436620184627131271)
              ·
                refine ⟨31571966154930276940696907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21047977436620184627131271 31571966154930276940696907)
                ·
                  refine ⟨47357949232395415411045361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31571966154930276940696907 47357949232395415411045361)
                  ·
                    refine ⟨35518461924296561558284021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47357949232395415411045361 35518461924296561558284021)
                    ·
                      refine ⟨3329855805402802646089127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35518461924296561558284021 3329855805402802646089127)
                      ·
                        rfl

theorem cell23_6484871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_6484871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484871 prefixEnd_6484871 := by exact prefixLift 6484871
  have htrace : WordTrace (prefixWord ++ tailWord_6484871) baseStart_6484871 baseEnd_6484871 := by
    simpa [prefixWord, tailWord_6484871, baseEnd_6484871] using wordTrace_append hprefix tailTrace_6484871
  have hstable : (prefixWord ++ tailWord_6484871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484871).length < 2 ^ (prefixWord ++ tailWord_6484871).sum := by decide
  have hdescent : baseEnd_6484871 < baseStart_6484871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484881 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 1, 6, 2]
def baseStart_6484881 : Nat := 118140960795 + 6484881 * 2 ^ 59
def prefixEnd_6484881 : Nat := 4983230072969 + 3 ^ 40 * 6484881 * 2
def baseEnd_6484881 : Nat := 3329860940209347606964081

theorem tailTrace_6484881 : CollatzResearch.WordTrace tailWord_6484881 prefixEnd_6484881 3329860940209347606964081 := by
  unfold tailWord_6484881
  simp only [CollatzResearch.WordTrace]
  refine ⟨236523041219391141344982497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157682027479594094229988331 236523041219391141344982497)
  ·
    refine ⟨177392280914543356008736873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236523041219391141344982497 177392280914543356008736873)
    ·
      refine ⟨133044210685907517006552655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177392280914543356008736873 133044210685907517006552655)
      ·
        refine ⟨199566316028861275509828983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133044210685907517006552655 199566316028861275509828983)
        ·
          refine ⟨299349474043291913264743475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199566316028861275509828983 299349474043291913264743475)
          ·
            refine ⟨449024211064937869897115213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299349474043291913264743475 449024211064937869897115213)
            ·
              refine ⟨168384079149351701211418205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 449024211064937869897115213 168384079149351701211418205)
              ·
                refine ⟨63144029681006887954281827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168384079149351701211418205 63144029681006887954281827)
                ·
                  refine ⟨94716044521510331931422741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63144029681006887954281827 94716044521510331931422741)
                  ·
                    refine ⟨4439814586945796809285441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94716044521510331931422741 4439814586945796809285441)
                    ·
                      refine ⟨3329860940209347606964081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439814586945796809285441 3329860940209347606964081)
                      ·
                        rfl

theorem cell23_6484881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_6484881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484881 prefixEnd_6484881 := by exact prefixLift 6484881
  have htrace : WordTrace (prefixWord ++ tailWord_6484881) baseStart_6484881 baseEnd_6484881 := by
    simpa [prefixWord, tailWord_6484881, baseEnd_6484881] using wordTrace_append hprefix tailTrace_6484881
  have hstable : (prefixWord ++ tailWord_6484881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484881).length < 2 ^ (prefixWord ++ tailWord_6484881).sum := by decide
  have hdescent : baseEnd_6484881 < baseStart_6484881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484898 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_6484898 : Nat := 118140960795 + 6484898 * 2 ^ 59
def prefixEnd_6484898 : Nat := 4983230072969 + 3 ^ 40 * 6484898 * 2
def baseEnd_6484898 : Nat := 3329869669380474040451503

theorem tailTrace_6484898 : CollatzResearch.WordTrace tailWord_6484898 prefixEnd_6484898 3329869669380474040451503 := by
  unfold tailWord_6484898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59130915315082388312087837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157682440840219702165567565 59130915315082388312087837)
  ·
    refine ⟨22174093243155895617032939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59130915315082388312087837 22174093243155895617032939)
    ·
      refine ⟨33261139864733843425549409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22174093243155895617032939 33261139864733843425549409)
      ·
        refine ⟨24945854898550382569162057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33261139864733843425549409 24945854898550382569162057)
        ·
          refine ⟨18709391173912786926871543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24945854898550382569162057 18709391173912786926871543)
          ·
            refine ⟨28064086760869180390307315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18709391173912786926871543 28064086760869180390307315)
            ·
              refine ⟨42096130141303770585460973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28064086760869180390307315 42096130141303770585460973)
              ·
                refine ⟨15786048802988913969547865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42096130141303770585460973 15786048802988913969547865)
                ·
                  refine ⟨11839536602241685477160899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15786048802988913969547865 11839536602241685477160899)
                  ·
                    refine ⟨17759304903362528215741349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11839536602241685477160899 17759304903362528215741349)
                    ·
                      refine ⟨3329869669380474040451503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17759304903362528215741349 3329869669380474040451503)
                      ·
                        rfl

theorem cell23_6484898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_6484898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484898 prefixEnd_6484898 := by exact prefixLift 6484898
  have htrace : WordTrace (prefixWord ++ tailWord_6484898) baseStart_6484898 baseEnd_6484898 := by
    simpa [prefixWord, tailWord_6484898, baseEnd_6484898] using wordTrace_append hprefix tailTrace_6484898
  have hstable : (prefixWord ++ tailWord_6484898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484898).length < 2 ^ (prefixWord ++ tailWord_6484898).sum := by decide
  have hdescent : baseEnd_6484898 < baseStart_6484898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484921 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 6]
def baseStart_6484921 : Nat := 118140960795 + 6484921 * 2 ^ 59
def prefixEnd_6484921 : Nat := 4983230072969 + 3 ^ 40 * 6484921 * 2
def baseEnd_6484921 : Nat := 369986831048391938940433

theorem tailTrace_6484921 : CollatzResearch.WordTrace tailWord_6484921 prefixEnd_6484921 369986831048391938940433 := by
  unfold tailWord_6484921
  simp only [CollatzResearch.WordTrace]
  refine ⟨236524500139246228176438617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157683000092830818784292411 236524500139246228176438617)
  ·
    refine ⟨177393375104434671132328963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236524500139246228176438617 177393375104434671132328963)
    ·
      refine ⟨266090062656652006698493445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177393375104434671132328963 266090062656652006698493445)
      ·
        refine ⟨49891886748122251255967521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266090062656652006698493445 49891886748122251255967521)
        ·
          refine ⟨37418915061091688441975641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49891886748122251255967521 37418915061091688441975641)
          ·
            refine ⟨28064186295818766331481731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37418915061091688441975641 28064186295818766331481731)
            ·
              refine ⟨42096279443728149497222597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28064186295818766331481731 42096279443728149497222597)
              ·
                refine ⟨7893052395699028030729237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42096279443728149497222597 7893052395699028030729237)
                ·
                  refine ⟨369986831048391938940433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7893052395699028030729237 369986831048391938940433)
                  ·
                    rfl

theorem cell23_6484921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 6].length) (baseStart_6484921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484921 prefixEnd_6484921 := by exact prefixLift 6484921
  have htrace : WordTrace (prefixWord ++ tailWord_6484921) baseStart_6484921 baseEnd_6484921 := by
    simpa [prefixWord, tailWord_6484921, baseEnd_6484921] using wordTrace_append hprefix tailTrace_6484921
  have hstable : (prefixWord ++ tailWord_6484921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484921).length < 2 ^ (prefixWord ++ tailWord_6484921).sum := by decide
  have hdescent : baseEnd_6484921 < baseStart_6484921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484932 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6484932 : Nat := 118140960795 + 6484932 * 2 ^ 59
def prefixEnd_6484932 : Nat := 4983230072969 + 3 ^ 40 * 6484932 * 2
def baseEnd_6484932 : Nat := 3329887127722726907426347

theorem tailTrace_6484932 : CollatzResearch.WordTrace tailWord_6484932 prefixEnd_6484932 3329887127722726907426347 := by
  unfold tailWord_6484932
  simp only [CollatzResearch.WordTrace]
  refine ⟨118262450671103188527544525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157683267561470918036726033 118262450671103188527544525)
  ·
    refine ⟨44348419001663695697829197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118262450671103188527544525 44348419001663695697829197)
    ·
      refine ⟨16630657125623885886685949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44348419001663695697829197 16630657125623885886685949)
      ·
        refine ⟨6236496422108957207507231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16630657125623885886685949 6236496422108957207507231)
        ·
          refine ⟨9354744633163435811260847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236496422108957207507231 9354744633163435811260847)
          ·
            refine ⟨14032116949745153716891271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9354744633163435811260847 14032116949745153716891271)
            ·
              refine ⟨21048175424617730575336907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14032116949745153716891271 21048175424617730575336907)
              ·
                refine ⟨31572263136926595863005361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21048175424617730575336907 31572263136926595863005361)
                ·
                  refine ⟨23679197352694946897254021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31572263136926595863005361 23679197352694946897254021)
                  ·
                    refine ⟨4439849503630302543235129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23679197352694946897254021 4439849503630302543235129)
                    ·
                      refine ⟨3329887127722726907426347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439849503630302543235129 3329887127722726907426347)
                      ·
                        rfl

theorem cell23_6484932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6484932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484932 prefixEnd_6484932 := by exact prefixLift 6484932
  have htrace : WordTrace (prefixWord ++ tailWord_6484932) baseStart_6484932 baseEnd_6484932 := by
    simpa [prefixWord, tailWord_6484932, baseEnd_6484932] using wordTrace_append hprefix tailTrace_6484932
  have hstable : (prefixWord ++ tailWord_6484932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484932).length < 2 ^ (prefixWord ++ tailWord_6484932).sum := by decide
  have hdescent : baseEnd_6484932 < baseStart_6484932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484944 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_6484944 : Nat := 118140960795 + 6484944 * 2 ^ 59
def prefixEnd_6484944 : Nat := 4983230072969 + 3 ^ 40 * 6484944 * 2
def baseEnd_6484944 : Nat := 3329893289490580860476291

theorem tailTrace_6484944 : CollatzResearch.WordTrace tailWord_6484944 prefixEnd_6484944 3329893289490580860476291 := by
  unfold tailWord_6484944
  simp only [CollatzResearch.WordTrace]
  refine ⟨118262669509081451552262943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157683559345441935403017257 118262669509081451552262943)
  ·
    refine ⟨177394004263622177328394415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118262669509081451552262943 177394004263622177328394415)
    ·
      refine ⟨266091006395433265992591623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177394004263622177328394415 266091006395433265992591623)
      ·
        refine ⟨399136509593149898988887435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266091006395433265992591623 399136509593149898988887435)
        ·
          refine ⟨598704764389724848483331153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399136509593149898988887435 598704764389724848483331153)
          ·
            refine ⟨449028573292293636362498365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598704764389724848483331153 449028573292293636362498365)
            ·
              refine ⟨168385714984610113635936887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 449028573292293636362498365 168385714984610113635936887)
              ·
                refine ⟨252578572476915170453905331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168385714984610113635936887 252578572476915170453905331)
                ·
                  refine ⟨378867858715372755680857997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252578572476915170453905331 378867858715372755680857997)
                  ·
                    refine ⟨142075447018264783380321749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378867858715372755680857997 142075447018264783380321749)
                    ·
                      refine ⟨3329893289490580860476291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142075447018264783380321749 3329893289490580860476291)
                      ·
                        rfl

theorem cell23_6484944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_6484944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484944 prefixEnd_6484944 := by exact prefixLift 6484944
  have htrace : WordTrace (prefixWord ++ tailWord_6484944) baseStart_6484944 baseEnd_6484944 := by
    simpa [prefixWord, tailWord_6484944, baseEnd_6484944] using wordTrace_append hprefix tailTrace_6484944
  have hstable : (prefixWord ++ tailWord_6484944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484944).length < 2 ^ (prefixWord ++ tailWord_6484944).sum := by decide
  have hdescent : baseEnd_6484944 < baseStart_6484944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6484982 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_6484982 : Nat := 118140960795 + 6484982 * 2 ^ 59
def prefixEnd_6484982 : Nat := 4983230072969 + 3 ^ 40 * 6484982 * 2
def baseEnd_6484982 : Nat := 3329912801755451711801117

theorem tailTrace_6484982 : CollatzResearch.WordTrace tailWord_6484982 prefixEnd_6484982 3329912801755451711801117 := by
  unfold tailWord_6484982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782920312001577224650575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157684483328016823729606133 14782920312001577224650575)
  ·
    refine ⟨22174380468002365836975863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14782920312001577224650575 22174380468002365836975863)
    ·
      refine ⟨33261570702003548755463795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22174380468002365836975863 33261570702003548755463795)
      ·
        refine ⟨49892356053005323133195693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33261570702003548755463795 49892356053005323133195693)
        ·
          refine ⟨18709633519876996174948385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49892356053005323133195693 18709633519876996174948385)
          ·
            refine ⟨14032225139907747131211289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18709633519876996174948385 14032225139907747131211289)
            ·
              refine ⟨10524168854930810348408467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14032225139907747131211289 10524168854930810348408467)
              ·
                refine ⟨15786253282396215522612701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10524168854930810348408467 15786253282396215522612701)
                ·
                  refine ⟨5919844980898580820979763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15786253282396215522612701 5919844980898580820979763)
                  ·
                    refine ⟨8879767471347871231469645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5919844980898580820979763 8879767471347871231469645)
                    ·
                      refine ⟨3329912801755451711801117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8879767471347871231469645 3329912801755451711801117)
                      ·
                        rfl

theorem cell23_6484982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_6484982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6484982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6484982 prefixEnd_6484982 := by exact prefixLift 6484982
  have htrace : WordTrace (prefixWord ++ tailWord_6484982) baseStart_6484982 baseEnd_6484982 := by
    simpa [prefixWord, tailWord_6484982, baseEnd_6484982] using wordTrace_append hprefix tailTrace_6484982
  have hstable : (prefixWord ++ tailWord_6484982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6484982).length < 2 ^ (prefixWord ++ tailWord_6484982).sum := by decide
  have hdescent : baseEnd_6484982 < baseStart_6484982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6484982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485025 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_6485025 : Nat := 118140960795 + 6485025 * 2 ^ 59
def prefixEnd_6485025 : Nat := 4983230072969 + 3 ^ 40 * 6485025 * 2
def baseEnd_6485025 : Nat := 3329934881423595043563419

theorem tailTrace_6485025 : CollatzResearch.WordTrace tailWord_6485025 prefixEnd_6485025 3329934881423595043563419 := by
  unfold tailWord_6485025
  simp only [CollatzResearch.WordTrace]
  refine ⟨236528293330869453938224529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157685528887246302625483019 236528293330869453938224529)
  ·
    refine ⟨177396219998152090453668397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236528293330869453938224529 177396219998152090453668397)
    ·
      refine ⟨66523582499307033920125649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177396219998152090453668397 66523582499307033920125649)
      ·
        refine ⟨49892686874480275440094237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66523582499307033920125649 49892686874480275440094237)
        ·
          refine ⟨18709757577930103290035339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49892686874480275440094237 18709757577930103290035339)
          ·
            refine ⟨28064636366895154935053009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18709757577930103290035339 28064636366895154935053009)
            ·
              refine ⟨21048477275171366201289757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28064636366895154935053009 21048477275171366201289757)
              ·
                refine ⟨7893178978189262325483659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21048477275171366201289757 7893178978189262325483659)
                ·
                  refine ⟨11839768467283893488225489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7893178978189262325483659 11839768467283893488225489)
                  ·
                    refine ⟨8879826350462920116169117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11839768467283893488225489 8879826350462920116169117)
                    ·
                      refine ⟨3329934881423595043563419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8879826350462920116169117 3329934881423595043563419)
                      ·
                        rfl

theorem cell23_6485025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_6485025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485025 prefixEnd_6485025 := by exact prefixLift 6485025
  have htrace : WordTrace (prefixWord ++ tailWord_6485025) baseStart_6485025 baseEnd_6485025 := by
    simpa [prefixWord, tailWord_6485025, baseEnd_6485025] using wordTrace_append hprefix tailTrace_6485025
  have hstable : (prefixWord ++ tailWord_6485025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485025).length < 2 ^ (prefixWord ++ tailWord_6485025).sum := by decide
  have hdescent : baseEnd_6485025 < baseStart_6485025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485028 : List Nat := [2, 3, 1, 4, 1, 3, 9]
def baseStart_6485028 : Nat := 118140960795 + 6485028 * 2 ^ 59
def prefixEnd_6485028 : Nat := 4983230072969 + 3 ^ 40 * 6485028 * 2
def baseEnd_6485028 : Nat := 41110326195871092985505

theorem tailTrace_6485028 : CollatzResearch.WordTrace tailWord_6485028 prefixEnd_6485028 41110326195871092985505 := by
  unfold tailWord_6485028
  simp only [CollatzResearch.WordTrace]
  refine ⟨118264201374929292725291869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157685601833239056967055825 118264201374929292725291869)
  ·
    refine ⟨44349075515598484771984451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118264201374929292725291869 44349075515598484771984451)
    ·
      refine ⟨66523613273397727157976677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44349075515598484771984451 66523613273397727157976677)
      ·
        refine ⟨12473177488762073842120627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66523613273397727157976677 12473177488762073842120627)
        ·
          refine ⟨18709766233143110763180941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12473177488762073842120627 18709766233143110763180941)
          ·
            refine ⟨7016162337428666536192853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18709766233143110763180941 7016162337428666536192853)
            ·
              refine ⟨41110326195871092985505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7016162337428666536192853 41110326195871092985505)
              ·
                rfl

theorem cell23_6485028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 9].length) (baseStart_6485028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485028 prefixEnd_6485028 := by exact prefixLift 6485028
  have htrace : WordTrace (prefixWord ++ tailWord_6485028) baseStart_6485028 baseEnd_6485028 := by
    simpa [prefixWord, tailWord_6485028, baseEnd_6485028] using wordTrace_append hprefix tailTrace_6485028
  have hstable : (prefixWord ++ tailWord_6485028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485028).length < 2 ^ (prefixWord ++ tailWord_6485028).sum := by decide
  have hdescent : baseEnd_6485028 < baseStart_6485028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485041 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 2, 7]
def baseStart_6485041 : Nat := 118140960795 + 6485041 * 2 ^ 59
def prefixEnd_6485041 : Nat := 4983230072969 + 3 ^ 40 * 6485041 * 2
def baseEnd_6485041 : Nat := 1109981032371355660321115

theorem tailTrace_6485041 : CollatzResearch.WordTrace tailWord_6485041 prefixEnd_6485041 1109981032371355660321115 := by
  unfold tailWord_6485041
  simp only [CollatzResearch.WordTrace]
  refine ⟨236528876898811488670806977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157685917932540992447204651 236528876898811488670806977)
  ·
    refine ⟨177396657674108616503105233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236528876898811488670806977 177396657674108616503105233)
    ·
      refine ⟨133047493255581462377328925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177396657674108616503105233 133047493255581462377328925)
      ·
        refine ⟨49892809970843048391498347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133047493255581462377328925 49892809970843048391498347)
        ·
          refine ⟨74839214956264572587247521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49892809970843048391498347 74839214956264572587247521)
          ·
            refine ⟨56129411217198429440435641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74839214956264572587247521 56129411217198429440435641)
            ·
              refine ⟨42097058412898822080326731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56129411217198429440435641 42097058412898822080326731)
              ·
                refine ⟨63145587619348233120490097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42097058412898822080326731 63145587619348233120490097)
                ·
                  refine ⟨47359190714511174840367573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63145587619348233120490097 47359190714511174840367573)
                  ·
                    refine ⟨1109981032371355660321115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47359190714511174840367573 1109981032371355660321115)
                    ·
                      rfl

theorem cell23_6485041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_6485041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485041 prefixEnd_6485041 := by exact prefixLift 6485041
  have htrace : WordTrace (prefixWord ++ tailWord_6485041) baseStart_6485041 baseEnd_6485041 := by
    simpa [prefixWord, tailWord_6485041, baseEnd_6485041] using wordTrace_append hprefix tailTrace_6485041
  have hstable : (prefixWord ++ tailWord_6485041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485041).length < 2 ^ (prefixWord ++ tailWord_6485041).sum := by decide
  have hdescent : baseEnd_6485041 < baseStart_6485041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485065 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 1, 3, 2]
def baseStart_6485065 : Nat := 118140960795 + 6485065 * 2 ^ 59
def prefixEnd_6485065 : Nat := 4983230072969 + 3 ^ 40 * 6485065 * 2
def baseEnd_6485065 : Nat := 3329955420649774887063235

theorem tailTrace_6485065 : CollatzResearch.WordTrace tailWord_6485065 prefixEnd_6485065 3329955420649774887063235 := by
  unfold tailWord_6485065
  simp only [CollatzResearch.WordTrace]
  refine ⟨236529752250724540769680649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157686501500483027179787099 236529752250724540769680649)
  ·
    refine ⟨177397314188043405577260487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236529752250724540769680649 177397314188043405577260487)
    ·
      refine ⟨266095971282065108365890731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177397314188043405577260487 266095971282065108365890731)
      ·
        refine ⟨399143956923097662548836097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266095971282065108365890731 399143956923097662548836097)
        ·
          refine ⟨299357967692323246911627073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399143956923097662548836097 299357967692323246911627073)
          ·
            refine ⟨224518475769242435183720305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299357967692323246911627073 224518475769242435183720305)
            ·
              refine ⟨168388856826931826387790229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224518475769242435183720305 168388856826931826387790229)
              ·
                refine ⟨7893227663762429361927667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168388856826931826387790229 7893227663762429361927667)
                ·
                  refine ⟨11839841495643644042891501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7893227663762429361927667 11839841495643644042891501)
                  ·
                    refine ⟨4439940560866366516084313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11839841495643644042891501 4439940560866366516084313)
                    ·
                      refine ⟨3329955420649774887063235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439940560866366516084313 3329955420649774887063235)
                      ·
                        rfl

theorem cell23_6485065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 3, 2].length) (baseStart_6485065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485065 prefixEnd_6485065 := by exact prefixLift 6485065
  have htrace : WordTrace (prefixWord ++ tailWord_6485065) baseStart_6485065 baseEnd_6485065 := by
    simpa [prefixWord, tailWord_6485065, baseEnd_6485065] using wordTrace_append hprefix tailTrace_6485065
  have hstable : (prefixWord ++ tailWord_6485065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485065).length < 2 ^ (prefixWord ++ tailWord_6485065).sum := by decide
  have hdescent : baseEnd_6485065 < baseStart_6485065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485081 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_6485081 : Nat := 118140960795 + 6485081 * 2 ^ 59
def prefixEnd_6485081 : Nat := 4983230072969 + 3 ^ 40 * 6485081 * 2
def baseEnd_6485081 : Nat := 3329963636340246824463161

theorem tailTrace_6485081 : CollatzResearch.WordTrace tailWord_6485081 prefixEnd_6485081 3329963636340246824463161 := by
  unfold tailWord_6485081
  simp only [CollatzResearch.WordTrace]
  refine ⟨236530335818666575502263097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157686890545777717001508731 236530335818666575502263097)
  ·
    refine ⟨177397751863999931626697323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236530335818666575502263097 177397751863999931626697323)
    ·
      refine ⟨266096627795999897440045985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177397751863999931626697323 266096627795999897440045985)
      ·
        refine ⟨199572470846999923080034489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266096627795999897440045985 199572470846999923080034489)
        ·
          refine ⟨149679353135249942310025867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199572470846999923080034489 149679353135249942310025867)
          ·
            refine ⟨224519029702874913465038801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149679353135249942310025867 224519029702874913465038801)
            ·
              refine ⟨168389272277156185098779101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224519029702874913465038801 168389272277156185098779101)
              ·
                refine ⟨63145977103933569412042163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168389272277156185098779101 63145977103933569412042163)
                ·
                  refine ⟨94718965655900354118063245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63145977103933569412042163 94718965655900354118063245)
                  ·
                    refine ⟨35519612120962632794273717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94718965655900354118063245 35519612120962632794273717)
                    ·
                      refine ⟨3329963636340246824463161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35519612120962632794273717 3329963636340246824463161)
                      ·
                        rfl

theorem cell23_6485081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_6485081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485081 prefixEnd_6485081 := by exact prefixLift 6485081
  have htrace : WordTrace (prefixWord ++ tailWord_6485081) baseStart_6485081 baseEnd_6485081 := by
    simpa [prefixWord, tailWord_6485081, baseEnd_6485081] using wordTrace_append hprefix tailTrace_6485081
  have hstable : (prefixWord ++ tailWord_6485081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485081).length < 2 ^ (prefixWord ++ tailWord_6485081).sum := by decide
  have hdescent : baseEnd_6485081 < baseStart_6485081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485091 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6]
def baseStart_6485091 : Nat := 118140960795 + 6485091 * 2 ^ 59
def prefixEnd_6485091 : Nat := 4983230072969 + 3 ^ 40 * 6485091 * 2
def baseEnd_6485091 : Nat := 3329968771146791785338115

theorem tailTrace_6485091 : CollatzResearch.WordTrace tailWord_6485091 prefixEnd_6485091 3329968771146791785338115 := by
  unfold tailWord_6485091
  simp only [CollatzResearch.WordTrace]
  refine ⟨236530700548630347210127127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157687133699086898140084751 236530700548630347210127127)
  ·
    refine ⟨354796050822945520815190691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236530700548630347210127127 354796050822945520815190691)
    ·
      refine ⟨532194076234418281222786037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354796050822945520815190691 532194076234418281222786037)
      ·
        refine ⟨49893194646976713864636191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 532194076234418281222786037 49893194646976713864636191)
        ·
          refine ⟨74839791970465070796954287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49893194646976713864636191 74839791970465070796954287)
          ·
            refine ⟨112259687955697606195431431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74839791970465070796954287 112259687955697606195431431)
            ·
              refine ⟨168389531933546409293147147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112259687955697606195431431 168389531933546409293147147)
              ·
                refine ⟨252584297900319613939720721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168389531933546409293147147 252584297900319613939720721)
                ·
                  refine ⟨189438223425239710454790541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252584297900319613939720721 189438223425239710454790541)
                  ·
                    refine ⟨71039333784464891420546453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189438223425239710454790541 71039333784464891420546453)
                    ·
                      refine ⟨3329968771146791785338115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71039333784464891420546453 3329968771146791785338115)
                      ·
                        rfl

theorem cell23_6485091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_6485091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485091 prefixEnd_6485091 := by exact prefixLift 6485091
  have htrace : WordTrace (prefixWord ++ tailWord_6485091) baseStart_6485091 baseEnd_6485091 := by
    simpa [prefixWord, tailWord_6485091, baseEnd_6485091] using wordTrace_append hprefix tailTrace_6485091
  have hstable : (prefixWord ++ tailWord_6485091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485091).length < 2 ^ (prefixWord ++ tailWord_6485091).sum := by decide
  have hdescent : baseEnd_6485091 < baseStart_6485091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485112 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 2, 2, 2]
def baseStart_6485112 : Nat := 118140960795 + 6485112 * 2 ^ 59
def prefixEnd_6485112 : Nat := 4983230072969 + 3 ^ 40 * 6485112 * 2
def baseEnd_6485112 : Nat := 3329979554240536203175519

theorem tailTrace_6485112 : CollatzResearch.WordTrace tailWord_6485112 prefixEnd_6485112 3329979554240536203175519 := by
  unfold tailWord_6485112
  simp only [CollatzResearch.WordTrace]
  refine ⟨118265733240777133898320795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157687644321036178531094393 118265733240777133898320795)
  ·
    refine ⟨177398599861165700847481193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118265733240777133898320795 177398599861165700847481193)
    ·
      refine ⟨133048949895874275635610895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177398599861165700847481193 133048949895874275635610895)
      ·
        refine ⟨199573424843811413453416343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133048949895874275635610895 199573424843811413453416343)
        ·
          refine ⟨299360137265717120180124515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199573424843811413453416343 299360137265717120180124515)
          ·
            refine ⟨449040205898575680270186773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299360137265717120180124515 449040205898575680270186773)
            ·
              refine ⟨21048759651495735012665005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 449040205898575680270186773 21048759651495735012665005)
              ·
                refine ⟨7893284869310900629749377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21048759651495735012665005 7893284869310900629749377)
                ·
                  refine ⟨5919963651983175472312033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7893284869310900629749377 5919963651983175472312033)
                  ·
                    refine ⟨4439972738987381604234025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919963651983175472312033 4439972738987381604234025)
                    ·
                      refine ⟨3329979554240536203175519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439972738987381604234025 3329979554240536203175519)
                      ·
                        rfl

theorem cell23_6485112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_6485112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485112 prefixEnd_6485112 := by exact prefixLift 6485112
  have htrace : WordTrace (prefixWord ++ tailWord_6485112) baseStart_6485112 baseEnd_6485112 := by
    simpa [prefixWord, tailWord_6485112, baseEnd_6485112] using wordTrace_append hprefix tailTrace_6485112
  have hstable : (prefixWord ++ tailWord_6485112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485112).length < 2 ^ (prefixWord ++ tailWord_6485112).sum := by decide
  have hdescent : baseEnd_6485112 < baseStart_6485112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485146 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6485146 : Nat := 118140960795 + 6485146 * 2 ^ 59
def prefixEnd_6485146 : Nat := 4983230072969 + 3 ^ 40 * 6485146 * 2
def baseEnd_6485146 : Nat := 3329997012582789070150363

theorem tailTrace_6485146 : CollatzResearch.WordTrace tailWord_6485146 prefixEnd_6485146 3329997012582789070150363 := by
  unfold tailWord_6485146
  simp only [CollatzResearch.WordTrace]
  refine ⟨59133176640857772900844823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157688471042287394402252861 59133176640857772900844823)
  ·
    refine ⟨88699764961286659351267235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59133176640857772900844823 88699764961286659351267235)
    ·
      refine ⟨133049647441929989026900853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88699764961286659351267235 133049647441929989026900853)
      ·
        refine ⟨12473404447680936471271955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133049647441929989026900853 12473404447680936471271955)
        ·
          refine ⟨18710106671521404706907933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12473404447680936471271955 18710106671521404706907933)
          ·
            refine ⟨7016290001820526765090475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18710106671521404706907933 7016290001820526765090475)
            ·
              refine ⟨10524435002730790147635713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7016290001820526765090475 10524435002730790147635713)
              ·
                refine ⟨7893326252048092610726785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10524435002730790147635713 7893326252048092610726785)
                ·
                  refine ⟨5919994689036069458045089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7893326252048092610726785 5919994689036069458045089)
                  ·
                    refine ⟨4439996016777052093533817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919994689036069458045089 4439996016777052093533817)
                    ·
                      refine ⟨3329997012582789070150363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4439996016777052093533817 3329997012582789070150363)
                      ·
                        rfl

theorem cell23_6485146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6485146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485146 prefixEnd_6485146 := by exact prefixLift 6485146
  have htrace : WordTrace (prefixWord ++ tailWord_6485146) baseStart_6485146 baseEnd_6485146 := by
    simpa [prefixWord, tailWord_6485146, baseEnd_6485146] using wordTrace_append hprefix tailTrace_6485146
  have hstable : (prefixWord ++ tailWord_6485146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485146).length < 2 ^ (prefixWord ++ tailWord_6485146).sum := by decide
  have hdescent : baseEnd_6485146 < baseStart_6485146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485162 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6485162 : Nat := 118140960795 + 6485162 * 2 ^ 59
def prefixEnd_6485162 : Nat := 4983230072969 + 3 ^ 40 * 6485162 * 2
def baseEnd_6485162 : Nat := 3330005228273261007550289

theorem tailTrace_6485162 : CollatzResearch.WordTrace tailWord_6485162 prefixEnd_6485162 3330005228273261007550289 := by
  unfold tailWord_6485162
  simp only [CollatzResearch.WordTrace]
  refine ⟨59133322532843281583990435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157688860087582084223974493 59133322532843281583990435)
  ·
    refine ⟨88699983799264922375985653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59133322532843281583990435 88699983799264922375985653)
    ·
      refine ⟨8315623481181086472748655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88699983799264922375985653 8315623481181086472748655)
      ·
        refine ⟨12473435221771629709122983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315623481181086472748655 12473435221771629709122983)
        ·
          refine ⟨18710152832657444563684475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12473435221771629709122983 18710152832657444563684475)
          ·
            refine ⟨28065229248986166845526713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18710152832657444563684475 28065229248986166845526713)
            ·
              refine ⟨21048921936739625134145035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28065229248986166845526713 21048921936739625134145035)
              ·
                refine ⟨31573382905109437701217553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21048921936739625134145035 31573382905109437701217553)
                ·
                  refine ⟨23680037178832078275913165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31573382905109437701217553 23680037178832078275913165)
                  ·
                    refine ⟨8880013942062029353467437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23680037178832078275913165 8880013942062029353467437)
                    ·
                      refine ⟨3330005228273261007550289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8880013942062029353467437 3330005228273261007550289)
                      ·
                        rfl

theorem cell23_6485162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6485162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485162 prefixEnd_6485162 := by exact prefixLift 6485162
  have htrace : WordTrace (prefixWord ++ tailWord_6485162) baseStart_6485162 baseEnd_6485162 := by
    simpa [prefixWord, tailWord_6485162, baseEnd_6485162] using wordTrace_append hprefix tailTrace_6485162
  have hstable : (prefixWord ++ tailWord_6485162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485162).length < 2 ^ (prefixWord ++ tailWord_6485162).sum := by decide
  have hdescent : baseEnd_6485162 < baseStart_6485162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485168 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_6485168 : Nat := 118140960795 + 6485168 * 2 ^ 59
def prefixEnd_6485168 : Nat := 4983230072969 + 3 ^ 40 * 6485168 * 2
def baseEnd_6485168 : Nat := 3330008309157187984075261

theorem tailTrace_6485168 : CollatzResearch.WordTrace tailWord_6485168 prefixEnd_6485168 3330008309157187984075261 := by
  unfold tailWord_6485168
  simp only [CollatzResearch.WordTrace]
  refine ⟨118266754484675694680340079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157689005979567592907120105 118266754484675694680340079)
  ·
    refine ⟨177400131727013542020510119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118266754484675694680340079 177400131727013542020510119)
    ·
      refine ⟨266100197590520313030765179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177400131727013542020510119 266100197590520313030765179)
      ·
        refine ⟨399150296385780469546147769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266100197590520313030765179 399150296385780469546147769)
        ·
          refine ⟨299362722289335352159610827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399150296385780469546147769 299362722289335352159610827)
          ·
            refine ⟨449044083434003028239416241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299362722289335352159610827 449044083434003028239416241)
            ·
              refine ⟨336783062575502271179562181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449044083434003028239416241 336783062575502271179562181)
              ·
                refine ⟨63146824232906675846167909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336783062575502271179562181 63146824232906675846167909)
                ·
                  refine ⟨11840029543670001721156483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63146824232906675846167909 11840029543670001721156483)
                  ·
                    refine ⟨17760044315505002581734725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11840029543670001721156483 17760044315505002581734725)
                    ·
                      refine ⟨3330008309157187984075261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17760044315505002581734725 3330008309157187984075261)
                      ·
                        rfl

theorem cell23_6485168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_6485168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485168 prefixEnd_6485168 := by exact prefixLift 6485168
  have htrace : WordTrace (prefixWord ++ tailWord_6485168) baseStart_6485168 baseEnd_6485168 := by
    simpa [prefixWord, tailWord_6485168, baseEnd_6485168] using wordTrace_append hprefix tailTrace_6485168
  have hstable : (prefixWord ++ tailWord_6485168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485168).length < 2 ^ (prefixWord ++ tailWord_6485168).sum := by decide
  have hdescent : baseEnd_6485168 < baseStart_6485168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485275 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 2, 6, 2]
def baseStart_6485275 : Nat := 118140960795 + 6485275 * 2 ^ 59
def prefixEnd_6485275 : Nat := 4983230072969 + 3 ^ 40 * 6485275 * 2
def baseEnd_6485275 : Nat := 3330063251587219065437269

theorem tailTrace_6485275 : CollatzResearch.WordTrace tailWord_6485275 prefixEnd_6485275 3330063251587219065437269 := by
  unfold tailWord_6485275
  simp only [CollatzResearch.WordTrace]
  refine ⟨236537411579963746634825279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157691607719975831089883519 236537411579963746634825279)
  ·
    refine ⟨354806117369945619952237919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236537411579963746634825279 354806117369945619952237919)
    ·
      refine ⟨532209176054918429928356879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354806117369945619952237919 532209176054918429928356879)
      ·
        refine ⟨798313764082377644892535319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532209176054918429928356879 798313764082377644892535319)
        ·
          refine ⟨1197470646123566467338802979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798313764082377644892535319 1197470646123566467338802979)
          ·
            refine ⟨1796205969185349701008204469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197470646123566467338802979 1796205969185349701008204469)
            ·
              refine ⟨168394309611126534469519169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1796205969185349701008204469 168394309611126534469519169)
              ·
                refine ⟨126295732208344900852139377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168394309611126534469519169 126295732208344900852139377)
                ·
                  refine ⟨94721799156258675639104533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126295732208344900852139377 94721799156258675639104533)
                  ·
                    refine ⟨4440084335449625420583025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94721799156258675639104533 4440084335449625420583025)
                    ·
                      refine ⟨3330063251587219065437269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440084335449625420583025 3330063251587219065437269)
                      ·
                        rfl

theorem cell23_6485275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6, 2].length) (baseStart_6485275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485275 prefixEnd_6485275 := by exact prefixLift 6485275
  have htrace : WordTrace (prefixWord ++ tailWord_6485275) baseStart_6485275 baseEnd_6485275 := by
    simpa [prefixWord, tailWord_6485275, baseEnd_6485275] using wordTrace_append hprefix tailTrace_6485275
  have hstable : (prefixWord ++ tailWord_6485275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485275).length < 2 ^ (prefixWord ++ tailWord_6485275).sum := by decide
  have hdescent : baseEnd_6485275 < baseStart_6485275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485285 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_6485285 : Nat := 118140960795 + 6485285 * 2 ^ 59
def prefixEnd_6485285 : Nat := 4983230072969 + 3 ^ 40 * 6485285 * 2
def baseEnd_6485285 : Nat := 1110022795464588008770741

theorem tailTrace_6485285 : CollatzResearch.WordTrace tailWord_6485285 prefixEnd_6485285 1110022795464588008770741 := by
  unfold tailWord_6485285
  simp only [CollatzResearch.WordTrace]
  refine ⟨236537776309927518342689309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157691850873285012228459539 236537776309927518342689309)
  ·
    refine ⟨88701666116222819378508491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236537776309927518342689309 88701666116222819378508491)
    ·
      refine ⟨133052499174334229067762737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88701666116222819378508491 133052499174334229067762737)
      ·
        refine ⟨99789374380750671800822053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133052499174334229067762737 99789374380750671800822053)
        ·
          refine ⟨18710507696390750962654135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99789374380750671800822053 18710507696390750962654135)
          ·
            refine ⟨28065761544586126443981203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18710507696390750962654135 28065761544586126443981203)
            ·
              refine ⟨42098642316879189665971805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28065761544586126443981203 42098642316879189665971805)
              ·
                refine ⟨15786990868829696124739427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42098642316879189665971805 15786990868829696124739427)
                ·
                  refine ⟨23680486303244544187109141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15786990868829696124739427 23680486303244544187109141)
                  ·
                    refine ⟨1110022795464588008770741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23680486303244544187109141 1110022795464588008770741)
                    ·
                      rfl

theorem cell23_6485285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_6485285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485285 prefixEnd_6485285 := by exact prefixLift 6485285
  have htrace : WordTrace (prefixWord ++ tailWord_6485285) baseStart_6485285 baseEnd_6485285 := by
    simpa [prefixWord, tailWord_6485285, baseEnd_6485285] using wordTrace_append hprefix tailTrace_6485285
  have hstable : (prefixWord ++ tailWord_6485285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485285).length < 2 ^ (prefixWord ++ tailWord_6485285).sum := by decide
  have hdescent : baseEnd_6485285 < baseStart_6485285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485312 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3]
def baseStart_6485312 : Nat := 118140960795 + 6485312 * 2 ^ 59
def prefixEnd_6485312 : Nat := 4983230072969 + 3 ^ 40 * 6485312 * 2
def baseEnd_6485312 : Nat := 3330082250371435420674599

theorem tailTrace_6485312 : CollatzResearch.WordTrace tailWord_6485312 prefixEnd_6485312 3330082250371435420674599 := by
  unfold tailWord_6485312
  simp only [CollatzResearch.WordTrace]
  refine ⟨118269380540414850976961095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157692507387219801302614793 118269380540414850976961095)
  ·
    refine ⟨177404070810622276465441643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118269380540414850976961095 177404070810622276465441643)
    ·
      refine ⟨266106106215933414698162465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177404070810622276465441643 266106106215933414698162465)
      ·
        refine ⟨199579579661950061023621849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266106106215933414698162465 199579579661950061023621849)
        ·
          refine ⟨149684684746462545767716387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199579579661950061023621849 149684684746462545767716387)
          ·
            refine ⟨224527027119693818651574581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149684684746462545767716387 224527027119693818651574581)
            ·
              refine ⟨21049408792471295498585117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224527027119693818651574581 21049408792471295498585117)
              ·
                refine ⟨7893528297176735811969419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21049408792471295498585117 7893528297176735811969419)
                ·
                  refine ⟨11840292445765103717954129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7893528297176735811969419 11840292445765103717954129)
                  ·
                    refine ⟨8880219334323827788465597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11840292445765103717954129 8880219334323827788465597)
                    ·
                      refine ⟨3330082250371435420674599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8880219334323827788465597 3330082250371435420674599)
                      ·
                        rfl

theorem cell23_6485312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_6485312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485312 prefixEnd_6485312 := by exact prefixLift 6485312
  have htrace : WordTrace (prefixWord ++ tailWord_6485312) baseStart_6485312 baseEnd_6485312 := by
    simpa [prefixWord, tailWord_6485312, baseEnd_6485312] using wordTrace_append hprefix tailTrace_6485312
  have hstable : (prefixWord ++ tailWord_6485312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485312).length < 2 ^ (prefixWord ++ tailWord_6485312).sum := by decide
  have hdescent : baseEnd_6485312 < baseStart_6485312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485319 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 2, 4]
def baseStart_6485319 : Nat := 118140960795 + 6485319 * 2 ^ 59
def prefixEnd_6485319 : Nat := 4983230072969 + 3 ^ 40 * 6485319 * 2
def baseEnd_6485319 : Nat := 1110028614912005631095689

theorem tailTrace_6485319 : CollatzResearch.WordTrace tailWord_6485319 prefixEnd_6485319 1110028614912005631095689 := by
  unfold tailWord_6485319
  simp only [CollatzResearch.WordTrace]
  refine ⟨236539016391804342149427011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157692677594536228099618007 236539016391804342149427011)
  ·
    refine ⟨354808524587706513224140517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236539016391804342149427011 354808524587706513224140517)
    ·
      refine ⟨66526598360194971229526347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354808524587706513224140517 66526598360194971229526347)
      ·
        refine ⟨99789897540292456844289521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66526598360194971229526347 99789897540292456844289521)
        ·
          refine ⟨74842423155219342633217141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99789897540292456844289521 74842423155219342633217141)
          ·
            refine ⟨7016477170801813371864107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74842423155219342633217141 7016477170801813371864107)
            ·
              refine ⟨10524715756202720057796161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7016477170801813371864107 10524715756202720057796161)
              ·
                refine ⟨7893536817152040043347121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10524715756202720057796161 7893536817152040043347121)
                ·
                  refine ⟨5920152612864030032510341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7893536817152040043347121 5920152612864030032510341)
                  ·
                    refine ⟨1110028614912005631095689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5920152612864030032510341 1110028614912005631095689)
                    ·
                      rfl

theorem cell23_6485319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_6485319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485319 prefixEnd_6485319 := by exact prefixLift 6485319
  have htrace : WordTrace (prefixWord ++ tailWord_6485319) baseStart_6485319 baseEnd_6485319 := by
    simpa [prefixWord, tailWord_6485319, baseEnd_6485319] using wordTrace_append hprefix tailTrace_6485319
  have hstable : (prefixWord ++ tailWord_6485319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485319).length < 2 ^ (prefixWord ++ tailWord_6485319).sum := by decide
  have hdescent : baseEnd_6485319 < baseStart_6485319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485326 : List Nat := [4, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_6485326 : Nat := 118140960795 + 6485326 * 2 ^ 59
def prefixEnd_6485326 : Nat := 4983230072969 + 3 ^ 40 * 6485326 * 2
def baseEnd_6485326 : Nat := 3330089439100598365899535

theorem tailTrace_6485326 : CollatzResearch.WordTrace tailWord_6485326 prefixEnd_6485326 3330089439100598365899535 := by
  unfold tailWord_6485326
  simp only [CollatzResearch.WordTrace]
  refine ⟨29567408962847372793116479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157692847801852654896621221 29567408962847372793116479)
  ·
    refine ⟨44351113444271059189674719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29567408962847372793116479 44351113444271059189674719)
    ·
      refine ⟨66526670166406588784512079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44351113444271059189674719 66526670166406588784512079)
      ·
        refine ⟨99790005249609883176768119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66526670166406588784512079 99790005249609883176768119)
        ·
          refine ⟨149685007874414824765152179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99790005249609883176768119 149685007874414824765152179)
          ·
            refine ⟨224527511811622237147728269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149685007874414824765152179 224527511811622237147728269)
            ·
              refine ⟨84197816929358338930398101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224527511811622237147728269 84197816929358338930398101)
              ·
                refine ⟨3946772668563672137362411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84197816929358338930398101 3946772668563672137362411)
                ·
                  refine ⟨5920159002845508206043617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946772668563672137362411 5920159002845508206043617)
                  ·
                    refine ⟨4440119252134131154532713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5920159002845508206043617 4440119252134131154532713)
                    ·
                      refine ⟨3330089439100598365899535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440119252134131154532713 3330089439100598365899535)
                      ·
                        rfl

theorem cell23_6485326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_6485326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485326 prefixEnd_6485326 := by exact prefixLift 6485326
  have htrace : WordTrace (prefixWord ++ tailWord_6485326) baseStart_6485326 baseEnd_6485326 := by
    simpa [prefixWord, tailWord_6485326, baseEnd_6485326] using wordTrace_append hprefix tailTrace_6485326
  have hstable : (prefixWord ++ tailWord_6485326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485326).length < 2 ^ (prefixWord ++ tailWord_6485326).sum := by decide
  have hdescent : baseEnd_6485326 < baseStart_6485326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485369 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 1, 3, 2]
def baseStart_6485369 : Nat := 118140960795 + 6485369 * 2 ^ 59
def prefixEnd_6485369 : Nat := 4983230072969 + 3 ^ 40 * 6485369 * 2
def baseEnd_6485369 : Nat := 3330111518768741697661837

theorem tailTrace_6485369 : CollatzResearch.WordTrace tailWord_6485369 prefixEnd_6485369 3330111518768741697661837 := by
  unfold tailWord_6485369
  simp only [CollatzResearch.WordTrace]
  refine ⟨236540840041623200688747161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157693893361082133792498107 236540840041623200688747161)
  ·
    refine ⟨177405630031217400516560371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236540840041623200688747161 177405630031217400516560371)
    ·
      refine ⟨266108445046826100774840557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177405630031217400516560371 266108445046826100774840557)
      ·
        refine ⟨99790666892559787790565209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266108445046826100774840557 99790666892559787790565209)
        ·
          refine ⟨74843000169419840842923907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99790666892559787790565209 74843000169419840842923907)
          ·
            refine ⟨112264500254129761264385861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74843000169419840842923907 112264500254129761264385861)
            ·
              refine ⟨21049593797649330237072349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112264500254129761264385861 21049593797649330237072349)
              ·
                refine ⟨7893597674118498838902131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21049593797649330237072349 7893597674118498838902131)
                ·
                  refine ⟨11840396511177748258353197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7893597674118498838902131 11840396511177748258353197)
                  ·
                    refine ⟨4440148691691655596882449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11840396511177748258353197 4440148691691655596882449)
                    ·
                      refine ⟨3330111518768741697661837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440148691691655596882449 3330111518768741697661837)
                      ·
                        rfl

theorem cell23_6485369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_6485369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485369 prefixEnd_6485369 := by exact prefixLift 6485369
  have htrace : WordTrace (prefixWord ++ tailWord_6485369) baseStart_6485369 baseEnd_6485369 := by
    simpa [prefixWord, tailWord_6485369, baseEnd_6485369] using wordTrace_append hprefix tailTrace_6485369
  have hstable : (prefixWord ++ tailWord_6485369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485369).length < 2 ^ (prefixWord ++ tailWord_6485369).sum := by decide
  have hdescent : baseEnd_6485369 < baseStart_6485369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485433 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 2, 2, 2]
def baseStart_6485433 : Nat := 118140960795 + 6485433 * 2 ^ 59
def prefixEnd_6485433 : Nat := 4983230072969 + 3 ^ 40 * 6485433 * 2
def baseEnd_6485433 : Nat := 3330144381530629447261543

theorem tailTrace_6485433 : CollatzResearch.WordTrace tailWord_6485433 prefixEnd_6485433 3330144381530629447261543 := by
  unfold tailWord_6485433
  simp only [CollatzResearch.WordTrace]
  refine ⟨236543174313391339619076953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157695449542260893079384635 236543174313391339619076953)
  ·
    refine ⟨177407380735043504714307715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236543174313391339619076953 177407380735043504714307715)
    ·
      refine ⟨266111071102565257071461573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177407380735043504714307715 266111071102565257071461573)
      ·
        refine ⟨49895825831730985700899045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266111071102565257071461573 49895825831730985700899045)
        ·
          refine ⟨9355467343449559818918571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49895825831730985700899045 9355467343449559818918571)
          ·
            refine ⟨14033201015174339728377857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9355467343449559818918571 14033201015174339728377857)
            ·
              refine ⟨10524900761380754796283393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14033201015174339728377857 10524900761380754796283393)
              ·
                refine ⟨7893675571035566097212545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10524900761380754796283393 7893675571035566097212545)
                ·
                  refine ⟨5920256678276674572909409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7893675571035566097212545 5920256678276674572909409)
                  ·
                    refine ⟨4440192508707505929682057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5920256678276674572909409 4440192508707505929682057)
                    ·
                      refine ⟨3330144381530629447261543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440192508707505929682057 3330144381530629447261543)
                      ·
                        rfl

theorem cell23_6485433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_6485433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485433 prefixEnd_6485433 := by exact prefixLift 6485433
  have htrace : WordTrace (prefixWord ++ tailWord_6485433) baseStart_6485433 baseEnd_6485433 := by
    simpa [prefixWord, tailWord_6485433, baseEnd_6485433] using wordTrace_append hprefix tailTrace_6485433
  have hstable : (prefixWord ++ tailWord_6485433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485433).length < 2 ^ (prefixWord ++ tailWord_6485433).sum := by decide
  have hdescent : baseEnd_6485433 < baseStart_6485433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485469 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6485469 : Nat := 118140960795 + 6485469 * 2 ^ 59
def prefixEnd_6485469 : Nat := 4983230072969 + 3 ^ 40 * 6485469 * 2
def baseEnd_6485469 : Nat := 1110054288944730435470459

theorem tailTrace_6485469 : CollatzResearch.WordTrace tailWord_6485469 prefixEnd_6485469 1110054288944730435470459 := by
  unfold tailWord_6485469
  simp only [CollatzResearch.WordTrace]
  refine ⟨236544487341260917767387461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157696324894173945178258307 236544487341260917767387461)
  ·
    refine ⟨44352091376486422081385149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236544487341260917767387461 44352091376486422081385149)
    ·
      refine ⟨16632034266182408280519431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44352091376486422081385149 16632034266182408280519431)
      ·
        refine ⟨24948051399273612420779147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16632034266182408280519431 24948051399273612420779147)
        ·
          refine ⟨37422077098910418631168721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24948051399273612420779147 37422077098910418631168721)
          ·
            refine ⟨28066557824182813973376541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37422077098910418631168721 28066557824182813973376541)
            ·
              refine ⟨10524959184068555240016203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28066557824182813973376541 10524959184068555240016203)
              ·
                refine ⟨15787438776102832860024305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10524959184068555240016203 15787438776102832860024305)
                ·
                  refine ⟨11840579082077124645018229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15787438776102832860024305 11840579082077124645018229)
                  ·
                    refine ⟨1110054288944730435470459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11840579082077124645018229 1110054288944730435470459)
                    ·
                      rfl

theorem cell23_6485469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6485469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485469 prefixEnd_6485469 := by exact prefixLift 6485469
  have htrace : WordTrace (prefixWord ++ tailWord_6485469) baseStart_6485469 baseEnd_6485469 := by
    simpa [prefixWord, tailWord_6485469, baseEnd_6485469] using wordTrace_append hprefix tailTrace_6485469
  have hstable : (prefixWord ++ tailWord_6485469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485469).length < 2 ^ (prefixWord ++ tailWord_6485469).sum := by decide
  have hdescent : baseEnd_6485469 < baseStart_6485469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485472 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_6485472 : Nat := 118140960795 + 6485472 * 2 ^ 59
def prefixEnd_6485472 : Nat := 4983230072969 + 3 ^ 40 * 6485472 * 2
def baseEnd_6485472 : Nat := 3330164407276154794673863

theorem tailTrace_6485472 : CollatzResearch.WordTrace tailWord_6485472 prefixEnd_6485472 3330164407276154794673863 := by
  unfold tailWord_6485472
  simp only [CollatzResearch.WordTrace]
  refine ⟨118272298380125024639873335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157696397840166699519831113 118272298380125024639873335)
  ·
    refine ⟨177408447570187536959810003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118272298380125024639873335 177408447570187536959810003)
    ·
      refine ⟨266112671355281305439715005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177408447570187536959810003 266112671355281305439715005)
      ·
        refine ⟨99792251758230489539893127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266112671355281305439715005 99792251758230489539893127)
        ·
          refine ⟨149688377637345734309839691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99792251758230489539893127 149688377637345734309839691)
          ·
            refine ⟨224532566456018601464759537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149688377637345734309839691 224532566456018601464759537)
            ·
              refine ⟨168399424842013951098569653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224532566456018601464759537 168399424842013951098569653)
              ·
                refine ⟨15787446078938807915490905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168399424842013951098569653 15787446078938807915490905)
                ·
                  refine ⟨11840584559204105936618179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15787446078938807915490905 11840584559204105936618179)
                  ·
                    refine ⟨17760876838806158904927269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11840584559204105936618179 17760876838806158904927269)
                    ·
                      refine ⟨3330164407276154794673863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17760876838806158904927269 3330164407276154794673863)
                      ·
                        rfl

theorem cell23_6485472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_6485472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485472 prefixEnd_6485472 := by exact prefixLift 6485472
  have htrace : WordTrace (prefixWord ++ tailWord_6485472) baseStart_6485472 baseEnd_6485472 := by
    simpa [prefixWord, tailWord_6485472, baseEnd_6485472] using wordTrace_append hprefix tailTrace_6485472
  have hstable : (prefixWord ++ tailWord_6485472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485472).length < 2 ^ (prefixWord ++ tailWord_6485472).sum := by decide
  have hdescent : baseEnd_6485472 < baseStart_6485472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485489 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 2, 4, 2]
def baseStart_6485489 : Nat := 118140960795 + 6485489 * 2 ^ 59
def prefixEnd_6485489 : Nat := 4983230072969 + 3 ^ 40 * 6485489 * 2
def baseEnd_6485489 : Nat := 3330173136447281228161285

theorem tailTrace_6485489 : CollatzResearch.WordTrace tailWord_6485489 prefixEnd_6485489 3330173136447281228161285 := by
  unfold tailWord_6485489
  simp only [CollatzResearch.WordTrace]
  refine ⟨236545216801188461183115521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157696811200792307455410347 236545216801188461183115521)
  ·
    refine ⟨177408912600891345887336641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236545216801188461183115521 177408912600891345887336641)
    ·
      refine ⟨133056684450668509415502481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177408912600891345887336641 133056684450668509415502481)
      ·
        refine ⟨99792513338001382061626861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133056684450668509415502481 99792513338001382061626861)
        ·
          refine ⟨37422192501750518273110073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99792513338001382061626861 37422192501750518273110073)
          ·
            refine ⟨28066644376312888704832555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37422192501750518273110073 28066644376312888704832555)
            ·
              refine ⟨42099966564469333057248833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28066644376312888704832555 42099966564469333057248833)
              ·
                refine ⟨31574974923351999792936625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42099966564469333057248833 31574974923351999792936625)
                ·
                  refine ⟨23681231192513999844702469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31574974923351999792936625 23681231192513999844702469)
                  ·
                    refine ⟨4440230848596374970881713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23681231192513999844702469 4440230848596374970881713)
                    ·
                      refine ⟨3330173136447281228161285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440230848596374970881713 3330173136447281228161285)
                      ·
                        rfl

theorem cell23_6485489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_6485489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485489 prefixEnd_6485489 := by exact prefixLift 6485489
  have htrace : WordTrace (prefixWord ++ tailWord_6485489) baseStart_6485489 baseEnd_6485489 := by
    simpa [prefixWord, tailWord_6485489, baseEnd_6485489] using wordTrace_append hprefix tailTrace_6485489
  have hstable : (prefixWord ++ tailWord_6485489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485489).length < 2 ^ (prefixWord ++ tailWord_6485489).sum := by decide
  have hdescent : baseEnd_6485489 < baseStart_6485489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485512 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 6]
def baseStart_6485512 : Nat := 118140960795 + 6485512 * 2 ^ 59
def prefixEnd_6485512 : Nat := 4983230072969 + 3 ^ 40 * 6485512 * 2
def baseEnd_6485512 : Nat := 370020549611370515352631

theorem tailTrace_6485512 : CollatzResearch.WordTrace tailWord_6485512 prefixEnd_6485512 370020549611370515352631 := by
  unfold tailWord_6485512
  simp only [CollatzResearch.WordTrace]
  refine ⟨118273027840052568055601395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157697370453403424074135193 118273027840052568055601395)
  ·
    refine ⟨177409541760078852083402093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118273027840052568055601395 177409541760078852083402093)
    ·
      refine ⟨66528578160029569531275785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177409541760078852083402093 66528578160029569531275785)
      ·
        refine ⟨49896433620022177148456839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66528578160029569531275785 49896433620022177148456839)
        ·
          refine ⟨74844650430033265722685259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49896433620022177148456839 74844650430033265722685259)
          ·
            refine ⟨112266975645049898584027889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74844650430033265722685259 112266975645049898584027889)
            ·
              refine ⟨84200231733787423938020917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112266975645049898584027889 84200231733787423938020917)
              ·
                refine ⟨7893771725042570994189461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84200231733787423938020917 7893771725042570994189461)
                ·
                  refine ⟨370020549611370515352631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7893771725042570994189461 370020549611370515352631)
                  ·
                    rfl

theorem cell23_6485512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 6].length) (baseStart_6485512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485512 prefixEnd_6485512 := by exact prefixLift 6485512
  have htrace : WordTrace (prefixWord ++ tailWord_6485512) baseStart_6485512 baseEnd_6485512 := by
    simpa [prefixWord, tailWord_6485512, baseEnd_6485512] using wordTrace_append hprefix tailTrace_6485512
  have hstable : (prefixWord ++ tailWord_6485512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485512).length < 2 ^ (prefixWord ++ tailWord_6485512).sum := by decide
  have hdescent : baseEnd_6485512 < baseStart_6485512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485550 : List Nat := [4, 1, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_6485550 : Nat := 118140960795 + 6485550 * 2 ^ 59
def prefixEnd_6485550 : Nat := 4983230072969 + 3 ^ 40 * 6485550 * 2
def baseEnd_6485550 : Nat := 1110068152922401829832835

theorem tailTrace_6485550 : CollatzResearch.WordTrace tailWord_6485550 prefixEnd_6485550 1110068152922401829832835 := by
  unfold tailWord_6485550
  simp only [CollatzResearch.WordTrace]
  refine ⟨29568430206745933575135763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157698294435978312400724069 29568430206745933575135763)
  ·
    refine ⟨44352645310118900362703645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29568430206745933575135763 44352645310118900362703645)
    ·
      refine ⟨16632241991294587636013867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44352645310118900362703645 16632241991294587636013867)
      ·
        refine ⟨24948362986941881454020801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16632241991294587636013867 24948362986941881454020801)
        ·
          refine ⟨18711272240206411090515601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24948362986941881454020801 18711272240206411090515601)
          ·
            refine ⟨14033454180154808317886701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18711272240206411090515601 14033454180154808317886701)
            ·
              refine ⟨5262545317558053119207513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14033454180154808317886701 5262545317558053119207513)
              ·
                refine ⟨3946908988168539839405635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5262545317558053119207513 3946908988168539839405635)
                ·
                  refine ⟨5920363482252809759108453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946908988168539839405635 5920363482252809759108453)
                  ·
                    refine ⟨1110068152922401829832835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5920363482252809759108453 1110068152922401829832835)
                    ·
                      rfl

theorem cell23_6485550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_6485550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485550 prefixEnd_6485550 := by exact prefixLift 6485550
  have htrace : WordTrace (prefixWord ++ tailWord_6485550) baseStart_6485550 baseEnd_6485550 := by
    simpa [prefixWord, tailWord_6485550, baseEnd_6485550] using wordTrace_append hprefix tailTrace_6485550
  have hstable : (prefixWord ++ tailWord_6485550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485550).length < 2 ^ (prefixWord ++ tailWord_6485550).sum := by decide
  have hdescent : baseEnd_6485550 < baseStart_6485550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485602 : List Nat := [3, 3, 2, 15]
def baseStart_6485602 : Nat := 118140960795 + 6485602 * 2 ^ 59
def prefixEnd_6485602 : Nat := 4983230072969 + 3 ^ 40 * 6485602 * 2
def baseEnd_6485602 : Nat := 1522739442049034881595

theorem tailTrace_6485602 : CollatzResearch.WordTrace tailWord_6485602 prefixEnd_6485602 1522739442049034881595 := by
  unfold tailWord_6485602
  simp only [CollatzResearch.WordTrace]
  refine ⟨59137334562444770370494765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157699558833186054321319373 59137334562444770370494765)
  ·
    refine ⟨22176500460916788888935537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59137334562444770370494765 22176500460916788888935537)
    ·
      refine ⟨16632375345687591666701653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22176500460916788888935537 16632375345687591666701653)
      ·
        refine ⟨1522739442049034881595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 16632375345687591666701653 1522739442049034881595)
        ·
          rfl

theorem cell23_6485602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 15].length) (baseStart_6485602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485602 prefixEnd_6485602 := by exact prefixLift 6485602
  have htrace : WordTrace (prefixWord ++ tailWord_6485602) baseStart_6485602 baseEnd_6485602 := by
    simpa [prefixWord, tailWord_6485602, baseEnd_6485602] using wordTrace_append hprefix tailTrace_6485602
  have hstable : (prefixWord ++ tailWord_6485602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485602).length < 2 ^ (prefixWord ++ tailWord_6485602).sum := by decide
  have hdescent : baseEnd_6485602 < baseStart_6485602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485632 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 2, 7]
def baseStart_6485632 : Nat := 118140960795 + 6485632 * 2 ^ 59
def prefixEnd_6485632 : Nat := 4983230072969 + 3 ^ 40 * 6485632 * 2
def baseEnd_6485632 : Nat := 1110082188060291389557709

theorem tailTrace_6485632 : CollatzResearch.WordTrace tailWord_6485632 prefixEnd_6485632 1110082188060291389557709 := by
  unfold tailWord_6485632
  simp only [CollatzResearch.WordTrace]
  refine ⟨118275216219835198302785575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157700288293113597737047433 118275216219835198302785575)
  ·
    refine ⟨177412824329752797454178363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118275216219835198302785575 177412824329752797454178363)
    ·
      refine ⟨266119236494629196181267545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177412824329752797454178363 266119236494629196181267545)
      ·
        refine ⟨199589427370971897135950659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266119236494629196181267545 199589427370971897135950659)
        ·
          refine ⟨299384141056457845703925989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199589427370971897135950659 299384141056457845703925989)
          ·
            refine ⟨56134526448085846069486123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299384141056457845703925989 56134526448085846069486123)
            ·
              refine ⟨84201789672128769104229185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56134526448085846069486123 84201789672128769104229185)
              ·
                refine ⟨63151342254096576828171889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84201789672128769104229185 63151342254096576828171889)
                ·
                  refine ⟨47363506690572432621128917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63151342254096576828171889 47363506690572432621128917)
                  ·
                    refine ⟨1110082188060291389557709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47363506690572432621128917 1110082188060291389557709)
                    ·
                      rfl

theorem cell23_6485632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_6485632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485632 prefixEnd_6485632 := by exact prefixLift 6485632
  have htrace : WordTrace (prefixWord ++ tailWord_6485632) baseStart_6485632 baseEnd_6485632 := by
    simpa [prefixWord, tailWord_6485632, baseEnd_6485632] using wordTrace_append hprefix tailTrace_6485632
  have hstable : (prefixWord ++ tailWord_6485632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485632).length < 2 ^ (prefixWord ++ tailWord_6485632).sum := by decide
  have hdescent : baseEnd_6485632 < baseStart_6485632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485636 : List Nat := [2, 3, 2, 1, 4, 1, 3, 7]
def baseStart_6485636 : Nat := 118140960795 + 6485636 * 2 ^ 59
def prefixEnd_6485636 : Nat := 4983230072969 + 3 ^ 40 * 6485636 * 2
def baseEnd_6485636 : Nat := 123342541411240450111967

theorem tailTrace_6485636 : CollatzResearch.WordTrace tailWord_6485636 prefixEnd_6485636 123342541411240450111967 := by
  unfold tailWord_6485636
  simp only [CollatzResearch.WordTrace]
  refine ⟨118275289165827952644358381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157700385554437270192477841 118275289165827952644358381)
  ·
    refine ⟨44353233437185482241634393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118275289165827952644358381 44353233437185482241634393)
    ·
      refine ⟨33264925077889111681225795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44353233437185482241634393 33264925077889111681225795)
      ·
        refine ⟨49897387616833667521838693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33264925077889111681225795 49897387616833667521838693)
        ·
          refine ⟨9355760178156312660344755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49897387616833667521838693 9355760178156312660344755)
          ·
            refine ⟨14033640267234468990517133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9355760178156312660344755 14033640267234468990517133)
            ·
              refine ⟨5262615100212925871443925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14033640267234468990517133 5262615100212925871443925)
              ·
                refine ⟨123342541411240450111967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5262615100212925871443925 123342541411240450111967)
                ·
                  rfl

theorem cell23_6485636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 7].length) (baseStart_6485636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485636 prefixEnd_6485636 := by exact prefixLift 6485636
  have htrace : WordTrace (prefixWord ++ tailWord_6485636) baseStart_6485636 baseEnd_6485636 := by
    simpa [prefixWord, tailWord_6485636, baseEnd_6485636] using wordTrace_append hprefix tailTrace_6485636
  have hstable : (prefixWord ++ tailWord_6485636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485636).length < 2 ^ (prefixWord ++ tailWord_6485636).sum := by decide
  have hdescent : baseEnd_6485636 < baseStart_6485636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485646 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_6485646 : Nat := 118140960795 + 6485646 * 2 ^ 59
def prefixEnd_6485646 : Nat := 4983230072969 + 3 ^ 40 * 6485646 * 2
def baseEnd_6485646 : Nat := 3330253752910037113898063

theorem tailTrace_6485646 : CollatzResearch.WordTrace tailWord_6485646 prefixEnd_6485646 3330253752910037113898063 := by
  unfold tailWord_6485646
  simp only [CollatzResearch.WordTrace]
  refine ⟨29568867882702459624572599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157700628707746451331053861 29568867882702459624572599)
  ·
    refine ⟨44353301824053689436858899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29568867882702459624572599 44353301824053689436858899)
    ·
      refine ⟨66529952736080534155288349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44353301824053689436858899 66529952736080534155288349)
      ·
        refine ⟨24948732276030200308233131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66529952736080534155288349 24948732276030200308233131)
        ·
          refine ⟨37423098414045300462349697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24948732276030200308233131 37423098414045300462349697)
          ·
            refine ⟨28067323810533975346762273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37423098414045300462349697 28067323810533975346762273)
            ·
              refine ⟨21050492857900481510071705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28067323810533975346762273 21050492857900481510071705)
              ·
                refine ⟨15787869643425361132553779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21050492857900481510071705 15787869643425361132553779)
                ·
                  refine ⟨23681804465138041698830669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15787869643425361132553779 23681804465138041698830669)
                  ·
                    refine ⟨8880676674426765637061501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23681804465138041698830669 8880676674426765637061501)
                    ·
                      refine ⟨3330253752910037113898063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8880676674426765637061501 3330253752910037113898063)
                      ·
                        rfl

theorem cell23_6485646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_6485646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485646 prefixEnd_6485646 := by exact prefixLift 6485646
  have htrace : WordTrace (prefixWord ++ tailWord_6485646) baseStart_6485646 baseEnd_6485646 := by
    simpa [prefixWord, tailWord_6485646, baseEnd_6485646] using wordTrace_append hprefix tailTrace_6485646
  have hstable : (prefixWord ++ tailWord_6485646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485646).length < 2 ^ (prefixWord ++ tailWord_6485646).sum := by decide
  have hdescent : baseEnd_6485646 < baseStart_6485646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485689 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 3]
def baseStart_6485689 : Nat := 118140960795 + 6485689 * 2 ^ 59
def prefixEnd_6485689 : Nat := 4983230072969 + 3 ^ 40 * 6485689 * 2
def baseEnd_6485689 : Nat := 3330275832578180445660365

theorem tailTrace_6485689 : CollatzResearch.WordTrace tailWord_6485689 prefixEnd_6485689 3330275832578180445660365 := by
  unfold tailWord_6485689
  simp only [CollatzResearch.WordTrace]
  refine ⟨236552511400463895340396121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157701674266975930226930747 236552511400463895340396121)
  ·
    refine ⟨177414383550347921505297091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236552511400463895340396121 177414383550347921505297091)
    ·
      refine ⟨266121575325521882257945637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177414383550347921505297091 266121575325521882257945637)
      ·
        refine ⟨49897795373535352923364807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266121575325521882257945637 49897795373535352923364807)
        ·
          refine ⟨74846693060303029385047211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49897795373535352923364807 74846693060303029385047211)
          ·
            refine ⟨112270039590454544077570817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74846693060303029385047211 112270039590454544077570817)
            ·
              refine ⟨84202529692840908058178113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112270039590454544077570817 84202529692840908058178113)
              ·
                refine ⟨63151897269630681043633585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84202529692840908058178113 63151897269630681043633585)
                ·
                  refine ⟨47363922952223010782725189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63151897269630681043633585 47363922952223010782725189)
                  ·
                    refine ⟨8880735553541814521760973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47363922952223010782725189 8880735553541814521760973)
                    ·
                      refine ⟨3330275832578180445660365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8880735553541814521760973 3330275832578180445660365)
                      ·
                        rfl

theorem cell23_6485689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_6485689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485689 prefixEnd_6485689 := by exact prefixLift 6485689
  have htrace : WordTrace (prefixWord ++ tailWord_6485689) baseStart_6485689 baseEnd_6485689 := by
    simpa [prefixWord, tailWord_6485689, baseEnd_6485689] using wordTrace_append hprefix tailTrace_6485689
  have hstable : (prefixWord ++ tailWord_6485689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485689).length < 2 ^ (prefixWord ++ tailWord_6485689).sum := by decide
  have hdescent : baseEnd_6485689 < baseStart_6485689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485698 : List Nat := [3, 5, 1, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6485698 : Nat := 118140960795 + 6485698 * 2 ^ 59
def prefixEnd_6485698 : Nat := 4983230072969 + 3 ^ 40 * 6485698 * 2
def baseEnd_6485698 : Nat := 3330280453904070910447825

theorem tailTrace_6485698 : CollatzResearch.WordTrace tailWord_6485698 prefixEnd_6485698 3330280453904070910447825 := by
  unfold tailWord_6485698
  simp only [CollatzResearch.WordTrace]
  refine ⟨59138209914357822469368437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157701893104954193251649165 59138209914357822469368437)
  ·
    refine ⟨5544207179471045856503291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59138209914357822469368437 5544207179471045856503291)
    ·
      refine ⟨8316310769206568784754937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5544207179471045856503291 8316310769206568784754937)
      ·
        refine ⟨6237233076904926588566203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8316310769206568784754937 6237233076904926588566203)
        ·
          refine ⟨9355849615357389882849305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6237233076904926588566203 9355849615357389882849305)
          ·
            refine ⟨7016887211518042412136979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9355849615357389882849305 7016887211518042412136979)
            ·
              refine ⟨10525330817277063618205469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7016887211518042412136979 10525330817277063618205469)
              ·
                refine ⟨3946999056478898856827051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10525330817277063618205469 3946999056478898856827051)
                ·
                  refine ⟨5920498584718348285240577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946999056478898856827051 5920498584718348285240577)
                  ·
                    refine ⟨4440373938538761213930433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5920498584718348285240577 4440373938538761213930433)
                    ·
                      refine ⟨3330280453904070910447825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440373938538761213930433 3330280453904070910447825)
                      ·
                        rfl

theorem cell23_6485698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6485698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485698 prefixEnd_6485698 := by exact prefixLift 6485698
  have htrace : WordTrace (prefixWord ++ tailWord_6485698) baseStart_6485698 baseEnd_6485698 := by
    simpa [prefixWord, tailWord_6485698, baseEnd_6485698] using wordTrace_append hprefix tailTrace_6485698
  have hstable : (prefixWord ++ tailWord_6485698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485698).length < 2 ^ (prefixWord ++ tailWord_6485698).sum := by decide
  have hdescent : baseEnd_6485698 < baseStart_6485698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485706 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_6485706 : Nat := 118140960795 + 6485706 * 2 ^ 59
def prefixEnd_6485706 : Nat := 4983230072969 + 3 ^ 40 * 6485706 * 2
def baseEnd_6485706 : Nat := 3330284561749306879147787

theorem tailTrace_6485706 : CollatzResearch.WordTrace tailWord_6485706 prefixEnd_6485706 3330284561749306879147787 := by
  unfold tailWord_6485706
  simp only [CollatzResearch.WordTrace]
  refine ⟨59138282860350576810941243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157702087627601538162509981 59138282860350576810941243)
  ·
    refine ⟨88707424290525865216411865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59138282860350576810941243 88707424290525865216411865)
    ·
      refine ⟨66530568217894398912308899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88707424290525865216411865 66530568217894398912308899)
      ·
        refine ⟨99795852326841598368463349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66530568217894398912308899 99795852326841598368463349)
        ·
          refine ⟨9355861155641399847043439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99795852326841598368463349 9355861155641399847043439)
          ·
            refine ⟨14033791733462099770565159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9355861155641399847043439 14033791733462099770565159)
            ·
              refine ⟨21050687600193149655847739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14033791733462099770565159 21050687600193149655847739)
              ·
                refine ⟨31576031400289724483771609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21050687600193149655847739 31576031400289724483771609)
                ·
                  refine ⟨23682023550217293362828707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31576031400289724483771609 23682023550217293362828707)
                  ·
                    refine ⟨35523035325325940044243061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23682023550217293362828707 35523035325325940044243061)
                    ·
                      refine ⟨3330284561749306879147787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35523035325325940044243061 3330284561749306879147787)
                      ·
                        rfl

theorem cell23_6485706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_6485706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485706 prefixEnd_6485706 := by exact prefixLift 6485706
  have htrace : WordTrace (prefixWord ++ tailWord_6485706) baseStart_6485706 baseEnd_6485706 := by
    simpa [prefixWord, tailWord_6485706, baseEnd_6485706] using wordTrace_append hprefix tailTrace_6485706
  have hstable : (prefixWord ++ tailWord_6485706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485706).length < 2 ^ (prefixWord ++ tailWord_6485706).sum := by decide
  have hdescent : baseEnd_6485706 < baseStart_6485706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485756 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_6485756 : Nat := 118140960795 + 6485756 * 2 ^ 59
def prefixEnd_6485756 : Nat := 4983230072969 + 3 ^ 40 * 6485756 * 2
def baseEnd_6485756 : Nat := 1110103411927343894507519

theorem tailTrace_6485756 : CollatzResearch.WordTrace tailWord_6485756 prefixEnd_6485756 1110103411927343894507519 := by
  unfold tailWord_6485756
  simp only [CollatzResearch.WordTrace]
  refine ⟨118277477545610582891542561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157703303394147443855390081 118277477545610582891542561)
  ·
    refine ⟨88708108159207937168656921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118277477545610582891542561 88708108159207937168656921)
    ·
      refine ⟨66531081119405952876492691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88708108159207937168656921 66531081119405952876492691)
      ·
        refine ⟨99796621679108929314739037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66531081119405952876492691 99796621679108929314739037)
        ·
          refine ⟨37423733129665848493027139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99796621679108929314739037 37423733129665848493027139)
          ·
            refine ⟨56135599694498772739540709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37423733129665848493027139 56135599694498772739540709)
            ·
              refine ⟨10525424942718519888663883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56135599694498772739540709 10525424942718519888663883)
              ·
                refine ⟨15788137414077779832995825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10525424942718519888663883 15788137414077779832995825)
                ·
                  refine ⟨11841103060558334874746869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15788137414077779832995825 11841103060558334874746869)
                  ·
                    refine ⟨1110103411927343894507519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11841103060558334874746869 1110103411927343894507519)
                    ·
                      rfl

theorem cell23_6485756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_6485756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485756 prefixEnd_6485756 := by exact prefixLift 6485756
  have htrace : WordTrace (prefixWord ++ tailWord_6485756) baseStart_6485756 baseEnd_6485756 := by
    simpa [prefixWord, tailWord_6485756, baseEnd_6485756] using wordTrace_append hprefix tailTrace_6485756
  have hstable : (prefixWord ++ tailWord_6485756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485756).length < 2 ^ (prefixWord ++ tailWord_6485756).sum := by decide
  have hdescent : baseEnd_6485756 < baseStart_6485756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485759 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_6485759 : Nat := 118140960795 + 6485759 * 2 ^ 59
def prefixEnd_6485759 : Nat := 4983230072969 + 3 ^ 40 * 6485759 * 2
def baseEnd_6485759 : Nat := 3330311776223995171785043

theorem tailTrace_6485759 : CollatzResearch.WordTrace tailWord_6485759 prefixEnd_6485759 3330311776223995171785043 := by
  unfold tailWord_6485759
  simp only [CollatzResearch.WordTrace]
  refine ⟨236555064510210297295444331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157703376340140198196962887 236555064510210297295444331)
  ·
    refine ⟨354832596765315445943166497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236555064510210297295444331 354832596765315445943166497)
    ·
      refine ⟨266124447573986584457374873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354832596765315445943166497 266124447573986584457374873)
      ·
        refine ⟨199593335680489938343031155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266124447573986584457374873 199593335680489938343031155)
        ·
          refine ⟨299390003520734907514546733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199593335680489938343031155 299390003520734907514546733)
          ·
            refine ⟨112271251320275590317955025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299390003520734907514546733 112271251320275590317955025)
            ·
              refine ⟨84203438490206692738466269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112271251320275590317955025 84203438490206692738466269)
              ·
                refine ⟨31576289433827509776924851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84203438490206692738466269 31576289433827509776924851)
                ·
                  refine ⟨47364434150741264665387277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31576289433827509776924851 47364434150741264665387277)
                  ·
                    refine ⟨17761662806527974249520229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47364434150741264665387277 17761662806527974249520229)
                    ·
                      refine ⟨3330311776223995171785043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17761662806527974249520229 3330311776223995171785043)
                      ·
                        rfl

theorem cell23_6485759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_6485759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485759 prefixEnd_6485759 := by exact prefixLift 6485759
  have htrace : WordTrace (prefixWord ++ tailWord_6485759) baseStart_6485759 baseEnd_6485759 := by
    simpa [prefixWord, tailWord_6485759, baseEnd_6485759] using wordTrace_append hprefix tailTrace_6485759
  have hstable : (prefixWord ++ tailWord_6485759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485759).length < 2 ^ (prefixWord ++ tailWord_6485759).sum := by decide
  have hdescent : baseEnd_6485759 < baseStart_6485759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485793 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_6485793 : Nat := 118140960795 + 6485793 * 2 ^ 59
def prefixEnd_6485793 : Nat := 4983230072969 + 3 ^ 40 * 6485793 * 2
def baseEnd_6485793 : Nat := 3330329234566248038759887

theorem tailTrace_6485793 : CollatzResearch.WordTrace tailWord_6485793 prefixEnd_6485793 3330329234566248038759887 := by
  unfold tailWord_6485793
  simp only [CollatzResearch.WordTrace]
  refine ⟨236556304592087121102182033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157704203061391414068121355 236556304592087121102182033)
  ·
    refine ⟨177417228444065340826636525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236556304592087121102182033 177417228444065340826636525)
    ·
      refine ⟨66531460666524502809988697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177417228444065340826636525 66531460666524502809988697)
      ·
        refine ⟨49898595499893377107491523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66531460666524502809988697 49898595499893377107491523)
        ·
          refine ⟨74847893249840065661237285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49898595499893377107491523 74847893249840065661237285)
          ·
            refine ⟨14033979984345012311481991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74847893249840065661237285 14033979984345012311481991)
            ·
              refine ⟨21050969976517518467222987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14033979984345012311481991 21050969976517518467222987)
              ·
                refine ⟨31576454964776277700834481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21050969976517518467222987 31576454964776277700834481)
                ·
                  refine ⟨23682341223582208275625861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31576454964776277700834481 23682341223582208275625861)
                  ·
                    refine ⟨4440438979421664051679849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23682341223582208275625861 4440438979421664051679849)
                    ·
                      refine ⟨3330329234566248038759887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440438979421664051679849 3330329234566248038759887)
                      ·
                        rfl

theorem cell23_6485793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_6485793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485793 prefixEnd_6485793 := by exact prefixLift 6485793
  have htrace : WordTrace (prefixWord ++ tailWord_6485793) baseStart_6485793 baseEnd_6485793 := by
    simpa [prefixWord, tailWord_6485793, baseEnd_6485793] using wordTrace_append hprefix tailTrace_6485793
  have hstable : (prefixWord ++ tailWord_6485793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485793).length < 2 ^ (prefixWord ++ tailWord_6485793).sum := by decide
  have hdescent : baseEnd_6485793 < baseStart_6485793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485813 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_6485813 : Nat := 118140960795 + 6485813 * 2 ^ 59
def prefixEnd_6485813 : Nat := 4983230072969 + 3 ^ 40 * 6485813 * 2
def baseEnd_6485813 : Nat := 3330339504179337960509795

theorem tailTrace_6485813 : CollatzResearch.WordTrace tailWord_6485813 prefixEnd_6485813 3330339504179337960509795 := by
  unfold tailWord_6485813
  simp only [CollatzResearch.WordTrace]
  refine ⟨236557034052014664517910093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157704689368009776345273395 236557034052014664517910093)
  ·
    refine ⟨88708887769505499194216285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236557034052014664517910093 88708887769505499194216285)
    ·
      refine ⟨33265832913564562197831107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88708887769505499194216285 33265832913564562197831107)
      ·
        refine ⟨49898749370346843296746661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33265832913564562197831107 49898749370346843296746661)
        ·
          refine ⟨9356015506940033118139999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49898749370346843296746661 9356015506940033118139999)
          ·
            refine ⟨14034023260410049677209999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9356015506940033118139999 14034023260410049677209999)
            ·
              refine ⟨21051034890615074515814999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14034023260410049677209999 21051034890615074515814999)
              ·
                refine ⟨31576552335922611773722499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21051034890615074515814999 31576552335922611773722499)
                ·
                  refine ⟨47364828503883917660583749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31576552335922611773722499 47364828503883917660583749)
                  ·
                    refine ⟨8880905344478234561359453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47364828503883917660583749 8880905344478234561359453)
                    ·
                      refine ⟨3330339504179337960509795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8880905344478234561359453 3330339504179337960509795)
                      ·
                        rfl

theorem cell23_6485813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_6485813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485813 prefixEnd_6485813 := by exact prefixLift 6485813
  have htrace : WordTrace (prefixWord ++ tailWord_6485813) baseStart_6485813 baseEnd_6485813 := by
    simpa [prefixWord, tailWord_6485813, baseEnd_6485813] using wordTrace_append hprefix tailTrace_6485813
  have hstable : (prefixWord ++ tailWord_6485813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485813).length < 2 ^ (prefixWord ++ tailWord_6485813).sum := by decide
  have hdescent : baseEnd_6485813 < baseStart_6485813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485837 : List Nat := [1, 6, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_6485837 : Nat := 118140960795 + 6485837 * 2 ^ 59
def prefixEnd_6485837 : Nat := 4983230072969 + 3 ^ 40 * 6485837 * 2
def baseEnd_6485837 : Nat := 1110117275905015288869895

theorem tailTrace_6485837 : CollatzResearch.WordTrace tailWord_6485837 prefixEnd_6485837 1110117275905015288869895 := by
  unfold tailWord_6485837
  simp only [CollatzResearch.WordTrace]
  refine ⟨236557909403927716616783765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157705272935951811077855843 236557909403927716616783765)
  ·
    refine ⟨11088652003309111716411739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236557909403927716616783765 11088652003309111716411739)
    ·
      refine ⟨16632978004963667574617609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11088652003309111716411739 16632978004963667574617609)
      ·
        refine ⟨12474733503722750680963207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16632978004963667574617609 12474733503722750680963207)
        ·
          refine ⟨18712100255584126021444811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12474733503722750680963207 18712100255584126021444811)
          ·
            refine ⟨28068150383376189032167217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18712100255584126021444811 28068150383376189032167217)
            ·
              refine ⟨21051112787532141774125413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28068150383376189032167217 21051112787532141774125413)
              ·
                refine ⟨3947083647662276582648515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21051112787532141774125413 3947083647662276582648515)
                ·
                  refine ⟨5920625471493414873972773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947083647662276582648515 5920625471493414873972773)
                  ·
                    refine ⟨1110117275905015288869895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5920625471493414873972773 1110117275905015288869895)
                    ·
                      rfl

theorem cell23_6485837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_6485837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485837 prefixEnd_6485837 := by exact prefixLift 6485837
  have htrace : WordTrace (prefixWord ++ tailWord_6485837) baseStart_6485837 baseEnd_6485837 := by
    simpa [prefixWord, tailWord_6485837, baseEnd_6485837] using wordTrace_append hprefix tailTrace_6485837
  have hstable : (prefixWord ++ tailWord_6485837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485837).length < 2 ^ (prefixWord ++ tailWord_6485837).sum := by decide
  have hdescent : baseEnd_6485837 < baseStart_6485837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485863 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 1, 5]
def baseStart_6485863 : Nat := 118140960795 + 6485863 * 2 ^ 59
def prefixEnd_6485863 : Nat := 4983230072969 + 3 ^ 40 * 6485863 * 2
def baseEnd_6485863 : Nat := 1110121726070687588294855

theorem tailTrace_6485863 : CollatzResearch.WordTrace tailWord_6485863 prefixEnd_6485863 1110121726070687588294855 := by
  unfold tailWord_6485863
  simp only [CollatzResearch.WordTrace]
  refine ⟨236558857701833523057230243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157705905134555682038153495 236558857701833523057230243)
  ·
    refine ⟨354838286552750284585845365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236558857701833523057230243 354838286552750284585845365)
    ·
      refine ⟨33266089364320339179923003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 354838286552750284585845365 33266089364320339179923003)
      ·
        refine ⟨49899134046480508769884505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33266089364320339179923003 49899134046480508769884505)
        ·
          refine ⟨37424350534860381577413379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49899134046480508769884505 37424350534860381577413379)
          ·
            refine ⟨56136525802290572366120069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37424350534860381577413379 56136525802290572366120069)
            ·
              refine ⟨10525598587929482318647513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56136525802290572366120069 10525598587929482318647513)
              ·
                refine ⟨7894198940947111738985635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10525598587929482318647513 7894198940947111738985635)
                ·
                  refine ⟨11841298411420667608478453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894198940947111738985635 11841298411420667608478453)
                  ·
                    refine ⟨1110121726070687588294855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11841298411420667608478453 1110121726070687588294855)
                    ·
                      rfl

theorem cell23_6485863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_6485863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485863 prefixEnd_6485863 := by exact prefixLift 6485863
  have htrace : WordTrace (prefixWord ++ tailWord_6485863) baseStart_6485863 baseEnd_6485863 := by
    simpa [prefixWord, tailWord_6485863, baseEnd_6485863] using wordTrace_append hprefix tailTrace_6485863
  have hstable : (prefixWord ++ tailWord_6485863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485863).length < 2 ^ (prefixWord ++ tailWord_6485863).sum := by decide
  have hdescent : baseEnd_6485863 < baseStart_6485863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485870 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_6485870 : Nat := 118140960795 + 6485870 * 2 ^ 59
def prefixEnd_6485870 : Nat := 4983230072969 + 3 ^ 40 * 6485870 * 2
def baseEnd_6485870 : Nat := 3330368772576644237497033

theorem tailTrace_6485870 : CollatzResearch.WordTrace tailWord_6485870 prefixEnd_6485870 3330368772576644237497033 := by
  unfold tailWord_6485870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29569889126601020406591883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157706075341872108835156709 29569889126601020406591883)
  ·
    refine ⟨44354833689901530609887825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29569889126601020406591883 44354833689901530609887825)
    ·
      refine ⟨33266125267426147957415869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44354833689901530609887825 33266125267426147957415869)
      ·
        refine ⟨12474796975284805484030951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33266125267426147957415869 12474796975284805484030951)
        ·
          refine ⟨18712195462927208226046427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12474796975284805484030951 18712195462927208226046427)
          ·
            refine ⟨28068293194390812339069641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18712195462927208226046427 28068293194390812339069641)
            ·
              refine ⟨21051219895793109254302231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28068293194390812339069641 21051219895793109254302231)
              ·
                refine ⟨31576829843689663881453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21051219895793109254302231 31576829843689663881453347)
                ·
                  refine ⟨47365244765534495822180021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31576829843689663881453347 47365244765534495822180021)
                  ·
                    refine ⟨4440491696768858983329377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47365244765534495822180021 4440491696768858983329377)
                    ·
                      refine ⟨3330368772576644237497033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440491696768858983329377 3330368772576644237497033)
                      ·
                        rfl

theorem cell23_6485870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_6485870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485870 prefixEnd_6485870 := by exact prefixLift 6485870
  have htrace : WordTrace (prefixWord ++ tailWord_6485870) baseStart_6485870 baseEnd_6485870 := by
    simpa [prefixWord, tailWord_6485870, baseEnd_6485870] using wordTrace_append hprefix tailTrace_6485870
  have hstable : (prefixWord ++ tailWord_6485870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485870).length < 2 ^ (prefixWord ++ tailWord_6485870).sum := by decide
  have hdescent : baseEnd_6485870 < baseStart_6485870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485893 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_6485893 : Nat := 118140960795 + 6485893 * 2 ^ 59
def prefixEnd_6485893 : Nat := 4983230072969 + 3 ^ 40 * 6485893 * 2
def baseEnd_6485893 : Nat := 1110126860877232549169809

theorem tailTrace_6485893 : CollatzResearch.WordTrace tailWord_6485893 prefixEnd_6485893 1110126860877232549169809 := by
  unfold tailWord_6485893
  simp only [CollatzResearch.WordTrace]
  refine ⟨236559951891724838180822333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157706634594483225453881555 236559951891724838180822333)
  ·
    refine ⟨88709981959396814317808375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236559951891724838180822333 88709981959396814317808375)
    ·
      refine ⟨133064972939095221476712563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88709981959396814317808375 133064972939095221476712563)
      ·
        refine ⟨199597459408642832215068845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133064972939095221476712563 199597459408642832215068845)
        ·
          refine ⟨74849047278241062080650817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199597459408642832215068845 74849047278241062080650817)
          ·
            refine ⟨56136785458680796560488113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74849047278241062080650817 56136785458680796560488113)
            ·
              refine ⟨42102589094010597420366085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56136785458680796560488113 42102589094010597420366085)
              ·
                refine ⟨7894235455126987016318641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42102589094010597420366085 7894235455126987016318641)
                ·
                  refine ⟨5920676591345240262238981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7894235455126987016318641 5920676591345240262238981)
                  ·
                    refine ⟨1110126860877232549169809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5920676591345240262238981 1110126860877232549169809)
                    ·
                      rfl

theorem cell23_6485893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_6485893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485893 prefixEnd_6485893 := by exact prefixLift 6485893
  have htrace : WordTrace (prefixWord ++ tailWord_6485893) baseStart_6485893 baseEnd_6485893 := by
    simpa [prefixWord, tailWord_6485893, baseEnd_6485893] using wordTrace_append hprefix tailTrace_6485893
  have hstable : (prefixWord ++ tailWord_6485893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485893).length < 2 ^ (prefixWord ++ tailWord_6485893).sum := by decide
  have hdescent : baseEnd_6485893 < baseStart_6485893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485937 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 1, 2, 3]
def baseStart_6485937 : Nat := 118140960795 + 6485937 * 2 ^ 59
def prefixEnd_6485937 : Nat := 4983230072969 + 3 ^ 40 * 6485937 * 2
def baseEnd_6485937 : Nat := 3330403175780495475359225

theorem tailTrace_6485937 : CollatzResearch.WordTrace tailWord_6485937 prefixEnd_6485937 3330403175780495475359225 := by
  unfold tailWord_6485937
  simp only [CollatzResearch.WordTrace]
  refine ⟨236561556703565433695424065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157707704469043622463616043 236561556703565433695424065)
  ·
    refine ⟨177421167527674075271568049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236561556703565433695424065 177421167527674075271568049)
    ·
      refine ⟨133065875645755556453676037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177421167527674075271568049 133065875645755556453676037)
      ·
        refine ⟨24949851683579166835064257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133065875645755556453676037 24949851683579166835064257)
        ·
          refine ⟨18712388762684375126298193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24949851683579166835064257 18712388762684375126298193)
          ·
            refine ⟨14034291572013281344723645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18712388762684375126298193 14034291572013281344723645)
            ·
              refine ⟨5262859339504980504271367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14034291572013281344723645 5262859339504980504271367)
              ·
                refine ⟨7894289009257470756407051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262859339504980504271367 7894289009257470756407051)
                ·
                  refine ⟨11841433513886206134610577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894289009257470756407051 11841433513886206134610577)
                  ·
                    refine ⟨8881075135414654600957933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11841433513886206134610577 8881075135414654600957933)
                    ·
                      refine ⟨3330403175780495475359225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8881075135414654600957933 3330403175780495475359225)
                      ·
                        rfl

theorem cell23_6485937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_6485937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485937 prefixEnd_6485937 := by exact prefixLift 6485937
  have htrace : WordTrace (prefixWord ++ tailWord_6485937) baseStart_6485937 baseEnd_6485937 := by
    simpa [prefixWord, tailWord_6485937, baseEnd_6485937] using wordTrace_append hprefix tailTrace_6485937
  have hstable : (prefixWord ++ tailWord_6485937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485937).length < 2 ^ (prefixWord ++ tailWord_6485937).sum := by decide
  have hdescent : baseEnd_6485937 < baseStart_6485937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485940 : List Nat := [2, 5, 2, 1, 3, 10]
def baseStart_6485940 : Nat := 118140960795 + 6485940 * 2 ^ 59
def prefixEnd_6485940 : Nat := 4983230072969 + 3 ^ 40 * 6485940 * 2
def baseEnd_6485940 : Nat := 13705369202561559521077

theorem tailTrace_6485940 : CollatzResearch.WordTrace tailWord_6485940 prefixEnd_6485940 13705369202561559521077 := by
  unfold tailWord_6485940
  simp only [CollatzResearch.WordTrace]
  refine ⟨118280833061277282603891637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157707777415036376805188849 118280833061277282603891637)
  ·
    refine ⟨11088828099494745244114841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118280833061277282603891637 11088828099494745244114841)
    ·
      refine ⟨8316621074621058933086131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11088828099494745244114841 8316621074621058933086131)
      ·
        refine ⟨12474931611931588399629197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8316621074621058933086131 12474931611931588399629197)
        ·
          refine ⟨4678099354474345649860949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12474931611931588399629197 4678099354474345649860949)
          ·
            refine ⟨13705369202561559521077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4678099354474345649860949 13705369202561559521077)
            ·
              rfl

theorem cell23_6485940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 10].length) (baseStart_6485940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485940 prefixEnd_6485940 := by exact prefixLift 6485940
  have htrace : WordTrace (prefixWord ++ tailWord_6485940) baseStart_6485940 baseEnd_6485940 := by
    simpa [prefixWord, tailWord_6485940, baseEnd_6485940] using wordTrace_append hprefix tailTrace_6485940
  have hstable : (prefixWord ++ tailWord_6485940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485940).length < 2 ^ (prefixWord ++ tailWord_6485940).sum := by decide
  have hdescent : baseEnd_6485940 < baseStart_6485940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6485960 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_6485960 : Nat := 118140960795 + 6485960 * 2 ^ 59
def prefixEnd_6485960 : Nat := 4983230072969 + 3 ^ 40 * 6485960 * 2
def baseEnd_6485960 : Nat := 3330414985835548885371619

theorem tailTrace_6485960 : CollatzResearch.WordTrace tailWord_6485960 prefixEnd_6485960 3330414985835548885371619 := by
  unfold tailWord_6485960
  simp only [CollatzResearch.WordTrace]
  refine ⟨118281197791241054311755667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157708263721654739082340889 118281197791241054311755667)
  ·
    refine ⟨177421796686861581467633501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118281197791241054311755667 177421796686861581467633501)
    ·
      refine ⟨66533173757573093050362563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177421796686861581467633501 66533173757573093050362563)
      ·
        refine ⟨99799760636359639575543845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66533173757573093050362563 99799760636359639575543845)
        ·
          refine ⟨18712455119317432420414471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99799760636359639575543845 18712455119317432420414471)
          ·
            refine ⟨28068682678976148630621707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18712455119317432420414471 28068682678976148630621707)
            ·
              refine ⟨42103024018464222945932561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28068682678976148630621707 42103024018464222945932561)
              ·
                refine ⟨31577268013848167209449421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42103024018464222945932561 31577268013848167209449421)
                ·
                  refine ⟨11841475505193062703543533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31577268013848167209449421 11841475505193062703543533)
                  ·
                    refine ⟨4440553314447398513828825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11841475505193062703543533 4440553314447398513828825)
                    ·
                      refine ⟨3330414985835548885371619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440553314447398513828825 3330414985835548885371619)
                      ·
                        rfl

theorem cell23_6485960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_6485960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6485960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6485960 prefixEnd_6485960 := by exact prefixLift 6485960
  have htrace : WordTrace (prefixWord ++ tailWord_6485960) baseStart_6485960 baseEnd_6485960 := by
    simpa [prefixWord, tailWord_6485960, baseEnd_6485960] using wordTrace_append hprefix tailTrace_6485960
  have hstable : (prefixWord ++ tailWord_6485960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6485960).length < 2 ^ (prefixWord ++ tailWord_6485960).sum := by decide
  have hdescent : baseEnd_6485960 < baseStart_6485960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6485960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486024 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_6486024 : Nat := 118140960795 + 6486024 * 2 ^ 59
def prefixEnd_6486024 : Nat := 4983230072969 + 3 ^ 40 * 6486024 * 2
def baseEnd_6486024 : Nat := 3330447848597436634971325

theorem tailTrace_6486024 : CollatzResearch.WordTrace tailWord_6486024 prefixEnd_6486024 3330447848597436634971325 := by
  unfold tailWord_6486024
  simp only [CollatzResearch.WordTrace]
  refine ⟨118282364927125123776920563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157709819902833498369227417 118282364927125123776920563)
  ·
    refine ⟨177423547390687685665380845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118282364927125123776920563 177423547390687685665380845)
    ·
      refine ⟨66533830271507882124517817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177423547390687685665380845 66533830271507882124517817)
      ·
        refine ⟨49900372703630911593388363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66533830271507882124517817 49900372703630911593388363)
        ·
          refine ⟨74850559055446367390082545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49900372703630911593388363 74850559055446367390082545)
          ·
            refine ⟨56137919291584775542561909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74850559055446367390082545 56137919291584775542561909)
            ·
              refine ⟨5262929933586072707115179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56137919291584775542561909 5262929933586072707115179)
              ·
                refine ⟨7894394900379109060672769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262929933586072707115179 7894394900379109060672769)
                ·
                  refine ⟨5920796175284331795504577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7894394900379109060672769 5920796175284331795504577)
                  ·
                    refine ⟨4440597131463248846628433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5920796175284331795504577 4440597131463248846628433)
                    ·
                      refine ⟨3330447848597436634971325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440597131463248846628433 3330447848597436634971325)
                      ·
                        rfl

theorem cell23_6486024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_6486024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486024 prefixEnd_6486024 := by exact prefixLift 6486024
  have htrace : WordTrace (prefixWord ++ tailWord_6486024) baseStart_6486024 baseEnd_6486024 := by
    simpa [prefixWord, tailWord_6486024, baseEnd_6486024] using wordTrace_append hprefix tailTrace_6486024
  have hstable : (prefixWord ++ tailWord_6486024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486024).length < 2 ^ (prefixWord ++ tailWord_6486024).sum := by decide
  have hdescent : baseEnd_6486024 < baseStart_6486024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486070 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6486070 : Nat := 118140960795 + 6486070 * 2 ^ 59
def prefixEnd_6486070 : Nat := 4983230072969 + 3 ^ 40 * 6486070 * 2
def baseEnd_6486070 : Nat := 3330471468707543454996113

theorem tailTrace_6486070 : CollatzResearch.WordTrace tailWord_6486070 prefixEnd_6486070 3330471468707543454996113 := by
  unfold tailWord_6486070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14785400475755224838125979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157710938408055731606677109 14785400475755224838125979)
  ·
    refine ⟨22178100713632837257188969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14785400475755224838125979 22178100713632837257188969)
    ·
      refine ⟨16633575535224627942891727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22178100713632837257188969 16633575535224627942891727)
      ·
        refine ⟨24950363302836941914337591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16633575535224627942891727 24950363302836941914337591)
        ·
          refine ⟨37425544954255412871506387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24950363302836941914337591 37425544954255412871506387)
          ·
            refine ⟨56138317431383119307259581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37425544954255412871506387 56138317431383119307259581)
            ·
              refine ⟨21051869036768669740222343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56138317431383119307259581 21051869036768669740222343)
              ·
                refine ⟨31577803555153004610333515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21051869036768669740222343 31577803555153004610333515)
                ·
                  refine ⟨47366705332729506915500273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31577803555153004610333515 47366705332729506915500273)
                  ·
                    refine ⟨35525028999547130186625205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47366705332729506915500273 35525028999547130186625205)
                    ·
                      refine ⟨3330471468707543454996113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35525028999547130186625205 3330471468707543454996113)
                      ·
                        rfl

theorem cell23_6486070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6486070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486070 prefixEnd_6486070 := by exact prefixLift 6486070
  have htrace : WordTrace (prefixWord ++ tailWord_6486070) baseStart_6486070 baseEnd_6486070 := by
    simpa [prefixWord, tailWord_6486070, baseEnd_6486070] using wordTrace_append hprefix tailTrace_6486070
  have hstable : (prefixWord ++ tailWord_6486070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486070).length < 2 ^ (prefixWord ++ tailWord_6486070).sum := by decide
  have hdescent : baseEnd_6486070 < baseStart_6486070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486083 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 3]
def baseStart_6486083 : Nat := 118140960795 + 6486083 * 2 ^ 59
def prefixEnd_6486083 : Nat := 4983230072969 + 3 ^ 40 * 6486083 * 2
def baseEnd_6486083 : Nat := 3330478143956051904133553

theorem tailTrace_6486083 : CollatzResearch.WordTrace tailWord_6486083 prefixEnd_6486083 3330478143956051904133553 := by
  unfold tailWord_6486083
  simp only [CollatzResearch.WordTrace]
  refine ⟨236566881761036500630238903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157711254507357667086825935 236566881761036500630238903)
  ·
    refine ⟨354850322641554750945358355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236566881761036500630238903 354850322641554750945358355)
    ·
      refine ⟨532275483962332126418037533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354850322641554750945358355 532275483962332126418037533)
      ·
        refine ⟨199603306485874547406764075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532275483962332126418037533 199603306485874547406764075)
        ·
          refine ⟨299404959728811821110146113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199603306485874547406764075 299404959728811821110146113)
          ·
            refine ⟨224553719796608865832609585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299404959728811821110146113 224553719796608865832609585)
            ·
              refine ⟨168415289847456649374457189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224553719796608865832609585 168415289847456649374457189)
              ·
                refine ⟨31577866846398121757710723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168415289847456649374457189 31577866846398121757710723)
                ·
                  refine ⟨47366800269597182636566085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31577866846398121757710723 47366800269597182636566085)
                  ·
                    refine ⟨8881275050549471744356141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47366800269597182636566085 8881275050549471744356141)
                    ·
                      refine ⟨3330478143956051904133553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8881275050549471744356141 3330478143956051904133553)
                      ·
                        rfl

theorem cell23_6486083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_6486083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486083 prefixEnd_6486083 := by exact prefixLift 6486083
  have htrace : WordTrace (prefixWord ++ tailWord_6486083) baseStart_6486083 baseEnd_6486083 := by
    simpa [prefixWord, tailWord_6486083, baseEnd_6486083] using wordTrace_append hprefix tailTrace_6486083
  have hstable : (prefixWord ++ tailWord_6486083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486083).length < 2 ^ (prefixWord ++ tailWord_6486083).sum := by decide
  have hdescent : baseEnd_6486083 < baseStart_6486083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486124 : List Nat := [2, 2, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_6486124 : Nat := 118140960795 + 6486124 * 2 ^ 59
def prefixEnd_6486124 : Nat := 4983230072969 + 3 ^ 40 * 6486124 * 2
def baseEnd_6486124 : Nat := 1110166398887628747906955

theorem tailTrace_6486124 : CollatzResearch.WordTrace tailWord_6486124 prefixEnd_6486124 1110166398887628747906955 := by
  unfold tailWord_6486124
  simp only [CollatzResearch.WordTrace]
  refine ⟨118284188576943982316240713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157712251435925309754987617 118284188576943982316240713)
  ·
    refine ⟨88713141432707986737180535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118284188576943982316240713 88713141432707986737180535)
    ·
      refine ⟨133069712149061980105770803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88713141432707986737180535 133069712149061980105770803)
      ·
        refine ⟨199604568223592970158656205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133069712149061980105770803 199604568223592970158656205)
        ·
          refine ⟨74851713083847363809496077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199604568223592970158656205 74851713083847363809496077)
          ·
            refine ⟨28069392406442761428561029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74851713083847363809496077 28069392406442761428561029)
            ·
              refine ⟨5263011076208017767855193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28069392406442761428561029 5263011076208017767855193)
              ·
                refine ⟨3947258307156013325891395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263011076208017767855193 3947258307156013325891395)
                ·
                  refine ⟨5920887460734019988837093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947258307156013325891395 5920887460734019988837093)
                  ·
                    refine ⟨1110166398887628747906955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5920887460734019988837093 1110166398887628747906955)
                    ·
                      rfl

theorem cell23_6486124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_6486124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486124 prefixEnd_6486124 := by exact prefixLift 6486124
  have htrace : WordTrace (prefixWord ++ tailWord_6486124) baseStart_6486124 baseEnd_6486124 := by
    simpa [prefixWord, tailWord_6486124, baseEnd_6486124] using wordTrace_append hprefix tailTrace_6486124
  have hstable : (prefixWord ++ tailWord_6486124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486124).length < 2 ^ (prefixWord ++ tailWord_6486124).sum := by decide
  have hdescent : baseEnd_6486124 < baseStart_6486124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486147 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 3]
def baseStart_6486147 : Nat := 118140960795 + 6486147 * 2 ^ 59
def prefixEnd_6486147 : Nat := 4983230072969 + 3 ^ 40 * 6486147 * 2
def baseEnd_6486147 : Nat := 3330511006717939653733259

theorem tailTrace_6486147 : CollatzResearch.WordTrace tailWord_6486147 prefixEnd_6486147 3330511006717939653733259 := by
  unfold tailWord_6486147
  simp only [CollatzResearch.WordTrace]
  refine ⟨236569216032804639560568695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157712810688536426373712463 236569216032804639560568695)
  ·
    refine ⟨354853824049206959340853043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236569216032804639560568695 354853824049206959340853043)
    ·
      refine ⟨532280736073810439011279565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354853824049206959340853043 532280736073810439011279565)
      ·
        refine ⟨199605276027678914629229837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532280736073810439011279565 199605276027678914629229837)
        ·
          refine ⟨74851978510379592985961189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199605276027678914629229837 74851978510379592985961189)
          ·
            refine ⟨14034745970696173684867723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74851978510379592985961189 14034745970696173684867723)
            ·
              refine ⟨21052118956044260527301585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14034745970696173684867723 21052118956044260527301585)
              ·
                refine ⟨15789089217033195395476189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21052118956044260527301585 15789089217033195395476189)
                ·
                  refine ⟨5920908456387448273303571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15789089217033195395476189 5920908456387448273303571)
                  ·
                    refine ⟨8881362684581172409955357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5920908456387448273303571 8881362684581172409955357)
                    ·
                      refine ⟨3330511006717939653733259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8881362684581172409955357 3330511006717939653733259)
                      ·
                        rfl

theorem cell23_6486147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_6486147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486147 prefixEnd_6486147 := by exact prefixLift 6486147
  have htrace : WordTrace (prefixWord ++ tailWord_6486147) baseStart_6486147 baseEnd_6486147 := by
    simpa [prefixWord, tailWord_6486147, baseEnd_6486147] using wordTrace_append hprefix tailTrace_6486147
  have hstable : (prefixWord ++ tailWord_6486147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486147).length < 2 ^ (prefixWord ++ tailWord_6486147).sum := by decide
  have hdescent : baseEnd_6486147 < baseStart_6486147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486167 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 1, 5]
def baseStart_6486167 : Nat := 118140960795 + 6486167 * 2 ^ 59
def prefixEnd_6486167 : Nat := 4983230072969 + 3 ^ 40 * 6486167 * 2
def baseEnd_6486167 : Nat := 1110173758777009858494389

theorem tailTrace_6486167 : CollatzResearch.WordTrace tailWord_6486167 prefixEnd_6486167 1110173758777009858494389 := by
  unfold tailWord_6486167
  simp only [CollatzResearch.WordTrace]
  refine ⟨236569945492732182976296755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157713296995154788650864503 236569945492732182976296755)
  ·
    refine ⟨354854918239098274464445133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236569945492732182976296755 354854918239098274464445133)
    ·
      refine ⟨133070594339661852924166925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354854918239098274464445133 133070594339661852924166925)
      ·
        refine ⟨49901472877373194846562597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133070594339661852924166925 49901472877373194846562597)
        ·
          refine ⟨9356526164507474033730487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49901472877373194846562597 9356526164507474033730487)
          ·
            refine ⟨14034789246761211050595731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9356526164507474033730487 14034789246761211050595731)
            ·
              refine ⟨21052183870141816575893597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14034789246761211050595731 21052183870141816575893597)
              ·
                refine ⟨7894568951303181215960099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21052183870141816575893597 7894568951303181215960099)
                ·
                  refine ⟨11841853426954771823940149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894568951303181215960099 11841853426954771823940149)
                  ·
                    refine ⟨1110173758777009858494389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11841853426954771823940149 1110173758777009858494389)
                    ·
                      rfl

theorem cell23_6486167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_6486167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486167 prefixEnd_6486167 := by exact prefixLift 6486167
  have htrace : WordTrace (prefixWord ++ tailWord_6486167) baseStart_6486167 baseEnd_6486167 := by
    simpa [prefixWord, tailWord_6486167, baseEnd_6486167] using wordTrace_append hprefix tailTrace_6486167
  have hstable : (prefixWord ++ tailWord_6486167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486167).length < 2 ^ (prefixWord ++ tailWord_6486167).sum := by decide
  have hdescent : baseEnd_6486167 < baseStart_6486167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486204 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_6486204 : Nat := 118140960795 + 6486204 * 2 ^ 59
def prefixEnd_6486204 : Nat := 4983230072969 + 3 ^ 40 * 6486204 * 2
def baseEnd_6486204 : Nat := 3330540275115245930720497

theorem tailTrace_6486204 : CollatzResearch.WordTrace tailWord_6486204 prefixEnd_6486204 3330540275115245930720497 := by
  unfold tailWord_6486204
  simp only [CollatzResearch.WordTrace]
  refine ⟨118285647496799069147696833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157714196662398758863595777 118285647496799069147696833)
  ·
    refine ⟨88714235622599301860772625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118285647496799069147696833 88714235622599301860772625)
    ·
      refine ⟨66535676716949476395579469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88714235622599301860772625 66535676716949476395579469)
      ·
        refine ⟨24950878768856053648342301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66535676716949476395579469 24950878768856053648342301)
        ·
          refine ⟨9356579538321020118128363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24950878768856053648342301 9356579538321020118128363)
          ·
            refine ⟨14034869307481530177192545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9356579538321020118128363 14034869307481530177192545)
            ·
              refine ⟨10526151980611147632894409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14034869307481530177192545 10526151980611147632894409)
              ·
                refine ⟨7894613985458360724670807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10526151980611147632894409 7894613985458360724670807)
                ·
                  refine ⟨11841920978187541087006211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894613985458360724670807 11841920978187541087006211)
                  ·
                    refine ⟨17762881467281311630509317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11841920978187541087006211 17762881467281311630509317)
                    ·
                      refine ⟨3330540275115245930720497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17762881467281311630509317 3330540275115245930720497)
                      ·
                        rfl

theorem cell23_6486204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_6486204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486204 prefixEnd_6486204 := by exact prefixLift 6486204
  have htrace : WordTrace (prefixWord ++ tailWord_6486204) baseStart_6486204 baseEnd_6486204 := by
    simpa [prefixWord, tailWord_6486204, baseEnd_6486204] using wordTrace_append hprefix tailTrace_6486204
  have hstable : (prefixWord ++ tailWord_6486204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486204).length < 2 ^ (prefixWord ++ tailWord_6486204).sum := by decide
  have hdescent : baseEnd_6486204 < baseStart_6486204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486281 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 1, 3, 2]
def baseStart_6486281 : Nat := 118140960795 + 6486281 * 2 ^ 59
def prefixEnd_6486281 : Nat := 4983230072969 + 3 ^ 40 * 6486281 * 2
def baseEnd_6486281 : Nat := 3330579813125642129457643

theorem tailTrace_6486281 : CollatzResearch.WordTrace tailWord_6486281 prefixEnd_6486281 3330579813125642129457643 := by
  unfold tailWord_6486281
  simp only [CollatzResearch.WordTrace]
  refine ⟨236574103414319180445946697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157716068942879453630631131 236574103414319180445946697)
  ·
    refine ⟨177430577560739385334460023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236574103414319180445946697 177430577560739385334460023)
    ·
      refine ⟨266145866341109078001690035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177430577560739385334460023 266145866341109078001690035)
      ·
        refine ⟨399218799511663617002535053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266145866341109078001690035 399218799511663617002535053)
        ·
          refine ⟨149707049816873856375950645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399218799511663617002535053 149707049816873856375950645)
          ·
            refine ⟨14035035920331924035245373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149707049816873856375950645 14035035920331924035245373)
            ·
              refine ⟨5263138470124471513217015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14035035920331924035245373 5263138470124471513217015)
              ·
                refine ⟨7894707705186707269825523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5263138470124471513217015 7894707705186707269825523)
                ·
                  refine ⟨11842061557780060904738285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894707705186707269825523 11842061557780060904738285)
                  ·
                    refine ⟨4440773084167522839276857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11842061557780060904738285 4440773084167522839276857)
                    ·
                      refine ⟨3330579813125642129457643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440773084167522839276857 3330579813125642129457643)
                      ·
                        rfl

theorem cell23_6486281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 1, 3, 2].length) (baseStart_6486281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486281 prefixEnd_6486281 := by exact prefixLift 6486281
  have htrace : WordTrace (prefixWord ++ tailWord_6486281) baseStart_6486281 baseEnd_6486281 := by
    simpa [prefixWord, tailWord_6486281, baseEnd_6486281] using wordTrace_append hprefix tailTrace_6486281
  have hstable : (prefixWord ++ tailWord_6486281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486281).length < 2 ^ (prefixWord ++ tailWord_6486281).sum := by decide
  have hdescent : baseEnd_6486281 < baseStart_6486281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486300 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 7]
def baseStart_6486300 : Nat := 118140960795 + 6486300 * 2 ^ 59
def prefixEnd_6486300 : Nat := 4983230072969 + 3 ^ 40 * 6486300 * 2
def baseEnd_6486300 : Nat := 370065507695341950568895

theorem tailTrace_6486300 : CollatzResearch.WordTrace tailWord_6486300 prefixEnd_6486300 370065507695341950568895 := by
  unfold tailWord_6486300
  simp only [CollatzResearch.WordTrace]
  refine ⟨118287398200625173345444177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157716530934166897793925569 118287398200625173345444177)
  ·
    refine ⟨88715548650468880009083133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118287398200625173345444177 88715548650468880009083133)
    ·
      refine ⟨33268330743925830003406175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88715548650468880009083133 33268330743925830003406175)
      ·
        refine ⟨49902496115888745005109263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33268330743925830003406175 49902496115888745005109263)
        ·
          refine ⟨74853744173833117507663895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49902496115888745005109263 74853744173833117507663895)
          ·
            refine ⟨112280616260749676261495843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74853744173833117507663895 112280616260749676261495843)
            ·
              refine ⟨168420924391124514392243765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112280616260749676261495843 168420924391124514392243765)
              ·
                refine ⟨15789461661667923224272853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168420924391124514392243765 15789461661667923224272853)
                ·
                  refine ⟨370065507695341950568895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15789461661667923224272853 370065507695341950568895)
                  ·
                    rfl

theorem cell23_6486300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_6486300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486300 prefixEnd_6486300 := by exact prefixLift 6486300
  have htrace : WordTrace (prefixWord ++ tailWord_6486300) baseStart_6486300 baseEnd_6486300 := by
    simpa [prefixWord, tailWord_6486300, baseEnd_6486300] using wordTrace_append hprefix tailTrace_6486300
  have hstable : (prefixWord ++ tailWord_6486300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486300).length < 2 ^ (prefixWord ++ tailWord_6486300).sum := by decide
  have hdescent : baseEnd_6486300 < baseStart_6486300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486334 : List Nat := [4, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_6486334 : Nat := 118140960795 + 6486334 * 2 ^ 59
def prefixEnd_6486334 : Nat := 4983230072969 + 3 ^ 40 * 6486334 * 2
def baseEnd_6486334 : Nat := 370067447511147824677211

theorem tailTrace_6486334 : CollatzResearch.WordTrace tailWord_6486334 prefixEnd_6486334 370067447511147824677211 := by
  unfold tailWord_6486334
  simp only [CollatzResearch.WordTrace]
  refine ⟨29572004560390896312203257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157717357655418113665084037 29572004560390896312203257)
  ·
    refine ⟨22179003420293172234152443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29572004560390896312203257 22179003420293172234152443)
    ·
      refine ⟨33268505130439758351228665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22179003420293172234152443 33268505130439758351228665)
      ·
        refine ⟨24951378847829818763421499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33268505130439758351228665 24951378847829818763421499)
        ·
          refine ⟨37427068271744728145132249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24951378847829818763421499 37427068271744728145132249)
          ·
            refine ⟨28070301203808546108849187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37427068271744728145132249 28070301203808546108849187)
            ·
              refine ⟨42105451805712819163273781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28070301203808546108849187 42105451805712819163273781)
              ·
                refine ⟨3947386106785576796556917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42105451805712819163273781 3947386106785576796556917)
                ·
                  refine ⟨370067447511147824677211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3947386106785576796556917 370067447511147824677211)
                  ·
                    rfl

theorem cell23_6486334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_6486334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486334 prefixEnd_6486334 := by exact prefixLift 6486334
  have htrace : WordTrace (prefixWord ++ tailWord_6486334) baseStart_6486334 baseEnd_6486334 := by
    simpa [prefixWord, tailWord_6486334, baseEnd_6486334] using wordTrace_append hprefix tailTrace_6486334
  have hstable : (prefixWord ++ tailWord_6486334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486334).length < 2 ^ (prefixWord ++ tailWord_6486334).sum := by decide
  have hdescent : baseEnd_6486334 < baseStart_6486334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486377 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 3, 4]
def baseStart_6486377 : Nat := 118140960795 + 6486377 * 2 ^ 59
def prefixEnd_6486377 : Nat := 4983230072969 + 3 ^ 40 * 6486377 * 2
def baseEnd_6486377 : Nat := 1110209702422824584619067

theorem tailTrace_6486377 : CollatzResearch.WordTrace tailWord_6486377 prefixEnd_6486377 1110209702422824584619067 := by
  unfold tailWord_6486377
  simp only [CollatzResearch.WordTrace]
  refine ⟨236577604821971388841441385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157718403214647592560960923 236577604821971388841441385)
  ·
    refine ⟨177433203616478541631081039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236577604821971388841441385 177433203616478541631081039)
    ·
      refine ⟨266149805424717812446621559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177433203616478541631081039 266149805424717812446621559)
      ·
        refine ⟨399224708137076718669932339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266149805424717812446621559 399224708137076718669932339)
        ·
          refine ⟨598837062205615078004898509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399224708137076718669932339 598837062205615078004898509)
          ·
            refine ⟨224563898327105654251836941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 598837062205615078004898509 224563898327105654251836941)
            ·
              refine ⟨84211461872664620344438853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224563898327105654251836941 84211461872664620344438853)
              ·
                refine ⟨15789649101124616314582285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84211461872664620344438853 15789649101124616314582285)
                ·
                  refine ⟨5921118412921731117968357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15789649101124616314582285 5921118412921731117968357)
                  ·
                    refine ⟨1110209702422824584619067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5921118412921731117968357 1110209702422824584619067)
                    ·
                      rfl

theorem cell23_6486377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_6486377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486377 prefixEnd_6486377 := by exact prefixLift 6486377
  have htrace : WordTrace (prefixWord ++ tailWord_6486377) baseStart_6486377 baseEnd_6486377 := by
    simpa [prefixWord, tailWord_6486377, baseEnd_6486377] using wordTrace_append hprefix tailTrace_6486377
  have hstable : (prefixWord ++ tailWord_6486377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486377).length < 2 ^ (prefixWord ++ tailWord_6486377).sum := by decide
  have hdescent : baseEnd_6486377 < baseStart_6486377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486404 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_6486404 : Nat := 118140960795 + 6486404 * 2 ^ 59
def prefixEnd_6486404 : Nat := 4983230072969 + 3 ^ 40 * 6486404 * 2
def baseEnd_6486404 : Nat := 3330642971246145148219577

theorem tailTrace_6486404 : CollatzResearch.WordTrace tailWord_6486404 prefixEnd_6486404 3330642971246145148219577 := by
  unfold tailWord_6486404
  simp only [CollatzResearch.WordTrace]
  refine ⟨118289294796436786226337133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157719059728582381635116177 118289294796436786226337133)
  ·
    refine ⟨44358485548663794834876425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118289294796436786226337133 44358485548663794834876425)
    ·
      refine ⟨33268864161497846126157319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44358485548663794834876425 33268864161497846126157319)
      ·
        refine ⟨49903296242246769189235979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33268864161497846126157319 49903296242246769189235979)
        ·
          refine ⟨74854944363370153783853969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49903296242246769189235979 74854944363370153783853969)
          ·
            refine ⟨56141208272527615337890477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74854944363370153783853969 56141208272527615337890477)
            ·
              refine ⟨21052953102197855751708929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56141208272527615337890477 21052953102197855751708929)
              ·
                refine ⟨15789714826648391813781697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21052953102197855751708929 15789714826648391813781697)
                ·
                  refine ⟨11842286119986293860336273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15789714826648391813781697 11842286119986293860336273)
                  ·
                    refine ⟨8881714589989720395252205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11842286119986293860336273 8881714589989720395252205)
                    ·
                      refine ⟨3330642971246145148219577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8881714589989720395252205 3330642971246145148219577)
                      ·
                        rfl

theorem cell23_6486404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_6486404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486404 prefixEnd_6486404 := by exact prefixLift 6486404
  have htrace : WordTrace (prefixWord ++ tailWord_6486404) baseStart_6486404 baseEnd_6486404 := by
    simpa [prefixWord, tailWord_6486404, baseEnd_6486404] using wordTrace_append hprefix tailTrace_6486404
  have hstable : (prefixWord ++ tailWord_6486404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486404).length < 2 ^ (prefixWord ++ tailWord_6486404).sum := by decide
  have hdescent : baseEnd_6486404 < baseStart_6486404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486407 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 6]
def baseStart_6486407 : Nat := 118140960795 + 6486407 * 2 ^ 59
def prefixEnd_6486407 : Nat := 4983230072969 + 3 ^ 40 * 6486407 * 2
def baseEnd_6486407 : Nat := 370071612409789848498007

theorem tailTrace_6486407 : CollatzResearch.WordTrace tailWord_6486407 prefixEnd_6486407 370071612409789848498007 := by
  unfold tailWord_6486407
  simp only [CollatzResearch.WordTrace]
  refine ⟨236578699011862703965033475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157719132674575135976688983 236578699011862703965033475)
  ·
    refine ⟨354868048517794055947550213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236578699011862703965033475 354868048517794055947550213)
    ·
      refine ⟨66537759097086385490165665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354868048517794055947550213 66537759097086385490165665)
      ·
        refine ⟨49903319322814789117624249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66537759097086385490165665 49903319322814789117624249)
        ·
          refine ⟨37427489492111091838218187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49903319322814789117624249 37427489492111091838218187)
          ·
            refine ⟨56141234238166637757327281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37427489492111091838218187 56141234238166637757327281)
            ·
              refine ⟨42105925678624978317995461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56141234238166637757327281 42105925678624978317995461)
              ·
                refine ⟨7894861064742183434624149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42105925678624978317995461 7894861064742183434624149)
                ·
                  refine ⟨370071612409789848498007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7894861064742183434624149 370071612409789848498007)
                  ·
                    rfl

theorem cell23_6486407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 6].length) (baseStart_6486407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486407 prefixEnd_6486407 := by exact prefixLift 6486407
  have htrace : WordTrace (prefixWord ++ tailWord_6486407) baseStart_6486407 baseEnd_6486407 := by
    simpa [prefixWord, tailWord_6486407, baseEnd_6486407] using wordTrace_append hprefix tailTrace_6486407
  have hstable : (prefixWord ++ tailWord_6486407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486407).length < 2 ^ (prefixWord ++ tailWord_6486407).sum := by decide
  have hdescent : baseEnd_6486407 < baseStart_6486407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486424 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 6]
def baseStart_6486424 : Nat := 118140960795 + 6486424 * 2 ^ 59
def prefixEnd_6486424 : Nat := 4983230072969 + 3 ^ 40 * 6486424 * 2
def baseEnd_6486424 : Nat := 370072582317692785552165

theorem tailTrace_6486424 : CollatzResearch.WordTrace tailWord_6486424 prefixEnd_6486424 370072582317692785552165 := by
  unfold tailWord_6486424
  simp only [CollatzResearch.WordTrace]
  refine ⟨118289659526400557934201163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157719546035200743912268217 118289659526400557934201163)
  ·
    refine ⟨177434489289600836901301745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118289659526400557934201163 177434489289600836901301745)
    ·
      refine ⟨133075866967200627675976309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177434489289600836901301745 133075866967200627675976309)
      ·
        refine ⟨12475862528175058844622779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133075866967200627675976309 12475862528175058844622779)
        ·
          refine ⟨18713793792262588266934169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12475862528175058844622779 18713793792262588266934169)
          ·
            refine ⟨14035345344196941200200627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18713793792262588266934169 14035345344196941200200627)
            ·
              refine ⟨21053018016295411800300941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14035345344196941200200627 21053018016295411800300941)
              ·
                refine ⟨7894881756110779425112853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21053018016295411800300941 7894881756110779425112853)
                ·
                  refine ⟨370072582317692785552165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7894881756110779425112853 370072582317692785552165)
                  ·
                    rfl

theorem cell23_6486424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 6].length) (baseStart_6486424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486424 prefixEnd_6486424 := by exact prefixLift 6486424
  have htrace : WordTrace (prefixWord ++ tailWord_6486424) baseStart_6486424 baseEnd_6486424 := by
    simpa [prefixWord, tailWord_6486424, baseEnd_6486424] using wordTrace_append hprefix tailTrace_6486424
  have hstable : (prefixWord ++ tailWord_6486424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486424).length < 2 ^ (prefixWord ++ tailWord_6486424).sum := by decide
  have hdescent : baseEnd_6486424 < baseStart_6486424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486437 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_6486437 : Nat := 118140960795 + 6486437 * 2 ^ 59
def prefixEnd_6486437 : Nat := 4983230072969 + 3 ^ 40 * 6486437 * 2
def baseEnd_6486437 : Nat := 1110219972035914506368975

theorem tailTrace_6486437 : CollatzResearch.WordTrace tailWord_6486437 prefixEnd_6486437 1110219972035914506368975 := by
  unfold tailWord_6486437
  simp only [CollatzResearch.WordTrace]
  refine ⟨236579793201754019088625565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157719862134502679392417043 236579793201754019088625565)
  ·
    refine ⟨88717422450657757158234587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236579793201754019088625565 88717422450657757158234587)
    ·
      refine ⟨133076133675986635737351881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88717422450657757158234587 133076133675986635737351881)
      ·
        refine ⟨99807100256989976803013911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133076133675986635737351881 99807100256989976803013911)
        ·
          refine ⟨149710650385484965204520867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99807100256989976803013911 149710650385484965204520867)
          ·
            refine ⟨224565975578227447806781301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149710650385484965204520867 224565975578227447806781301)
            ·
              refine ⟨21053060210458823231885747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224565975578227447806781301 21053060210458823231885747)
              ·
                refine ⟨31579590315688234847828621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21053060210458823231885747 31579590315688234847828621)
                ·
                  refine ⟨11842346368383088067935733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31579590315688234847828621 11842346368383088067935733)
                  ·
                    refine ⟨1110219972035914506368975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11842346368383088067935733 1110219972035914506368975)
                    ·
                      rfl

theorem cell23_6486437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_6486437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486437 prefixEnd_6486437 := by exact prefixLift 6486437
  have htrace : WordTrace (prefixWord ++ tailWord_6486437) baseStart_6486437 baseEnd_6486437 := by
    simpa [prefixWord, tailWord_6486437, baseEnd_6486437] using wordTrace_append hprefix tailTrace_6486437
  have hstable : (prefixWord ++ tailWord_6486437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486437).length < 2 ^ (prefixWord ++ tailWord_6486437).sum := by decide
  have hdescent : baseEnd_6486437 < baseStart_6486437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486461 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_6486461 : Nat := 118140960795 + 6486461 * 2 ^ 59
def prefixEnd_6486461 : Nat := 4983230072969 + 3 ^ 40 * 6486461 * 2
def baseEnd_6486461 : Nat := 3330672239643451425206815

theorem tailTrace_6486461 : CollatzResearch.WordTrace tailWord_6486461 prefixEnd_6486461 3330672239643451425206815 := by
  unfold tailWord_6486461
  simp only [CollatzResearch.WordTrace]
  refine ⟨236580668553667071187499237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157720445702444714124999491 236580668553667071187499237)
  ·
    refine ⟨44358875353812575847656107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236580668553667071187499237 44358875353812575847656107)
    ·
      refine ⟨66538313030718863771484161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44358875353812575847656107 66538313030718863771484161)
      ·
        refine ⟨49903734773039147828613121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66538313030718863771484161 49903734773039147828613121)
        ·
          refine ⟨37427801079779360871459841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49903734773039147828613121 37427801079779360871459841)
          ·
            refine ⟨28070850809834520653594881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37427801079779360871459841 28070850809834520653594881)
            ·
              refine ⟨21053138107375890490196161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28070850809834520653594881 21053138107375890490196161)
              ·
                refine ⟨15789853580531917867647121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21053138107375890490196161 15789853580531917867647121)
                ·
                  refine ⟨11842390185398938400735341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15789853580531917867647121 11842390185398938400735341)
                  ·
                    refine ⟨4440896319524601900275753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11842390185398938400735341 4440896319524601900275753)
                    ·
                      refine ⟨3330672239643451425206815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4440896319524601900275753 3330672239643451425206815)
                      ·
                        rfl

theorem cell23_6486461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_6486461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486461 prefixEnd_6486461 := by exact prefixLift 6486461
  have htrace : WordTrace (prefixWord ++ tailWord_6486461) baseStart_6486461 baseEnd_6486461 := by
    simpa [prefixWord, tailWord_6486461, baseEnd_6486461] using wordTrace_append hprefix tailTrace_6486461
  have hstable : (prefixWord ++ tailWord_6486461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486461).length < 2 ^ (prefixWord ++ tailWord_6486461).sum := by decide
  have hdescent : baseEnd_6486461 < baseStart_6486461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486484 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_6486484 : Nat := 118140960795 + 6486484 * 2 ^ 59
def prefixEnd_6486484 : Nat := 4983230072969 + 3 ^ 40 * 6486484 * 2
def baseEnd_6486484 : Nat := 1110228016566168278406403

theorem tailTrace_6486484 : CollatzResearch.WordTrace tailWord_6486484 prefixEnd_6486484 1110228016566168278406403 := by
  unfold tailWord_6486484
  simp only [CollatzResearch.WordTrace]
  refine ⟨118290753716291873057793253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157721004955055830743724337 118290753716291873057793253)
  ·
    refine ⟨22179516321804726198336235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118290753716291873057793253 22179516321804726198336235)
    ·
      refine ⟨33269274482707089297504353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22179516321804726198336235 33269274482707089297504353)
      ·
        refine ⟨24951955862030316973128265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33269274482707089297504353 24951955862030316973128265)
        ·
          refine ⟨18713966896522737729846199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24951955862030316973128265 18713966896522737729846199)
          ·
            refine ⟨28070950344784106594769299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18713966896522737729846199 28070950344784106594769299)
            ·
              refine ⟨42106425517176159892153949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28070950344784106594769299 42106425517176159892153949)
              ·
                refine ⟨15789909568941059959557731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42106425517176159892153949 15789909568941059959557731)
                ·
                  refine ⟨23684864353411589939336597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15789909568941059959557731 23684864353411589939336597)
                  ·
                    refine ⟨1110228016566168278406403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23684864353411589939336597 1110228016566168278406403)
                    ·
                      rfl

theorem cell23_6486484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_6486484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486484 prefixEnd_6486484 := by exact prefixLift 6486484
  have htrace : WordTrace (prefixWord ++ tailWord_6486484) baseStart_6486484 baseEnd_6486484 := by
    simpa [prefixWord, tailWord_6486484, baseEnd_6486484] using wordTrace_append hprefix tailTrace_6486484
  have hstable : (prefixWord ++ tailWord_6486484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486484).length < 2 ^ (prefixWord ++ tailWord_6486484).sum := by decide
  have hdescent : baseEnd_6486484 < baseStart_6486484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486504 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6486504 : Nat := 118140960795 + 6486504 * 2 ^ 59
def prefixEnd_6486504 : Nat := 4983230072969 + 3 ^ 40 * 6486504 * 2
def baseEnd_6486504 : Nat := 3330694319311594756969117

theorem tailTrace_6486504 : CollatzResearch.WordTrace tailWord_6486504 prefixEnd_6486504 3330694319311594756969117 := by
  unfold tailWord_6486504
  simp only [CollatzResearch.WordTrace]
  refine ⟨118291118446255644765657283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157721491261674193020876377 118291118446255644765657283)
  ·
    refine ⟨177436677669383467148485925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118291118446255644765657283 177436677669383467148485925)
    ·
      refine ⟨33269377063009400090341111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177436677669383467148485925 33269377063009400090341111)
      ·
        refine ⟨49904065594514100135511667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33269377063009400090341111 49904065594514100135511667)
        ·
          refine ⟨74856098391771150203267501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49904065594514100135511667 74856098391771150203267501)
          ·
            refine ⟨28071036896914181326225313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74856098391771150203267501 28071036896914181326225313)
            ·
              refine ⟨21053277672685635994668985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28071036896914181326225313 21053277672685635994668985)
              ·
                refine ⟨15789958254514226996001739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21053277672685635994668985 15789958254514226996001739)
                ·
                  refine ⟨23684937381771340494002609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15789958254514226996001739 23684937381771340494002609)
                  ·
                    refine ⟨17763703036328505370501957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23684937381771340494002609 17763703036328505370501957)
                    ·
                      refine ⟨3330694319311594756969117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17763703036328505370501957 3330694319311594756969117)
                      ·
                        rfl

theorem cell23_6486504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6486504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486504 prefixEnd_6486504 := by exact prefixLift 6486504
  have htrace : WordTrace (prefixWord ++ tailWord_6486504) baseStart_6486504 baseEnd_6486504 := by
    simpa [prefixWord, tailWord_6486504, baseEnd_6486504] using wordTrace_append hprefix tailTrace_6486504
  have hstable : (prefixWord ++ tailWord_6486504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486504).length < 2 ^ (prefixWord ++ tailWord_6486504).sum := by decide
  have hdescent : baseEnd_6486504 < baseStart_6486504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486514 : List Nat := [3, 2, 1, 4, 2, 1, 10]
def baseStart_6486514 : Nat := 118140960795 + 6486514 * 2 ^ 59
def prefixEnd_6486514 : Nat := 4983230072969 + 3 ^ 40 * 6486514 * 2
def baseEnd_6486514 : Nat := 41119746347137527380791

theorem tailTrace_6486514 : CollatzResearch.WordTrace tailWord_6486514 prefixEnd_6486514 41119746347137527380791 := by
  unfold tailWord_6486514
  simp only [CollatzResearch.WordTrace]
  refine ⟨59145650405618765309794649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157721734414983374159452397 59145650405618765309794649)
  ·
    refine ⟨44359237804214073982345987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59145650405618765309794649 44359237804214073982345987)
    ·
      refine ⟨66538856706321110973518981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44359237804214073982345987 66538856706321110973518981)
      ·
        refine ⟨12476035632435208307534809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66538856706321110973518981 12476035632435208307534809)
        ·
          refine ⟨9357026724326406230651107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12476035632435208307534809 9357026724326406230651107)
          ·
            refine ⟨14035540086489609345976661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9357026724326406230651107 14035540086489609345976661)
            ·
              refine ⟨41119746347137527380791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14035540086489609345976661 41119746347137527380791)
              ·
                rfl

theorem cell23_6486514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 10].length) (baseStart_6486514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486514 prefixEnd_6486514 := by exact prefixLift 6486514
  have htrace : WordTrace (prefixWord ++ tailWord_6486514) baseStart_6486514 baseEnd_6486514 := by
    simpa [prefixWord, tailWord_6486514, baseEnd_6486514] using wordTrace_append hprefix tailTrace_6486514
  have hstable : (prefixWord ++ tailWord_6486514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486514).length < 2 ^ (prefixWord ++ tailWord_6486514).sum := by decide
  have hdescent : baseEnd_6486514 < baseStart_6486514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486548 : List Nat := [2, 4, 3, 1, 1, 3, 2, 7]
def baseStart_6486548 : Nat := 118140960795 + 6486548 * 2 ^ 59
def prefixEnd_6486548 : Nat := 4983230072969 + 3 ^ 40 * 6486548 * 2
def baseEnd_6486548 : Nat := 123359885646681206845145

theorem tailTrace_6486548 : CollatzResearch.WordTrace tailWord_6486548 prefixEnd_6486548 123359885646681206845145 := by
  unfold tailWord_6486548
  simp only [CollatzResearch.WordTrace]
  refine ⟨118291920852175942522958149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157722561136234590030610865 118291920852175942522958149)
  ·
    refine ⟨22179735159782989223054653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118291920852175942522958149 22179735159782989223054653)
    ·
      refine ⟨8317400684918620958645495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22179735159782989223054653 8317400684918620958645495)
      ·
        refine ⟨12476101027377931437968243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8317400684918620958645495 12476101027377931437968243)
        ·
          refine ⟨18714151541066897156952365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476101027377931437968243 18714151541066897156952365)
          ·
            refine ⟨7017806827900086433857137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18714151541066897156952365 7017806827900086433857137)
            ·
              refine ⟨5263355120925064825392853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7017806827900086433857137 5263355120925064825392853)
              ·
                refine ⟨123359885646681206845145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5263355120925064825392853 123359885646681206845145)
                ·
                  rfl

theorem cell23_6486548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 7].length) (baseStart_6486548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486548 prefixEnd_6486548 := by exact prefixLift 6486548
  have htrace : WordTrace (prefixWord ++ tailWord_6486548) baseStart_6486548 baseEnd_6486548 := by
    simpa [prefixWord, tailWord_6486548, baseEnd_6486548] using wordTrace_append hprefix tailTrace_6486548
  have hstable : (prefixWord ++ tailWord_6486548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486548).length < 2 ^ (prefixWord ++ tailWord_6486548).sum := by decide
  have hdescent : baseEnd_6486548 < baseStart_6486548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486584 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_6486584 : Nat := 118140960795 + 6486584 * 2 ^ 59
def prefixEnd_6486584 : Nat := 4983230072969 + 3 ^ 40 * 6486584 * 2
def baseEnd_6486584 : Nat := 3330735397763954443968749

theorem tailTrace_6486584 : CollatzResearch.WordTrace tailWord_6486584 prefixEnd_6486584 3330735397763954443968749 := by
  unfold tailWord_6486584
  simp only [CollatzResearch.WordTrace]
  refine ⟨118292577366110731597113403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157723436488147642129484537 118292577366110731597113403)
  ·
    refine ⟨177438866049166097395670105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118292577366110731597113403 177438866049166097395670105)
    ·
      refine ⟨133079149536874573046752579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177438866049166097395670105 133079149536874573046752579)
      ·
        refine ⟨199618724305311859570128869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133079149536874573046752579 199618724305311859570128869)
        ·
          refine ⟨37428510807245973669399163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199618724305311859570128869 37428510807245973669399163)
          ·
            refine ⟨56142766210868960504098745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37428510807245973669399163 56142766210868960504098745)
            ·
              refine ⟨42107074658151720378074059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56142766210868960504098745 42107074658151720378074059)
              ·
                refine ⟨63160611987227580567111089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42107074658151720378074059 63160611987227580567111089)
                ·
                  refine ⟨47370458990420685425333317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63160611987227580567111089 47370458990420685425333317)
                  ·
                    refine ⟨8881961060703878517249997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47370458990420685425333317 8881961060703878517249997)
                    ·
                      refine ⟨3330735397763954443968749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8881961060703878517249997 3330735397763954443968749)
                      ·
                        rfl

theorem cell23_6486584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_6486584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486584 prefixEnd_6486584 := by exact prefixLift 6486584
  have htrace : WordTrace (prefixWord ++ tailWord_6486584) baseStart_6486584 baseEnd_6486584 := by
    simpa [prefixWord, tailWord_6486584, baseEnd_6486584] using wordTrace_append hprefix tailTrace_6486584
  have hstable : (prefixWord ++ tailWord_6486584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486584).length < 2 ^ (prefixWord ++ tailWord_6486584).sum := by decide
  have hdescent : baseEnd_6486584 < baseStart_6486584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486632 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6486632 : Nat := 118140960795 + 6486632 * 2 ^ 59
def prefixEnd_6486632 : Nat := 4983230072969 + 3 ^ 40 * 6486632 * 2
def baseEnd_6486632 : Nat := 3330760044835370256168529

theorem tailTrace_6486632 : CollatzResearch.WordTrace tailWord_6486632 prefixEnd_6486632 3330760044835370256168529 := by
  unfold tailWord_6486632
  simp only [CollatzResearch.WordTrace]
  refine ⟨118293452718023783695987075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157724603624031711594649433 118293452718023783695987075)
  ·
    refine ⟨177440179077035675543980613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118293452718023783695987075 177440179077035675543980613)
    ·
      refine ⟨33270033576944189164496365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177440179077035675543980613 33270033576944189164496365)
      ·
        refine ⟨12476262591354070936686137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33270033576944189164496365 12476262591354070936686137)
        ·
          refine ⟨9357196943515553202514603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12476262591354070936686137 9357196943515553202514603)
          ·
            refine ⟨14035795415273329803771905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9357196943515553202514603 14035795415273329803771905)
            ·
              refine ⟨10526846561454997352828929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14035795415273329803771905 10526846561454997352828929)
              ·
                refine ⟨7895134921091248014621697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10526846561454997352828929 7895134921091248014621697)
                ·
                  refine ⟨5921351190818436010966273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7895134921091248014621697 5921351190818436010966273)
                  ·
                    refine ⟨4441013393113827008224705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5921351190818436010966273 4441013393113827008224705)
                    ·
                      refine ⟨3330760044835370256168529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441013393113827008224705 3330760044835370256168529)
                      ·
                        rfl

theorem cell23_6486632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6486632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486632 prefixEnd_6486632 := by exact prefixLift 6486632
  have htrace : WordTrace (prefixWord ++ tailWord_6486632) baseStart_6486632 baseEnd_6486632 := by
    simpa [prefixWord, tailWord_6486632, baseEnd_6486632] using wordTrace_append hprefix tailTrace_6486632
  have hstable : (prefixWord ++ tailWord_6486632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486632).length < 2 ^ (prefixWord ++ tailWord_6486632).sum := by decide
  have hdescent : baseEnd_6486632 < baseStart_6486632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486638 : List Nat := [4, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_6486638 : Nat := 118140960795 + 6486638 * 2 ^ 59
def prefixEnd_6486638 : Nat := 4983230072969 + 3 ^ 40 * 6486638 * 2
def baseEnd_6486638 : Nat := 370084791746588581410389

theorem tailTrace_6486638 : CollatzResearch.WordTrace tailWord_6486638 prefixEnd_6486638 370084791746588581410389 := by
  unfold tailWord_6486638
  simp only [CollatzResearch.WordTrace]
  refine ⟨29573390534253228802086571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157724749516017220277795045 29573390534253228802086571)
  ·
    refine ⟨44360085801379843203129857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29573390534253228802086571 44360085801379843203129857)
    ·
      refine ⟨33270064351034882402347393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44360085801379843203129857 33270064351034882402347393)
      ·
        refine ⟨24952548263276161801760545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33270064351034882402347393 24952548263276161801760545)
        ·
          refine ⟨18714411197457121351320409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24952548263276161801760545 18714411197457121351320409)
          ·
            refine ⟨14035808398092841013490307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18714411197457121351320409 14035808398092841013490307)
            ·
              refine ⟨21053712597139261520235461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14035808398092841013490307 21053712597139261520235461)
              ·
                refine ⟨3947571111963611535044149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21053712597139261520235461 3947571111963611535044149)
                ·
                  refine ⟨370084791746588581410389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3947571111963611535044149 370084791746588581410389)
                  ·
                    rfl

theorem cell23_6486638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_6486638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486638 prefixEnd_6486638 := by exact prefixLift 6486638
  have htrace : WordTrace (prefixWord ++ tailWord_6486638) baseStart_6486638 baseEnd_6486638 := by
    simpa [prefixWord, tailWord_6486638, baseEnd_6486638] using wordTrace_append hprefix tailTrace_6486638
  have hstable : (prefixWord ++ tailWord_6486638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486638).length < 2 ^ (prefixWord ++ tailWord_6486638).sum := by decide
  have hdescent : baseEnd_6486638 < baseStart_6486638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486714 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_6486714 : Nat := 118140960795 + 6486714 * 2 ^ 59
def prefixEnd_6486714 : Nat := 4983230072969 + 3 ^ 40 * 6486714 * 2
def baseEnd_6486714 : Nat := 3330802150249038935343151

theorem tailTrace_6486714 : CollatzResearch.WordTrace tailWord_6486714 prefixEnd_6486714 3330802150249038935343151 := by
  unfold tailWord_6486714
  simp only [CollatzResearch.WordTrace]
  refine ⟨59147474055437623849114799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157726597481166996930972797 59147474055437623849114799)
  ·
    refine ⟨88721211083156435773672199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59147474055437623849114799 88721211083156435773672199)
    ·
      refine ⟨133081816624734653660508299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88721211083156435773672199 133081816624734653660508299)
      ·
        refine ⟨199622724937101980490762449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133081816624734653660508299 199622724937101980490762449)
        ·
          refine ⟨149717043702826485368071837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199622724937101980490762449 149717043702826485368071837)
          ·
            refine ⟨56143891388559932013026939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149717043702826485368071837 56143891388559932013026939)
            ·
              refine ⟨84215837082839898019540409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56143891388559932013026939 84215837082839898019540409)
              ·
                refine ⟨63161877812129923514655307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84215837082839898019540409 63161877812129923514655307)
                ·
                  refine ⟨94742816718194885271982961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63161877812129923514655307 94742816718194885271982961)
                  ·
                    refine ⟨71057112538646163953987221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94742816718194885271982961 71057112538646163953987221)
                    ·
                      refine ⟨3330802150249038935343151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71057112538646163953987221 3330802150249038935343151)
                      ·
                        rfl

theorem cell23_6486714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_6486714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486714 prefixEnd_6486714 := by exact prefixLift 6486714
  have htrace : WordTrace (prefixWord ++ tailWord_6486714) baseStart_6486714 baseEnd_6486714 := by
    simpa [prefixWord, tailWord_6486714, baseEnd_6486714] using wordTrace_append hprefix tailTrace_6486714
  have hstable : (prefixWord ++ tailWord_6486714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486714).length < 2 ^ (prefixWord ++ tailWord_6486714).sum := by decide
  have hdescent : baseEnd_6486714 < baseStart_6486714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486732 : List Nat := [2, 2, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_6486732 : Nat := 118140960795 + 6486732 * 2 ^ 59
def prefixEnd_6486732 : Nat := 4983230072969 + 3 ^ 40 * 6486732 * 2
def baseEnd_6486732 : Nat := 1110270464300273288306023

theorem tailTrace_6486732 : CollatzResearch.WordTrace tailWord_6486732 prefixEnd_6486732 1110270464300273288306023 := by
  unfold tailWord_6486732
  simp only [CollatzResearch.WordTrace]
  refine ⟨118295276367842642235307225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157727035157123522980409633 118295276367842642235307225)
  ·
    refine ⟨88721457275881981676480419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118295276367842642235307225 88721457275881981676480419)
    ·
      refine ⟨133082185913822972514720629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88721457275881981676480419 133082185913822972514720629)
      ·
        refine ⟨12476454929420903673255059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133082185913822972514720629 12476454929420903673255059)
        ·
          refine ⟨18714682394131355509882589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476454929420903673255059 18714682394131355509882589)
          ·
            refine ⟨7018005897799258316205971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18714682394131355509882589 7018005897799258316205971)
            ·
              refine ⟨10527008846698887474308957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018005897799258316205971 10527008846698887474308957)
              ·
                refine ⟨3947628317512082802865859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10527008846698887474308957 3947628317512082802865859)
                ·
                  refine ⟨5921442476268124204298789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947628317512082802865859 5921442476268124204298789)
                  ·
                    refine ⟨1110270464300273288306023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5921442476268124204298789 1110270464300273288306023)
                    ·
                      rfl

theorem cell23_6486732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_6486732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486732 prefixEnd_6486732 := by exact prefixLift 6486732
  have htrace : WordTrace (prefixWord ++ tailWord_6486732) baseStart_6486732 baseEnd_6486732 := by
    simpa [prefixWord, tailWord_6486732, baseEnd_6486732] using wordTrace_append hprefix tailTrace_6486732
  have hstable : (prefixWord ++ tailWord_6486732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486732).length < 2 ^ (prefixWord ++ tailWord_6486732).sum := by decide
  have hdescent : baseEnd_6486732 < baseStart_6486732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486755 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6486755 : Nat := 118140960795 + 6486755 * 2 ^ 59
def prefixEnd_6486755 : Nat := 4983230072969 + 3 ^ 40 * 6486755 * 2
def baseEnd_6486755 : Nat := 3330823202955873274930463

theorem tailTrace_6486755 : CollatzResearch.WordTrace tailWord_6486755 prefixEnd_6486755 3330823202955873274930463 := by
  unfold tailWord_6486755
  simp only [CollatzResearch.WordTrace]
  refine ⟨236591391614601959398701719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157727594409734639599134479 236591391614601959398701719)
  ·
    refine ⟨354887087421902939098052579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236591391614601959398701719 354887087421902939098052579)
    ·
      refine ⟨532330631132854408647078869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354887087421902939098052579 532330631132854408647078869)
      ·
        refine ⟨12476499167176275202665911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 532330631132854408647078869 12476499167176275202665911)
        ·
          refine ⟨18714748750764412803998867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476499167176275202665911 18714748750764412803998867)
          ·
            refine ⟨28072123126146619205998301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18714748750764412803998867 28072123126146619205998301)
            ·
              refine ⟨10527046172304982202249363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28072123126146619205998301 10527046172304982202249363)
              ·
                refine ⟨15790569258457473303374045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527046172304982202249363 15790569258457473303374045)
                ·
                  refine ⟨5921463471921552488765267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15790569258457473303374045 5921463471921552488765267)
                  ·
                    refine ⟨8882195207882328733147901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921463471921552488765267 8882195207882328733147901)
                    ·
                      refine ⟨3330823202955873274930463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8882195207882328733147901 3330823202955873274930463)
                      ·
                        rfl

theorem cell23_6486755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6486755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486755 prefixEnd_6486755 := by exact prefixLift 6486755
  have htrace : WordTrace (prefixWord ++ tailWord_6486755) baseStart_6486755 baseEnd_6486755 := by
    simpa [prefixWord, tailWord_6486755, baseEnd_6486755] using wordTrace_append hprefix tailTrace_6486755
  have hstable : (prefixWord ++ tailWord_6486755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486755).length < 2 ^ (prefixWord ++ tailWord_6486755).sum := by decide
  have hdescent : baseEnd_6486755 < baseStart_6486755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486778 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_6486778 : Nat := 118140960795 + 6486778 * 2 ^ 59
def prefixEnd_6486778 : Nat := 4983230072969 + 3 ^ 40 * 6486778 * 2
def baseEnd_6486778 : Nat := 3330835013010926684942857

theorem tailTrace_6486778 : CollatzResearch.WordTrace tailWord_6486778 prefixEnd_6486778 3330835013010926684942857 := by
  unfold tailWord_6486778
  simp only [CollatzResearch.WordTrace]
  refine ⟨59148057623379658581697247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157728153662345756217859325 59148057623379658581697247)
  ·
    refine ⟨88722086435069487872545871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59148057623379658581697247 88722086435069487872545871)
    ·
      refine ⟨133083129652604231808818807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88722086435069487872545871 133083129652604231808818807)
      ·
        refine ⟨199624694478906347713228211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133083129652604231808818807 199624694478906347713228211)
        ·
          refine ⟨299437041718359521569842317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199624694478906347713228211 299437041718359521569842317)
          ·
            refine ⟨112288890644384820588690869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299437041718359521569842317 112288890644384820588690869)
            ·
              refine ⟨10527083497911076930189769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112288890644384820588690869 10527083497911076930189769)
              ·
                refine ⟨7895312623433307697642327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10527083497911076930189769 7895312623433307697642327)
                ·
                  refine ⟨11842968935149961546463491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7895312623433307697642327 11842968935149961546463491)
                  ·
                    refine ⟨17764453402724942319695237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11842968935149961546463491 17764453402724942319695237)
                    ·
                      refine ⟨3330835013010926684942857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17764453402724942319695237 3330835013010926684942857)
                      ·
                        rfl

theorem cell23_6486778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_6486778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486778 prefixEnd_6486778 := by exact prefixLift 6486778
  have htrace : WordTrace (prefixWord ++ tailWord_6486778) baseStart_6486778 baseEnd_6486778 := by
    simpa [prefixWord, tailWord_6486778, baseEnd_6486778] using wordTrace_append hprefix tailTrace_6486778
  have hstable : (prefixWord ++ tailWord_6486778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486778).length < 2 ^ (prefixWord ++ tailWord_6486778).sum := by decide
  have hdescent : baseEnd_6486778 < baseStart_6486778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486782 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_6486782 : Nat := 118140960795 + 6486782 * 2 ^ 59
def prefixEnd_6486782 : Nat := 4983230072969 + 3 ^ 40 * 6486782 * 2
def baseEnd_6486782 : Nat := 3330837066933544669292839

theorem tailTrace_6486782 : CollatzResearch.WordTrace tailWord_6486782 prefixEnd_6486782 3330837066933544669292839 := by
  unfold tailWord_6486782
  simp only [CollatzResearch.WordTrace]
  refine ⟨29574047048188017876241825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157728250923669428673289733 29574047048188017876241825)
  ·
    refine ⟨22180535286141013407181369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29574047048188017876241825 22180535286141013407181369)
    ·
      refine ⟨16635401464605760055386027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22180535286141013407181369 16635401464605760055386027)
      ·
        refine ⟨24953102196908640083079041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16635401464605760055386027 24953102196908640083079041)
        ·
          refine ⟨18714826647681480062309281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24953102196908640083079041 18714826647681480062309281)
          ·
            refine ⟨14036119985761110046731961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18714826647681480062309281 14036119985761110046731961)
            ·
              refine ⟨10527089989320832535048971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14036119985761110046731961 10527089989320832535048971)
              ·
                refine ⟨15790634983981248802573457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527089989320832535048971 15790634983981248802573457)
                ·
                  refine ⟨11842976237985936601930093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15790634983981248802573457 11842976237985936601930093)
                  ·
                    refine ⟨4441116089244726225723785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11842976237985936601930093 4441116089244726225723785)
                    ·
                      refine ⟨3330837066933544669292839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441116089244726225723785 3330837066933544669292839)
                      ·
                        rfl

theorem cell23_6486782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_6486782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486782 prefixEnd_6486782 := by exact prefixLift 6486782
  have htrace : WordTrace (prefixWord ++ tailWord_6486782) baseStart_6486782 baseEnd_6486782 := by
    simpa [prefixWord, tailWord_6486782, baseEnd_6486782] using wordTrace_append hprefix tailTrace_6486782
  have hstable : (prefixWord ++ tailWord_6486782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486782).length < 2 ^ (prefixWord ++ tailWord_6486782).sum := by decide
  have hdescent : baseEnd_6486782 < baseStart_6486782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486818 : List Nat := [3, 3, 1, 1, 2, 4, 1, 8]
def baseStart_6486818 : Nat := 118140960795 + 6486818 * 2 ^ 59
def prefixEnd_6486818 : Nat := 4983230072969 + 3 ^ 40 * 6486818 * 2
def baseEnd_6486818 : Nat := 123365020453226167720099

theorem tailTrace_6486818 : CollatzResearch.WordTrace tailWord_6486818 prefixEnd_6486818 123365020453226167720099 := by
  unfold tailWord_6486818
  simp only [CollatzResearch.WordTrace]
  refine ⟨59148422353343430289561277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157729126275582480772163405 59148422353343430289561277)
  ·
    refine ⟨22180658382503786358585479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59148422353343430289561277 22180658382503786358585479)
    ·
      refine ⟨33270987573755679537878219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22180658382503786358585479 33270987573755679537878219)
      ·
        refine ⟨49906481360633519306817329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33270987573755679537878219 49906481360633519306817329)
        ·
          refine ⟨37429861020475139480112997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49906481360633519306817329 37429861020475139480112997)
          ·
            refine ⟨7018098941339088652521187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37429861020475139480112997 7018098941339088652521187)
            ·
              refine ⟨10527148412008632978781781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018098941339088652521187 10527148412008632978781781)
              ·
                refine ⟨123365020453226167720099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10527148412008632978781781 123365020453226167720099)
                ·
                  rfl

theorem cell23_6486818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 8].length) (baseStart_6486818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486818 prefixEnd_6486818 := by exact prefixLift 6486818
  have htrace : WordTrace (prefixWord ++ tailWord_6486818) baseStart_6486818 baseEnd_6486818 := by
    simpa [prefixWord, tailWord_6486818, baseEnd_6486818] using wordTrace_append hprefix tailTrace_6486818
  have hstable : (prefixWord ++ tailWord_6486818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486818).length < 2 ^ (prefixWord ++ tailWord_6486818).sum := by decide
  have hdescent : baseEnd_6486818 < baseStart_6486818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486828 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_6486828 : Nat := 118140960795 + 6486828 * 2 ^ 59
def prefixEnd_6486828 : Nat := 4983230072969 + 3 ^ 40 * 6486828 * 2
def baseEnd_6486828 : Nat := 3330860687043651489317627

theorem tailTrace_6486828 : CollatzResearch.WordTrace tailWord_6486828 prefixEnd_6486828 3330860687043651489317627 := by
  unfold tailWord_6486828
  simp only [CollatzResearch.WordTrace]
  refine ⟨118297027071668746433054569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157729369428891661910739425 118297027071668746433054569)
  ·
    refine ⟨88722770303751559824790927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118297027071668746433054569 88722770303751559824790927)
    ·
      refine ⟨133084155455627339737186391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88722770303751559824790927 133084155455627339737186391)
      ·
        refine ⟨199626233183441009605779587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133084155455627339737186391 199626233183441009605779587)
        ·
          refine ⟨299439349775161514408669381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199626233183441009605779587 299439349775161514408669381)
          ·
            refine ⟨56144878082842783951625509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299439349775161514408669381 56144878082842783951625509)
            ·
              refine ⟨10527164640533021990929783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56144878082842783951625509 10527164640533021990929783)
              ·
                refine ⟨15790746960799532986394675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527164640533021990929783 15790746960799532986394675)
                ·
                  refine ⟨23686120441199299479592013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15790746960799532986394675 23686120441199299479592013)
                  ·
                    refine ⟨8882295165449737304847005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23686120441199299479592013 8882295165449737304847005)
                    ·
                      refine ⟨3330860687043651489317627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8882295165449737304847005 3330860687043651489317627)
                      ·
                        rfl

theorem cell23_6486828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_6486828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486828 prefixEnd_6486828 := by exact prefixLift 6486828
  have htrace : WordTrace (prefixWord ++ tailWord_6486828) baseStart_6486828 baseEnd_6486828 := by
    simpa [prefixWord, tailWord_6486828, baseEnd_6486828] using wordTrace_append hprefix tailTrace_6486828
  have hstable : (prefixWord ++ tailWord_6486828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486828).length < 2 ^ (prefixWord ++ tailWord_6486828).sum := by decide
  have hdescent : baseEnd_6486828 < baseStart_6486828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486846 : List Nat := [4, 2, 1, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_6486846 : Nat := 118140960795 + 6486846 * 2 ^ 59
def prefixEnd_6486846 : Nat := 4983230072969 + 3 ^ 40 * 6486846 * 2
def baseEnd_6486846 : Nat := 3330869929695432418892545

theorem tailTrace_6486846 : CollatzResearch.WordTrace tailWord_6486846 prefixEnd_6486846 3330869929695432418892545 := by
  unfold tailWord_6486846
  simp only [CollatzResearch.WordTrace]
  refine ⟨29574338832159035242533049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157729807104848187960176261 29574338832159035242533049)
  ·
    refine ⟨22180754124119276431899787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29574338832159035242533049 22180754124119276431899787)
    ·
      refine ⟨33271131186178914647849681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22180754124119276431899787 33271131186178914647849681)
      ·
        refine ⟨24953348389634185985887261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33271131186178914647849681 24953348389634185985887261)
        ·
          refine ⟨9357505646112819744707723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24953348389634185985887261 9357505646112819744707723)
          ·
            refine ⟨14036258469169229617061585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9357505646112819744707723 14036258469169229617061585)
            ·
              refine ⟨10527193851876922212796189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14036258469169229617061585 10527193851876922212796189)
              ·
                refine ⟨3947697694453845829798571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10527193851876922212796189 3947697694453845829798571)
                ·
                  refine ⟨5921546541680768744697857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947697694453845829798571 5921546541680768744697857)
                  ·
                    refine ⟨4441159906260576558523393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5921546541680768744697857 4441159906260576558523393)
                    ·
                      refine ⟨3330869929695432418892545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441159906260576558523393 3330869929695432418892545)
                      ·
                        rfl

theorem cell23_6486846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_6486846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486846 prefixEnd_6486846 := by exact prefixLift 6486846
  have htrace : WordTrace (prefixWord ++ tailWord_6486846) baseStart_6486846 baseEnd_6486846 := by
    simpa [prefixWord, tailWord_6486846, baseEnd_6486846] using wordTrace_append hprefix tailTrace_6486846
  have hstable : (prefixWord ++ tailWord_6486846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486846).length < 2 ^ (prefixWord ++ tailWord_6486846).sum := by decide
  have hdescent : baseEnd_6486846 < baseStart_6486846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486881 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_6486881 : Nat := 118140960795 + 6486881 * 2 ^ 59
def prefixEnd_6486881 : Nat := 4983230072969 + 3 ^ 40 * 6486881 * 2
def baseEnd_6486881 : Nat := 3330887901518339781954883

theorem tailTrace_6486881 : CollatzResearch.WordTrace tailWord_6486881 prefixEnd_6486881 3330887901518339781954883 := by
  unfold tailWord_6486881
  simp only [CollatzResearch.WordTrace]
  refine ⟨236595987212145482917788497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157730658141430321945192331 236595987212145482917788497)
  ·
    refine ⟨177446990409109112188341373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236595987212145482917788497 177446990409109112188341373)
    ·
      refine ⟨66542621403415917070628015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177446990409109112188341373 66542621403415917070628015)
      ·
        refine ⟨99813932105123875605942023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66542621403415917070628015 99813932105123875605942023)
        ·
          refine ⟨149720898157685813408913035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99813932105123875605942023 149720898157685813408913035)
          ·
            refine ⟨224581347236528720113369553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149720898157685813408913035 224581347236528720113369553)
            ·
              refine ⟨168436010427396540085027165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224581347236528720113369553 168436010427396540085027165)
              ·
                refine ⟨63163503910273702531885187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168436010427396540085027165 63163503910273702531885187)
                ·
                  refine ⟨94745255865410553797827781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63163503910273702531885187 94745255865410553797827781)
                  ·
                    refine ⟨17764735474764478837092709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94745255865410553797827781 17764735474764478837092709)
                    ·
                      refine ⟨3330887901518339781954883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17764735474764478837092709 3330887901518339781954883)
                      ·
                        rfl

theorem cell23_6486881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_6486881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486881 prefixEnd_6486881 := by exact prefixLift 6486881
  have htrace : WordTrace (prefixWord ++ tailWord_6486881) baseStart_6486881 baseEnd_6486881 := by
    simpa [prefixWord, tailWord_6486881, baseEnd_6486881] using wordTrace_append hprefix tailTrace_6486881
  have hstable : (prefixWord ++ tailWord_6486881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486881).length < 2 ^ (prefixWord ++ tailWord_6486881).sum := by decide
  have hdescent : baseEnd_6486881 < baseStart_6486881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486885 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 1, 4, 2]
def baseStart_6486885 : Nat := 118140960795 + 6486885 * 2 ^ 59
def prefixEnd_6486885 : Nat := 4983230072969 + 3 ^ 40 * 6486885 * 2
def baseEnd_6486885 : Nat := 3330889955440957766304865

theorem tailTrace_6486885 : CollatzResearch.WordTrace tailWord_6486885 prefixEnd_6486885 3330889955440957766304865 := by
  unfold tailWord_6486885
  simp only [CollatzResearch.WordTrace]
  refine ⟨236596133104130991600934109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157730755402753994400622739 236596133104130991600934109)
  ·
    refine ⟨88723549914049121850350291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236596133104130991600934109 88723549914049121850350291)
    ·
      refine ⟨133085324871073682775525437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88723549914049121850350291 133085324871073682775525437)
      ·
        refine ⟨49906996826652631040822039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133085324871073682775525437 49906996826652631040822039)
        ·
          refine ⟨74860495239978946561233059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49906996826652631040822039 74860495239978946561233059)
          ·
            refine ⟨112290742859968419841849589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74860495239978946561233059 112290742859968419841849589)
            ·
              refine ⟨10527257143122039360173399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112290742859968419841849589 10527257143122039360173399)
              ·
                refine ⟨15790885714683059040260099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527257143122039360173399 15790885714683059040260099)
                ·
                  refine ⟨23686328572024588560390149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15790885714683059040260099 23686328572024588560390149)
                  ·
                    refine ⟨4441186607254610355073153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23686328572024588560390149 4441186607254610355073153)
                    ·
                      refine ⟨3330889955440957766304865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441186607254610355073153 3330889955440957766304865)
                      ·
                        rfl

theorem cell23_6486885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_6486885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486885 prefixEnd_6486885 := by exact prefixLift 6486885
  have htrace : WordTrace (prefixWord ++ tailWord_6486885) baseStart_6486885 baseEnd_6486885 := by
    simpa [prefixWord, tailWord_6486885, baseEnd_6486885] using wordTrace_append hprefix tailTrace_6486885
  have hstable : (prefixWord ++ tailWord_6486885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486885).length < 2 ^ (prefixWord ++ tailWord_6486885).sum := by decide
  have hdescent : baseEnd_6486885 < baseStart_6486885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486891 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 7]
def baseStart_6486891 : Nat := 118140960795 + 6486891 * 2 ^ 59
def prefixEnd_6486891 : Nat := 4983230072969 + 3 ^ 40 * 6486891 * 2
def baseEnd_6486891 : Nat := 370099226258320526981093

theorem tailTrace_6486891 : CollatzResearch.WordTrace tailWord_6486891 prefixEnd_6486891 370099226258320526981093 := by
  unfold tailWord_6486891
  simp only [CollatzResearch.WordTrace]
  refine ⟨236596351942109254625652527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157730901294739503083768351 236596351942109254625652527)
  ·
    refine ⟨354894527913163881938478791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236596351942109254625652527 354894527913163881938478791)
    ·
      refine ⟨532341791869745822907718187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354894527913163881938478791 532341791869745822907718187)
      ·
        refine ⟨798512687804618734361577281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532341791869745822907718187 798512687804618734361577281)
        ·
          refine ⟨598884515853464050771182961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798512687804618734361577281 598884515853464050771182961)
          ·
            refine ⟨449163386890098038078387221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598884515853464050771182961 449163386890098038078387221)
            ·
              refine ⟨21054533760473345534924401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 449163386890098038078387221 21054533760473345534924401)
              ·
                refine ⟨15790900320355009151193301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21054533760473345534924401 15790900320355009151193301)
                ·
                  refine ⟨370099226258320526981093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15790900320355009151193301 370099226258320526981093)
                  ·
                    rfl

theorem cell23_6486891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 7].length) (baseStart_6486891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486891 prefixEnd_6486891 := by exact prefixLift 6486891
  have htrace : WordTrace (prefixWord ++ tailWord_6486891) baseStart_6486891 baseEnd_6486891 := by
    simpa [prefixWord, tailWord_6486891, baseEnd_6486891] using wordTrace_append hprefix tailTrace_6486891
  have hstable : (prefixWord ++ tailWord_6486891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486891).length < 2 ^ (prefixWord ++ tailWord_6486891).sum := by decide
  have hdescent : baseEnd_6486891 < baseStart_6486891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6486981 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 12]
def baseStart_6486981 : Nat := 118140960795 + 6486981 * 2 ^ 59
def prefixEnd_6486981 : Nat := 4983230072969 + 3 ^ 40 * 6486981 * 2
def baseEnd_6486981 : Nat := 370104361064865487856047

theorem tailTrace_6486981 : CollatzResearch.WordTrace tailWord_6486981 prefixEnd_6486981 370104361064865487856047 := by
  unfold tailWord_6486981
  simp only [CollatzResearch.WordTrace]
  refine ⟨236599634511783199996428797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157733089674522133330952531 236599634511783199996428797)
  ·
    refine ⟨88724862941918699998660799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236599634511783199996428797 88724862941918699998660799)
    ·
      refine ⟨133087294412878049997991199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88724862941918699998660799 133087294412878049997991199)
      ·
        refine ⟨199630941619317074996986799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133087294412878049997991199 199630941619317074996986799)
        ·
          refine ⟨299446412428975612495480199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199630941619317074996986799 299446412428975612495480199)
          ·
            refine ⟨449169618643463418743220299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299446412428975612495480199 449169618643463418743220299)
            ·
              refine ⟨673754427965195128114830449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449169618643463418743220299 673754427965195128114830449)
              ·
                refine ⟨505315820973896346086122837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673754427965195128114830449 505315820973896346086122837)
                ·
                  refine ⟨370104361064865487856047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 505315820973896346086122837 370104361064865487856047)
                  ·
                    rfl

theorem cell23_6486981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_6486981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6486981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6486981 prefixEnd_6486981 := by exact prefixLift 6486981
  have htrace : WordTrace (prefixWord ++ tailWord_6486981) baseStart_6486981 baseEnd_6486981 := by
    simpa [prefixWord, tailWord_6486981, baseEnd_6486981] using wordTrace_append hprefix tailTrace_6486981
  have hstable : (prefixWord ++ tailWord_6486981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6486981).length < 2 ^ (prefixWord ++ tailWord_6486981).sum := by decide
  have hdescent : baseEnd_6486981 < baseStart_6486981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6486981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487035 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 4, 3, 2]
def baseStart_6487035 : Nat := 118140960795 + 6487035 * 2 ^ 59
def prefixEnd_6487035 : Nat := 4983230072969 + 3 ^ 40 * 6487035 * 2
def baseEnd_6487035 : Nat := 3330966977539132179429175

theorem tailTrace_6487035 : CollatzResearch.WordTrace tailWord_6487035 prefixEnd_6487035 3330966977539132179429175 := by
  unfold tailWord_6487035
  simp only [CollatzResearch.WordTrace]
  refine ⟨236601604053587567218894559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157734402702391711479263039 236601604053587567218894559)
  ·
    refine ⟨354902406080381350828341839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236601604053587567218894559 354902406080381350828341839)
    ·
      refine ⟨532353609120572026242512759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354902406080381350828341839 532353609120572026242512759)
      ·
        refine ⟨798530413680858039363769139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532353609120572026242512759 798530413680858039363769139)
        ·
          refine ⟨1197795620521287059045653709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798530413680858039363769139 1197795620521287059045653709)
          ·
            refine ⟨449173357695482647142120141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1197795620521287059045653709 449173357695482647142120141)
            ·
              refine ⟨168440009135805992678295053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 449173357695482647142120141 168440009135805992678295053)
              ·
                refine ⟨63165003425927247254360645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168440009135805992678295053 63165003425927247254360645)
                ·
                  refine ⟨11843438142361358860192621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63165003425927247254360645 11843438142361358860192621)
                  ·
                    refine ⟨4441289303385509572572233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11843438142361358860192621 4441289303385509572572233)
                    ·
                      refine ⟨3330966977539132179429175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441289303385509572572233 3330966977539132179429175)
                      ·
                        rfl

theorem cell23_6487035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3, 2].length) (baseStart_6487035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487035 prefixEnd_6487035 := by exact prefixLift 6487035
  have htrace : WordTrace (prefixWord ++ tailWord_6487035) baseStart_6487035 baseEnd_6487035 := by
    simpa [prefixWord, tailWord_6487035, baseEnd_6487035] using wordTrace_append hprefix tailTrace_6487035
  have hstable : (prefixWord ++ tailWord_6487035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487035).length < 2 ^ (prefixWord ++ tailWord_6487035).sum := by decide
  have hdescent : baseEnd_6487035 < baseStart_6487035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487065 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 4]
def baseStart_6487065 : Nat := 118140960795 + 6487065 * 2 ^ 59
def prefixEnd_6487065 : Nat := 4983230072969 + 3 ^ 40 * 6487065 * 2
def baseEnd_6487065 : Nat := 3330982381958767062054037

theorem tailTrace_6487065 : CollatzResearch.WordTrace tailWord_6487065 prefixEnd_6487065 3330982381958767062054037 := by
  unfold tailWord_6487065
  simp only [CollatzResearch.WordTrace]
  refine ⟨236602698243478882342486649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157735132162319254894991099 236602698243478882342486649)
  ·
    refine ⟨177452023682609161756864987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236602698243478882342486649 177452023682609161756864987)
    ·
      refine ⟨266178035523913742635297481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177452023682609161756864987 266178035523913742635297481)
      ·
        refine ⟨199633526642935306976473111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266178035523913742635297481 199633526642935306976473111)
        ·
          refine ⟨299450289964402960464709667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199633526642935306976473111 299450289964402960464709667)
          ·
            refine ⟨449175434946604440697064501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299450289964402960464709667 449175434946604440697064501)
            ·
              refine ⟨42110197026244166315349797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449175434946604440697064501 42110197026244166315349797)
              ·
                refine ⟨7895661942420781184128087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42110197026244166315349797 7895661942420781184128087)
                ·
                  refine ⟨11843492913631171776192131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7895661942420781184128087 11843492913631171776192131)
                  ·
                    refine ⟨17765239370446757664288197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11843492913631171776192131 17765239370446757664288197)
                    ·
                      refine ⟨3330982381958767062054037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17765239370446757664288197 3330982381958767062054037)
                      ·
                        rfl

theorem cell23_6487065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_6487065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487065 prefixEnd_6487065 := by exact prefixLift 6487065
  have htrace : WordTrace (prefixWord ++ tailWord_6487065) baseStart_6487065 baseEnd_6487065 := by
    simpa [prefixWord, tailWord_6487065, baseEnd_6487065] using wordTrace_append hprefix tailTrace_6487065
  have hstable : (prefixWord ++ tailWord_6487065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487065).length < 2 ^ (prefixWord ++ tailWord_6487065).sum := by decide
  have hdescent : baseEnd_6487065 < baseStart_6487065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487075 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 4, 4]
def baseStart_6487075 : Nat := 118140960795 + 6487075 * 2 ^ 59
def prefixEnd_6487075 : Nat := 4983230072969 + 3 ^ 40 * 6487075 * 2
def baseEnd_6487075 : Nat := 1110329172255104007642997

theorem tailTrace_6487075 : CollatzResearch.WordTrace tailWord_6487075 prefixEnd_6487075 1110329172255104007642997 := by
  unfold tailWord_6487075
  simp only [CollatzResearch.WordTrace]
  refine ⟨236603062973442654050350679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157735375315628436033567119 236603062973442654050350679)
  ·
    refine ⟨354904594460163981075526019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236603062973442654050350679 354904594460163981075526019)
    ·
      refine ⟨532356891690245971613289029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354904594460163981075526019 532356891690245971613289029)
      ·
        refine ⟨99816917191921119677491693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 532356891690245971613289029 99816917191921119677491693)
        ·
          refine ⟨37431343946970419879059385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99816917191921119677491693 37431343946970419879059385)
          ·
            refine ⟨28073507960227814909294539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37431343946970419879059385 28073507960227814909294539)
            ·
              refine ⟨42110261940341722363941809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28073507960227814909294539 42110261940341722363941809)
              ·
                refine ⟨31582696455256291772956357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42110261940341722363941809 31582696455256291772956357)
                ·
                  refine ⟨5921755585360554707429317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31582696455256291772956357 5921755585360554707429317)
                  ·
                    refine ⟨1110329172255104007642997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5921755585360554707429317 1110329172255104007642997)
                    ·
                      rfl

theorem cell23_6487075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 4].length) (baseStart_6487075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487075 prefixEnd_6487075 := by exact prefixLift 6487075
  have htrace : WordTrace (prefixWord ++ tailWord_6487075) baseStart_6487075 baseEnd_6487075 := by
    simpa [prefixWord, tailWord_6487075, baseEnd_6487075] using wordTrace_append hprefix tailTrace_6487075
  have hstable : (prefixWord ++ tailWord_6487075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487075).length < 2 ^ (prefixWord ++ tailWord_6487075).sum := by decide
  have hdescent : baseEnd_6487075 < baseStart_6487075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487076 : List Nat := [2, 3, 1, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_6487076 : Nat := 118140960795 + 6487076 * 2 ^ 59
def prefixEnd_6487076 : Nat := 4983230072969 + 3 ^ 40 * 6487076 * 2
def baseEnd_6487076 : Nat := 3330988030245966519016487

theorem tailTrace_6487076 : CollatzResearch.WordTrace tailWord_6487076 prefixEnd_6487076 3330988030245966519016487 := by
  unfold tailWord_6487076
  simp only [CollatzResearch.WordTrace]
  refine ⟨118301549723219515610568541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157735399630959354147424721 118301549723219515610568541)
  ·
    refine ⟨44363081146207318353963203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118301549723219515610568541 44363081146207318353963203)
    ·
      refine ⟨66544621719310977530944805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44363081146207318353963203 66544621719310977530944805)
      ·
        refine ⟨12477116572370808287052151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66544621719310977530944805 12477116572370808287052151)
        ·
          refine ⟨18715674858556212430578227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12477116572370808287052151 18715674858556212430578227)
          ·
            refine ⟨28073512287834318645867341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18715674858556212430578227 28073512287834318645867341)
            ·
              refine ⟨10527567107937869492200253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28073512287834318645867341 10527567107937869492200253)
              ·
                refine ⟨3947837665476701059575095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10527567107937869492200253 3947837665476701059575095)
                ·
                  refine ⟨5921756498215051589362643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947837665476701059575095 5921756498215051589362643)
                  ·
                    refine ⟨8882634747322577384043965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921756498215051589362643 8882634747322577384043965)
                    ·
                      refine ⟨3330988030245966519016487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8882634747322577384043965 3330988030245966519016487)
                      ·
                        rfl

theorem cell23_6487076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_6487076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487076 prefixEnd_6487076 := by exact prefixLift 6487076
  have htrace : WordTrace (prefixWord ++ tailWord_6487076) baseStart_6487076 baseEnd_6487076 := by
    simpa [prefixWord, tailWord_6487076, baseEnd_6487076] using wordTrace_append hprefix tailTrace_6487076
  have hstable : (prefixWord ++ tailWord_6487076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487076).length < 2 ^ (prefixWord ++ tailWord_6487076).sum := by decide
  have hdescent : baseEnd_6487076 < baseStart_6487076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487102 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6487102 : Nat := 118140960795 + 6487102 * 2 ^ 59
def prefixEnd_6487102 : Nat := 4983230072969 + 3 ^ 40 * 6487102 * 2
def baseEnd_6487102 : Nat := 3331001380742983417291367

theorem tailTrace_6487102 : CollatzResearch.WordTrace tailWord_6487102 prefixEnd_6487102 3331001380742983417291367 := by
  unfold tailWord_6487102
  simp only [CollatzResearch.WordTrace]
  refine ⟨29575505968043104707697945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157736031829563225107722373 29575505968043104707697945)
  ·
    refine ⟨22181629476032328530773459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29575505968043104707697945 22181629476032328530773459)
    ·
      refine ⟨33272444214048492796160189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22181629476032328530773459 33272444214048492796160189)
      ·
        refine ⟨12477166580268184798560071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33272444214048492796160189 12477166580268184798560071)
        ·
          refine ⟨18715749870402277197840107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12477166580268184798560071 18715749870402277197840107)
          ·
            refine ⟨28073624805603415796760161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18715749870402277197840107 28073624805603415796760161)
            ·
              refine ⟨21055218604202561847570121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28073624805603415796760161 21055218604202561847570121)
              ·
                refine ⟨15791413953151921385677591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21055218604202561847570121 15791413953151921385677591)
                ·
                  refine ⟨23687120929727882078516387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15791413953151921385677591 23687120929727882078516387)
                  ·
                    refine ⟨35530681394591823117774581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23687120929727882078516387 35530681394591823117774581)
                    ·
                      refine ⟨3331001380742983417291367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35530681394591823117774581 3331001380742983417291367)
                      ·
                        rfl

theorem cell23_6487102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6487102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487102 prefixEnd_6487102 := by exact prefixLift 6487102
  have htrace : WordTrace (prefixWord ++ tailWord_6487102) baseStart_6487102 baseEnd_6487102 := by
    simpa [prefixWord, tailWord_6487102, baseEnd_6487102] using wordTrace_append hprefix tailTrace_6487102
  have hstable : (prefixWord ++ tailWord_6487102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487102).length < 2 ^ (prefixWord ++ tailWord_6487102).sum := by decide
  have hdescent : baseEnd_6487102 < baseStart_6487102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487132 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_6487132 : Nat := 118140960795 + 6487132 * 2 ^ 59
def prefixEnd_6487132 : Nat := 4983230072969 + 3 ^ 40 * 6487132 * 2
def baseEnd_6487132 : Nat := 3331016785162618299916229

theorem tailTrace_6487132 : CollatzResearch.WordTrace tailWord_6487132 prefixEnd_6487132 3331016785162618299916229 := by
  unfold tailWord_6487132
  simp only [CollatzResearch.WordTrace]
  refine ⟨118302570967118076392587825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157736761289490768523450433 118302570967118076392587825)
  ·
    refine ⟨88726928225338557294440869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118302570967118076392587825 88726928225338557294440869)
    ·
      refine ⟨16636299042250979492707663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88726928225338557294440869 16636299042250979492707663)
      ·
        refine ⟨24954448563376469239061495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16636299042250979492707663 24954448563376469239061495)
        ·
          refine ⟨37431672845064703858592243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24954448563376469239061495 37431672845064703858592243)
          ·
            refine ⟨56147509267597055787888365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37431672845064703858592243 56147509267597055787888365)
            ·
              refine ⟨21055315975348895920458137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56147509267597055787888365 21055315975348895920458137)
              ·
                refine ⟨15791486981511671940343603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21055315975348895920458137 15791486981511671940343603)
                ·
                  refine ⟨23687230472267507910515405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15791486981511671940343603 23687230472267507910515405)
                  ·
                    refine ⟨8882711427100315466443277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23687230472267507910515405 8882711427100315466443277)
                    ·
                      refine ⟨3331016785162618299916229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8882711427100315466443277 3331016785162618299916229)
                      ·
                        rfl

theorem cell23_6487132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_6487132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487132 prefixEnd_6487132 := by exact prefixLift 6487132
  have htrace : WordTrace (prefixWord ++ tailWord_6487132) baseStart_6487132 baseEnd_6487132 := by
    simpa [prefixWord, tailWord_6487132, baseEnd_6487132] using wordTrace_append hprefix tailTrace_6487132
  have hstable : (prefixWord ++ tailWord_6487132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487132).length < 2 ^ (prefixWord ++ tailWord_6487132).sum := by decide
  have hdescent : baseEnd_6487132 < baseStart_6487132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487149 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_6487149 : Nat := 118140960795 + 6487149 * 2 ^ 59
def prefixEnd_6487149 : Nat := 4983230072969 + 3 ^ 40 * 6487149 * 2
def baseEnd_6487149 : Nat := 3331025514333744733403651

theorem tailTrace_6487149 : CollatzResearch.WordTrace tailWord_6487149 prefixEnd_6487149 3331025514333744733403651 := by
  unfold tailWord_6487149
  simp only [CollatzResearch.WordTrace]
  refine ⟨236605761975174564688544501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157737174650116376459029667 236605761975174564688544501)
  ·
    refine ⟨22181790185172615439551047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236605761975174564688544501 22181790185172615439551047)
    ·
      refine ⟨33272685277758923159326571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22181790185172615439551047 33272685277758923159326571)
      ·
        refine ⟨49909027916638384738989857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33272685277758923159326571 49909027916638384738989857)
        ·
          refine ⟨37431770937478788554242393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49909027916638384738989857 37431770937478788554242393)
          ·
            refine ⟨28073828203109091415681795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37431770937478788554242393 28073828203109091415681795)
            ·
              refine ⟨42110742304663637123522693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28073828203109091415681795 42110742304663637123522693)
              ·
                refine ⟨7895764182124431960660505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42110742304663637123522693 7895764182124431960660505)
                ·
                  refine ⟨5921823136593323970495379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7895764182124431960660505 5921823136593323970495379)
                  ·
                    refine ⟨8882734704889985955743069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921823136593323970495379 8882734704889985955743069)
                    ·
                      refine ⟨3331025514333744733403651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8882734704889985955743069 3331025514333744733403651)
                      ·
                        rfl

theorem cell23_6487149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_6487149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487149 prefixEnd_6487149 := by exact prefixLift 6487149
  have htrace : WordTrace (prefixWord ++ tailWord_6487149) baseStart_6487149 baseEnd_6487149 := by
    simpa [prefixWord, tailWord_6487149, baseEnd_6487149] using wordTrace_append hprefix tailTrace_6487149
  have hstable : (prefixWord ++ tailWord_6487149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487149).length < 2 ^ (prefixWord ++ tailWord_6487149).sum := by decide
  have hdescent : baseEnd_6487149 < baseStart_6487149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487150 : List Nat := [4, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_6487150 : Nat := 118140960795 + 6487150 * 2 ^ 59
def prefixEnd_6487150 : Nat := 4983230072969 + 3 ^ 40 * 6487150 * 2
def baseEnd_6487150 : Nat := 3331026027814399229491147

theorem tailTrace_6487150 : CollatzResearch.WordTrace tailWord_6487150 prefixEnd_6487150 3331026027814399229491147 := by
  unfold tailWord_6487150
  simp only [CollatzResearch.WordTrace]
  refine ⟨29575724806021367732416363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157737198965447294572887269 29575724806021367732416363)
  ·
    refine ⟨44363587209032051598624545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29575724806021367732416363 44363587209032051598624545)
    ·
      refine ⟨33272690406774038698968409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44363587209032051598624545 33272690406774038698968409)
      ·
        refine ⟨24954517805080529024226307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33272690406774038698968409 24954517805080529024226307)
        ·
          refine ⟨37431776707620793536339461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24954517805080529024226307 37431776707620793536339461)
          ·
            refine ⟨7018458132678898788063649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37431776707620793536339461 7018458132678898788063649)
            ·
              refine ⟨5263843599509174091047737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7018458132678898788063649 5263843599509174091047737)
              ·
                refine ⟨3947882699631880568285803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263843599509174091047737 3947882699631880568285803)
                ·
                  refine ⟨5921824049447820852428705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947882699631880568285803 5921824049447820852428705)
                  ·
                    refine ⟨4441368037085865639321529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5921824049447820852428705 4441368037085865639321529)
                    ·
                      refine ⟨3331026027814399229491147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441368037085865639321529 3331026027814399229491147)
                      ·
                        rfl

theorem cell23_6487150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_6487150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487150 prefixEnd_6487150 := by exact prefixLift 6487150
  have htrace : WordTrace (prefixWord ++ tailWord_6487150) baseStart_6487150 baseEnd_6487150 := by
    simpa [prefixWord, tailWord_6487150, baseEnd_6487150] using wordTrace_append hprefix tailTrace_6487150
  have hstable : (prefixWord ++ tailWord_6487150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487150).length < 2 ^ (prefixWord ++ tailWord_6487150).sum := by decide
  have hdescent : baseEnd_6487150 < baseStart_6487150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487165 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_6487165 : Nat := 118140960795 + 6487165 * 2 ^ 59
def prefixEnd_6487165 : Nat := 4983230072969 + 3 ^ 40 * 6487165 * 2
def baseEnd_6487165 : Nat := 1110344576674738890267859

theorem tailTrace_6487165 : CollatzResearch.WordTrace tailWord_6487165 prefixEnd_6487165 1110344576674738890267859 := by
  unfold tailWord_6487165
  simp only [CollatzResearch.WordTrace]
  refine ⟨236606345543116599421126949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157737563695411066280751299 236606345543116599421126949)
  ·
    refine ⟨44363689789334362391461303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236606345543116599421126949 44363689789334362391461303)
    ·
      refine ⟨66545534684001543587191955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44363689789334362391461303 66545534684001543587191955)
      ·
        refine ⟨99818302026002315380787933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66545534684001543587191955 99818302026002315380787933)
        ·
          refine ⟨37431863259750868267795475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99818302026002315380787933 37431863259750868267795475)
          ·
            refine ⟨56147794889626302401693213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37431863259750868267795475 56147794889626302401693213)
            ·
              refine ⟨21055423083609863400634955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56147794889626302401693213 21055423083609863400634955)
              ·
                refine ⟨31583134625414795100952433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21055423083609863400634955 31583134625414795100952433)
                ·
                  refine ⟨23687350969061096325714325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31583134625414795100952433 23687350969061096325714325)
                  ·
                    refine ⟨1110344576674738890267859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23687350969061096325714325 1110344576674738890267859)
                    ·
                      rfl

theorem cell23_6487165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_6487165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487165 prefixEnd_6487165 := by exact prefixLift 6487165
  have htrace : WordTrace (prefixWord ++ tailWord_6487165) baseStart_6487165 baseEnd_6487165 := by
    simpa [prefixWord, tailWord_6487165, baseEnd_6487165] using wordTrace_append hprefix tailTrace_6487165
  have hstable : (prefixWord ++ tailWord_6487165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487165).length < 2 ^ (prefixWord ++ tailWord_6487165).sum := by decide
  have hdescent : baseEnd_6487165 < baseStart_6487165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487175 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_6487175 : Nat := 118140960795 + 6487175 * 2 ^ 59
def prefixEnd_6487175 : Nat := 4983230072969 + 3 ^ 40 * 6487175 * 2
def baseEnd_6487175 : Nat := 3331038864830761631678531

theorem tailTrace_6487175 : CollatzResearch.WordTrace tailWord_6487175 prefixEnd_6487175 3331038864830761631678531 := by
  unfold tailWord_6487175
  simp only [CollatzResearch.WordTrace]
  refine ⟨236606710273080371128990979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157737806848720247419327319 236606710273080371128990979)
  ·
    refine ⟨354910065409620556693486469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236606710273080371128990979 354910065409620556693486469)
    ·
      refine ⟨66545637264303854380028713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354910065409620556693486469 66545637264303854380028713)
      ·
        refine ⟨49909227948227890785021535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66545637264303854380028713 49909227948227890785021535)
        ·
          refine ⟨74863841922341836177532303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49909227948227890785021535 74863841922341836177532303)
          ·
            refine ⟨112295762883512754266298455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74863841922341836177532303 112295762883512754266298455)
            ·
              refine ⟨168443644325269131399447683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112295762883512754266298455 168443644325269131399447683)
              ·
                refine ⟨252665466487903697099171525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168443644325269131399447683 252665466487903697099171525)
                ·
                  refine ⟨47374774966481943206094661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252665466487903697099171525 47374774966481943206094661)
                  ·
                    refine ⟨8882770306215364351142749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47374774966481943206094661 8882770306215364351142749)
                    ·
                      refine ⟨3331038864830761631678531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8882770306215364351142749 3331038864830761631678531)
                      ·
                        rfl

theorem cell23_6487175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_6487175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487175 prefixEnd_6487175 := by exact prefixLift 6487175
  have htrace : WordTrace (prefixWord ++ tailWord_6487175) baseStart_6487175 baseEnd_6487175 := by
    simpa [prefixWord, tailWord_6487175, baseEnd_6487175] using wordTrace_append hprefix tailTrace_6487175
  have hstable : (prefixWord ++ tailWord_6487175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487175).length < 2 ^ (prefixWord ++ tailWord_6487175).sum := by decide
  have hdescent : baseEnd_6487175 < baseStart_6487175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487225 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 1, 7]
def baseStart_6487225 : Nat := 118140960795 + 6487225 * 2 ^ 59
def prefixEnd_6487225 : Nat := 4983230072969 + 3 ^ 40 * 6487225 * 2
def baseEnd_6487225 : Nat := 1110354846287828812017767

theorem tailTrace_6487225 : CollatzResearch.WordTrace tailWord_6487225 prefixEnd_6487225 1110354846287828812017767 := by
  unfold tailWord_6487225
  simp only [CollatzResearch.WordTrace]
  refine ⟨236608533922899229668311129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157739022615266153112207419 236608533922899229668311129)
  ·
    refine ⟨177456400442174422251233347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236608533922899229668311129 177456400442174422251233347)
    ·
      refine ⟨266184600663261633376850021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177456400442174422251233347 266184600663261633376850021)
      ·
        refine ⟨49909612624361556258159379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266184600663261633376850021 49909612624361556258159379)
        ·
          refine ⟨74864418936542334387239069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49909612624361556258159379 74864418936542334387239069)
          ·
            refine ⟨28074157101203375395214651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74864418936542334387239069 28074157101203375395214651)
            ·
              refine ⟨42111235651805063092821977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28074157101203375395214651 42111235651805063092821977)
              ·
                refine ⟨31583426738853797319616483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42111235651805063092821977 31583426738853797319616483)
                ·
                  refine ⟨47375140108280695979424725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31583426738853797319616483 47375140108280695979424725)
                  ·
                    refine ⟨1110354846287828812017767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47375140108280695979424725 1110354846287828812017767)
                    ·
                      rfl

theorem cell23_6487225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_6487225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487225 prefixEnd_6487225 := by exact prefixLift 6487225
  have htrace : WordTrace (prefixWord ++ tailWord_6487225) baseStart_6487225 baseEnd_6487225 := by
    simpa [prefixWord, tailWord_6487225, baseEnd_6487225] using wordTrace_append hprefix tailTrace_6487225
  have hstable : (prefixWord ++ tailWord_6487225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487225).length < 2 ^ (prefixWord ++ tailWord_6487225).sum := by decide
  have hdescent : baseEnd_6487225 < baseStart_6487225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487246 : List Nat := [4, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_6487246 : Nat := 118140960795 + 6487246 * 2 ^ 59
def prefixEnd_6487246 : Nat := 4983230072969 + 3 ^ 40 * 6487246 * 2
def baseEnd_6487246 : Nat := 370119480217470094876745

theorem tailTrace_6487246 : CollatzResearch.WordTrace tailWord_6487246 prefixEnd_6487246 370119480217470094876745 := by
  unfold tailWord_6487246
  simp only [CollatzResearch.WordTrace]
  refine ⟨29576162481977893781853199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157739533237215433503217061 29576162481977893781853199)
  ·
    refine ⟨44364243722966840672779799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29576162481977893781853199 44364243722966840672779799)
    ·
      refine ⟨66546365584450261009169699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44364243722966840672779799 66546365584450261009169699)
      ·
        refine ⟨99819548376675391513754549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66546365584450261009169699 99819548376675391513754549)
        ·
          refine ⟨9358082660313317954414489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99819548376675391513754549 9358082660313317954414489)
          ·
            refine ⟨7018561995234988465810867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9358082660313317954414489 7018561995234988465810867)
            ·
              refine ⟨10527842992852482698716301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018561995234988465810867 10527842992852482698716301)
              ·
                refine ⟨3947941122319681012018613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10527842992852482698716301 3947941122319681012018613)
                ·
                  refine ⟨370119480217470094876745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3947941122319681012018613 370119480217470094876745)
                  ·
                    rfl

theorem cell23_6487246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_6487246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487246 prefixEnd_6487246 := by exact prefixLift 6487246
  have htrace : WordTrace (prefixWord ++ tailWord_6487246) baseStart_6487246 baseEnd_6487246 := by
    simpa [prefixWord, tailWord_6487246, baseEnd_6487246] using wordTrace_append hprefix tailTrace_6487246
  have hstable : (prefixWord ++ tailWord_6487246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487246).length < 2 ^ (prefixWord ++ tailWord_6487246).sum := by decide
  have hdescent : baseEnd_6487246 < baseStart_6487246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487299 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 3]
def baseStart_6487299 : Nat := 118140960795 + 6487299 * 2 ^ 59
def prefixEnd_6487299 : Nat := 4983230072969 + 3 ^ 40 * 6487299 * 2
def baseEnd_6487299 : Nat := 3331102536431919146527961

theorem tailTrace_6487299 : CollatzResearch.WordTrace tailWord_6487299 prefixEnd_6487299 3331102536431919146527961 := by
  unfold tailWord_6487299
  simp only [CollatzResearch.WordTrace]
  refine ⟨236611232924631140306504951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157740821949754093537669967 236611232924631140306504951)
  ·
    refine ⟨354916849386946710459757427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236611232924631140306504951 354916849386946710459757427)
    ·
      refine ⟨532375274080420065689636141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354916849386946710459757427 532375274080420065689636141)
      ·
        refine ⟨199640727780157524633613553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532375274080420065689636141 199640727780157524633613553)
        ·
          refine ⟨149730545835118143475210165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199640727780157524633613553 149730545835118143475210165)
          ·
            refine ⟨14037238672042325950800953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149730545835118143475210165 14037238672042325950800953)
            ·
              refine ⟨10527929004031744463100715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14037238672042325950800953 10527929004031744463100715)
              ·
                refine ⟨15791893506047616694651073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527929004031744463100715 15791893506047616694651073)
                ·
                  refine ⟨11843920129535712520988305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15791893506047616694651073 11843920129535712520988305)
                  ·
                    refine ⟨8882940097151784390741229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11843920129535712520988305 8882940097151784390741229)
                    ·
                      refine ⟨3331102536431919146527961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8882940097151784390741229 3331102536431919146527961)
                      ·
                        rfl

theorem cell23_6487299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_6487299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487299 prefixEnd_6487299 := by exact prefixLift 6487299
  have htrace : WordTrace (prefixWord ++ tailWord_6487299) baseStart_6487299 baseEnd_6487299 := by
    simpa [prefixWord, tailWord_6487299, baseEnd_6487299] using wordTrace_append hprefix tailTrace_6487299
  have hstable : (prefixWord ++ tailWord_6487299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487299).length < 2 ^ (prefixWord ++ tailWord_6487299).sum := by decide
  have hdescent : baseEnd_6487299 < baseStart_6487299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487329 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_6487329 : Nat := 118140960795 + 6487329 * 2 ^ 59
def prefixEnd_6487329 : Nat := 4983230072969 + 3 ^ 40 * 6487329 * 2
def baseEnd_6487329 : Nat := 3331117940851554029152823

theorem tailTrace_6487329 : CollatzResearch.WordTrace tailWord_6487329 prefixEnd_6487329 3331117940851554029152823 := by
  unfold tailWord_6487329
  simp only [CollatzResearch.WordTrace]
  refine ⟨236612327114522455430097041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157741551409681636953398027 236612327114522455430097041)
  ·
    refine ⟨177459245335891841572572781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236612327114522455430097041 177459245335891841572572781)
    ·
      refine ⟨66547217000959440589714793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177459245335891841572572781 66547217000959440589714793)
      ·
        refine ⟨49910412750719580442286095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66547217000959440589714793 49910412750719580442286095)
        ·
          refine ⟨74865619126079370663429143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49910412750719580442286095 74865619126079370663429143)
          ·
            refine ⟨112298428689119055995143715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74865619126079370663429143 112298428689119055995143715)
            ·
              refine ⟨168447643033678583992715573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112298428689119055995143715 168447643033678583992715573)
              ·
                refine ⟨15791966534407367249317085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168447643033678583992715573 15791966534407367249317085)
                ·
                  refine ⟨5921987450402762718493907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15791966534407367249317085 5921987450402762718493907)
                  ·
                    refine ⟨8882981175604144077740861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921987450402762718493907 8882981175604144077740861)
                    ·
                      refine ⟨3331117940851554029152823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8882981175604144077740861 3331117940851554029152823)
                      ·
                        rfl

theorem cell23_6487329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_6487329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487329 prefixEnd_6487329 := by exact prefixLift 6487329
  have htrace : WordTrace (prefixWord ++ tailWord_6487329) baseStart_6487329 baseEnd_6487329 := by
    simpa [prefixWord, tailWord_6487329, baseEnd_6487329] using wordTrace_append hprefix tailTrace_6487329
  have hstable : (prefixWord ++ tailWord_6487329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487329).length < 2 ^ (prefixWord ++ tailWord_6487329).sum := by decide
  have hdescent : baseEnd_6487329 < baseStart_6487329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487332 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_6487332 : Nat := 118140960795 + 6487332 * 2 ^ 59
def prefixEnd_6487332 : Nat := 4983230072969 + 3 ^ 40 * 6487332 * 2
def baseEnd_6487332 : Nat := 1110373160431172505805103

theorem tailTrace_6487332 : CollatzResearch.WordTrace tailWord_6487332 prefixEnd_6487332 1110373160431172505805103 := by
  unfold tailWord_6487332
  simp only [CollatzResearch.WordTrace]
  refine ⟨118306218266755793471228125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157741624355674391294970833 118306218266755793471228125)
  ·
    refine ⟨44364831850033422551710547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118306218266755793471228125 44364831850033422551710547)
    ·
      refine ⟨66547247775050133827565821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44364831850033422551710547 66547247775050133827565821)
      ·
        refine ⟨24955217915643800185337183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66547247775050133827565821 24955217915643800185337183)
        ·
          refine ⟨37432826873465700278005775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24955217915643800185337183 37432826873465700278005775)
          ·
            refine ⟨56149240310198550417008663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37432826873465700278005775 56149240310198550417008663)
            ·
              refine ⟨84223860465297825625512995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56149240310198550417008663 84223860465297825625512995)
              ·
                refine ⟨126335790697946738438269493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84223860465297825625512995 126335790697946738438269493)
                ·
                  refine ⟨11843980377932506728587765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126335790697946738438269493 11843980377932506728587765)
                  ·
                    refine ⟨1110373160431172505805103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11843980377932506728587765 1110373160431172505805103)
                    ·
                      rfl

theorem cell23_6487332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_6487332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487332 prefixEnd_6487332 := by exact prefixLift 6487332
  have htrace : WordTrace (prefixWord ++ tailWord_6487332) baseStart_6487332 baseEnd_6487332 := by
    simpa [prefixWord, tailWord_6487332, baseEnd_6487332] using wordTrace_append hprefix tailTrace_6487332
  have hstable : (prefixWord ++ tailWord_6487332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487332).length < 2 ^ (prefixWord ++ tailWord_6487332).sum := by decide
  have hdescent : baseEnd_6487332 < baseStart_6487332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487346 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_6487346 : Nat := 118140960795 + 6487346 * 2 ^ 59
def prefixEnd_6487346 : Nat := 4983230072969 + 3 ^ 40 * 6487346 * 2
def baseEnd_6487346 : Nat := 3331126670022680462640245

theorem tailTrace_6487346 : CollatzResearch.WordTrace tailWord_6487346 prefixEnd_6487346 3331126670022680462640245 := by
  unfold tailWord_6487346
  simp only [CollatzResearch.WordTrace]
  refine ⟨59153236788865216833366473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157741964770307244888977261 59153236788865216833366473)
  ·
    refine ⟨44364927591648912625024855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59153236788865216833366473 44364927591648912625024855)
    ·
      refine ⟨66547391387473368937537283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44364927591648912625024855 66547391387473368937537283)
      ·
        refine ⟨99821087081210053406305925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66547391387473368937537283 99821087081210053406305925)
        ·
          refine ⟨18716453827726885013682361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99821087081210053406305925 18716453827726885013682361)
          ·
            refine ⟨14037340370795163760261771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18716453827726885013682361 14037340370795163760261771)
            ·
              refine ⟨21056010556192745640392657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14037340370795163760261771 21056010556192745640392657)
              ·
                refine ⟨15792007917144559230294493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21056010556192745640392657 15792007917144559230294493)
                ·
                  refine ⟨5922002968929209711360435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15792007917144559230294493 5922002968929209711360435)
                  ·
                    refine ⟨8883004453393814567040653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5922002968929209711360435 8883004453393814567040653)
                    ·
                      refine ⟨3331126670022680462640245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883004453393814567040653 3331126670022680462640245)
                      ·
                        rfl

theorem cell23_6487346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_6487346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487346 prefixEnd_6487346 := by exact prefixLift 6487346
  have htrace : WordTrace (prefixWord ++ tailWord_6487346) baseStart_6487346 baseEnd_6487346 := by
    simpa [prefixWord, tailWord_6487346, baseEnd_6487346] using wordTrace_append hprefix tailTrace_6487346
  have hstable : (prefixWord ++ tailWord_6487346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487346).length < 2 ^ (prefixWord ++ tailWord_6487346).sum := by decide
  have hdescent : baseEnd_6487346 < baseStart_6487346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487350 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6487350 : Nat := 118140960795 + 6487350 * 2 ^ 59
def prefixEnd_6487350 : Nat := 4983230072969 + 3 ^ 40 * 6487350 * 2
def baseEnd_6487350 : Nat := 3331128723945298446990227

theorem tailTrace_6487350 : CollatzResearch.WordTrace tailWord_6487350 prefixEnd_6487350 3331128723945298446990227 := by
  unfold tailWord_6487350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788318315465398501038219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157742062031630917344407669 14788318315465398501038219)
  ·
    refine ⟨22182477473198097751557329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14788318315465398501038219 22182477473198097751557329)
    ·
      refine ⟨16636858104898573313667997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22182477473198097751557329 16636858104898573313667997)
      ·
        refine ⟨6238821789336964992625499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16636858104898573313667997 6238821789336964992625499)
        ·
          refine ⟨9358232684005447488938249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6238821789336964992625499 9358232684005447488938249)
          ·
            refine ⟨7018674513004085616703687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9358232684005447488938249 7018674513004085616703687)
            ·
              refine ⟨10528011769506128425055531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018674513004085616703687 10528011769506128425055531)
              ·
                refine ⟨15792017654259192637583297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528011769506128425055531 15792017654259192637583297)
                ·
                  refine ⟨11844013240694394478187473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15792017654259192637583297 11844013240694394478187473)
                  ·
                    refine ⟨8883009930520795858640605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11844013240694394478187473 8883009930520795858640605)
                    ·
                      refine ⟨3331128723945298446990227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883009930520795858640605 3331128723945298446990227)
                      ·
                        rfl

theorem cell23_6487350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6487350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487350 prefixEnd_6487350 := by exact prefixLift 6487350
  have htrace : WordTrace (prefixWord ++ tailWord_6487350) baseStart_6487350 baseEnd_6487350 := by
    simpa [prefixWord, tailWord_6487350, baseEnd_6487350] using wordTrace_append hprefix tailTrace_6487350
  have hstable : (prefixWord ++ tailWord_6487350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487350).length < 2 ^ (prefixWord ++ tailWord_6487350).sum := by decide
  have hdescent : baseEnd_6487350 < baseStart_6487350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487356 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_6487356 : Nat := 118140960795 + 6487356 * 2 ^ 59
def prefixEnd_6487356 : Nat := 4983230072969 + 3 ^ 40 * 6487356 * 2
def baseEnd_6487356 : Nat := 3331131804829225423515199

theorem tailTrace_6487356 : CollatzResearch.WordTrace tailWord_6487356 prefixEnd_6487356 3331131804829225423515199 := by
  unfold tailWord_6487356
  simp only [CollatzResearch.WordTrace]
  refine ⟨118306655942712319520664961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157742207923616426027553281 118306655942712319520664961)
  ·
    refine ⟨88729991957034239640498721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118306655942712319520664961 88729991957034239640498721)
    ·
      refine ⟨66547493967775679730374041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88729991957034239640498721 66547493967775679730374041)
      ·
        refine ⟨49910620475831759797780531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66547493967775679730374041 49910620475831759797780531)
        ·
          refine ⟨74865930713747639696670797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49910620475831759797780531 74865930713747639696670797)
          ·
            refine ⟨28074724017655364886251549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74865930713747639696670797 28074724017655364886251549)
            ·
              refine ⟨10528021506620761832344331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28074724017655364886251549 10528021506620761832344331)
              ·
                refine ⟨15792032259931142748516497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528021506620761832344331 15792032259931142748516497)
                ·
                  refine ⟨11844024194948357061387373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15792032259931142748516497 11844024194948357061387373)
                  ·
                    refine ⟨4441509073105633898020265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11844024194948357061387373 4441509073105633898020265)
                    ·
                      refine ⟨3331131804829225423515199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441509073105633898020265 3331131804829225423515199)
                      ·
                        rfl

theorem cell23_6487356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_6487356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487356 prefixEnd_6487356 := by exact prefixLift 6487356
  have htrace : WordTrace (prefixWord ++ tailWord_6487356) baseStart_6487356 baseEnd_6487356 := by
    simpa [prefixWord, tailWord_6487356, baseEnd_6487356] using wordTrace_append hprefix tailTrace_6487356
  have hstable : (prefixWord ++ tailWord_6487356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487356).length < 2 ^ (prefixWord ++ tailWord_6487356).sum := by decide
  have hdescent : baseEnd_6487356 < baseStart_6487356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487386 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2]
def baseStart_6487386 : Nat := 118140960795 + 6487386 * 2 ^ 59
def prefixEnd_6487386 : Nat := 4983230072969 + 3 ^ 40 * 6487386 * 2
def baseEnd_6487386 : Nat := 3331147209248860306140061

theorem tailTrace_6487386 : CollatzResearch.WordTrace tailWord_6487386 prefixEnd_6487386 3331147209248860306140061 := by
  unfold tailWord_6487386
  simp only [CollatzResearch.WordTrace]
  refine ⟨59153601518828988541230503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157742937383543969443281341 59153601518828988541230503)
  ·
    refine ⟨88730402278243482811845755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59153601518828988541230503 88730402278243482811845755)
    ·
      refine ⟨133095603417365224217768633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88730402278243482811845755 133095603417365224217768633)
      ·
        refine ⟨99821702563023918163326475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133095603417365224217768633 99821702563023918163326475)
        ·
          refine ⟨149732553844535877244989713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99821702563023918163326475 149732553844535877244989713)
          ·
            refine ⟨112299415383401907933742285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149732553844535877244989713 112299415383401907933742285)
            ·
              refine ⟨42112280768775715475153357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112299415383401907933742285 42112280768775715475153357)
              ·
                refine ⟨15792105288290893303182509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42112280768775715475153357 15792105288290893303182509)
                ·
                  refine ⟨5922039483109084988693441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15792105288290893303182509 5922039483109084988693441)
                  ·
                    refine ⟨4441529612331813741520081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5922039483109084988693441 4441529612331813741520081)
                    ·
                      refine ⟨3331147209248860306140061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441529612331813741520081 3331147209248860306140061)
                      ·
                        rfl

theorem cell23_6487386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_6487386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487386 prefixEnd_6487386 := by exact prefixLift 6487386
  have htrace : WordTrace (prefixWord ++ tailWord_6487386) baseStart_6487386 baseEnd_6487386 := by
    simpa [prefixWord, tailWord_6487386, baseEnd_6487386] using wordTrace_append hprefix tailTrace_6487386
  have hstable : (prefixWord ++ tailWord_6487386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487386).length < 2 ^ (prefixWord ++ tailWord_6487386).sum := by decide
  have hdescent : baseEnd_6487386 < baseStart_6487386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487399 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_6487399 : Nat := 118140960795 + 6487399 * 2 ^ 59
def prefixEnd_6487399 : Nat := 4983230072969 + 3 ^ 40 * 6487399 * 2
def baseEnd_6487399 : Nat := 3331153884497368755277501

theorem tailTrace_6487399 : CollatzResearch.WordTrace tailWord_6487399 prefixEnd_6487399 3331153884497368755277501 := by
  unfold tailWord_6487399
  simp only [CollatzResearch.WordTrace]
  refine ⟨236614880224268857385145251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157743253482845904923430167 236614880224268857385145251)
  ·
    refine ⟨354922320336403286077717877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236614880224268857385145251 354922320336403286077717877)
    ·
      refine ⟨33273967531537808069786051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 354922320336403286077717877 33273967531537808069786051)
      ·
        refine ⟨49910951297306712104679077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33273967531537808069786051 49910951297306712104679077)
        ·
          refine ⟨9358303368245008519627327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49910951297306712104679077 9358303368245008519627327)
          ·
            refine ⟨14037455052367512779440991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9358303368245008519627327 14037455052367512779440991)
            ·
              refine ⟨21056182578551269169161487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14037455052367512779440991 21056182578551269169161487)
              ·
                refine ⟨31584273867826903753742231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21056182578551269169161487 31584273867826903753742231)
                ·
                  refine ⟨47376410801740355630613347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31584273867826903753742231 47376410801740355630613347)
                  ·
                    refine ⟨71064616202610533445920021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47376410801740355630613347 71064616202610533445920021)
                    ·
                      refine ⟨3331153884497368755277501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71064616202610533445920021 3331153884497368755277501)
                      ·
                        rfl

theorem cell23_6487399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_6487399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487399 prefixEnd_6487399 := by exact prefixLift 6487399
  have htrace : WordTrace (prefixWord ++ tailWord_6487399) baseStart_6487399 baseEnd_6487399 := by
    simpa [prefixWord, tailWord_6487399, baseEnd_6487399] using wordTrace_append hprefix tailTrace_6487399
  have hstable : (prefixWord ++ tailWord_6487399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487399).length < 2 ^ (prefixWord ++ tailWord_6487399).sum := by decide
  have hdescent : baseEnd_6487399 < baseStart_6487399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487419 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 3]
def baseStart_6487419 : Nat := 118140960795 + 6487419 * 2 ^ 59
def prefixEnd_6487419 : Nat := 4983230072969 + 3 ^ 40 * 6487419 * 2
def baseEnd_6487419 : Nat := 3331164154110458677027409

theorem tailTrace_6487419 : CollatzResearch.WordTrace tailWord_6487419 prefixEnd_6487419 3331164154110458677027409 := by
  unfold tailWord_6487419
  simp only [CollatzResearch.WordTrace]
  refine ⟨236615609684196400800873311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157743739789464267200582207 236615609684196400800873311)
  ·
    refine ⟨354923414526294601201309967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236615609684196400800873311 354923414526294601201309967)
    ·
      refine ⟨532385121789441901801964951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354923414526294601201309967 532385121789441901801964951)
      ·
        refine ⟨798577682684162852702947427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532385121789441901801964951 798577682684162852702947427)
        ·
          refine ⟨1197866524026244279054421141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798577682684162852702947427 1197866524026244279054421141)
          ·
            refine ⟨56149993313730200580675991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1197866524026244279054421141 56149993313730200580675991)
            ·
              refine ⟨84224989970595300871013987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56149993313730200580675991 84224989970595300871013987)
              ·
                refine ⟨126337484955892951306520981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84224989970595300871013987 126337484955892951306520981)
                ·
                  refine ⟨5922069607307482092493171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126337484955892951306520981 5922069607307482092493171)
                  ·
                    refine ⟨8883104410961223138739757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5922069607307482092493171 8883104410961223138739757)
                    ·
                      refine ⟨3331164154110458677027409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883104410961223138739757 3331164154110458677027409)
                      ·
                        rfl

theorem cell23_6487419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 3].length) (baseStart_6487419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487419 prefixEnd_6487419 := by exact prefixLift 6487419
  have htrace : WordTrace (prefixWord ++ tailWord_6487419) baseStart_6487419 baseEnd_6487419 := by
    simpa [prefixWord, tailWord_6487419, baseEnd_6487419] using wordTrace_append hprefix tailTrace_6487419
  have hstable : (prefixWord ++ tailWord_6487419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487419).length < 2 ^ (prefixWord ++ tailWord_6487419).sum := by decide
  have hdescent : baseEnd_6487419 < baseStart_6487419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487426 : List Nat := [3, 4, 2, 1, 1, 3, 9]
def baseStart_6487426 : Nat := 118140960795 + 6487426 * 2 ^ 59
def prefixEnd_6487426 : Nat := 4983230072969 + 3 ^ 40 * 6487426 * 2
def baseEnd_6487426 : Nat := 41125527758951112958517

theorem tailTrace_6487426 : CollatzResearch.WordTrace tailWord_6487426 prefixEnd_6487426 41125527758951112958517 := by
  unfold tailWord_6487426
  simp only [CollatzResearch.WordTrace]
  refine ⟨59153966248792760249094533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157743909996780693997585421 59153966248792760249094533)
  ·
    refine ⟨11091368671648642546705225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59153966248792760249094533 11091368671648642546705225)
    ·
      refine ⟨8318526503736481910028919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11091368671648642546705225 8318526503736481910028919)
      ·
        refine ⟨12477789755604722865043379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8318526503736481910028919 12477789755604722865043379)
        ·
          refine ⟨18716684633407084297565069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12477789755604722865043379 18716684633407084297565069)
          ·
            refine ⟨7018756737527656611586901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18716684633407084297565069 7018756737527656611586901)
            ·
              refine ⟨41125527758951112958517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7018756737527656611586901 41125527758951112958517)
              ·
                rfl

theorem cell23_6487426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 9].length) (baseStart_6487426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487426 prefixEnd_6487426 := by exact prefixLift 6487426
  have htrace : WordTrace (prefixWord ++ tailWord_6487426) baseStart_6487426 baseEnd_6487426 := by
    simpa [prefixWord, tailWord_6487426, baseEnd_6487426] using wordTrace_append hprefix tailTrace_6487426
  have hstable : (prefixWord ++ tailWord_6487426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487426).length < 2 ^ (prefixWord ++ tailWord_6487426).sum := by decide
  have hdescent : baseEnd_6487426 < baseStart_6487426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487436 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_6487436 : Nat := 118140960795 + 6487436 * 2 ^ 59
def prefixEnd_6487436 : Nat := 4983230072969 + 3 ^ 40 * 6487436 * 2
def baseEnd_6487436 : Nat := 3331172883281585110514831

theorem tailTrace_6487436 : CollatzResearch.WordTrace tailWord_6487436 prefixEnd_6487436 3331172883281585110514831 := by
  unfold tailWord_6487436
  simp only [CollatzResearch.WordTrace]
  refine ⟨118308114862567406352121081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157744153150089875136161441 118308114862567406352121081)
  ·
    refine ⟨88731086146925554764090811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118308114862567406352121081 88731086146925554764090811)
    ·
      refine ⟨133096629220388332146136217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88731086146925554764090811 133096629220388332146136217)
      ·
        refine ⟨99822471915291249109602163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133096629220388332146136217 99822471915291249109602163)
        ·
          refine ⟨149733707872936873664403245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99822471915291249109602163 149733707872936873664403245)
          ·
            refine ⟨56150140452351327624151217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149733707872936873664403245 56150140452351327624151217)
            ·
              refine ⟨42112605339263495718113413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56150140452351327624151217 42112605339263495718113413)
              ·
                refine ⟨7896113501111905447146265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42112605339263495718113413 7896113501111905447146265)
                ·
                  refine ⟨5922085125833929085359699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7896113501111905447146265 5922085125833929085359699)
                  ·
                    refine ⟨8883127688750893628039549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5922085125833929085359699 8883127688750893628039549)
                    ·
                      refine ⟨3331172883281585110514831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883127688750893628039549 3331172883281585110514831)
                      ·
                        rfl

theorem cell23_6487436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_6487436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487436 prefixEnd_6487436 := by exact prefixLift 6487436
  have htrace : WordTrace (prefixWord ++ tailWord_6487436) baseStart_6487436 baseEnd_6487436 := by
    simpa [prefixWord, tailWord_6487436, baseEnd_6487436] using wordTrace_append hprefix tailTrace_6487436
  have hstable : (prefixWord ++ tailWord_6487436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487436).length < 2 ^ (prefixWord ++ tailWord_6487436).sum := by decide
  have hdescent : baseEnd_6487436 < baseStart_6487436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487453 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_6487453 : Nat := 118140960795 + 6487453 * 2 ^ 59
def prefixEnd_6487453 : Nat := 4983230072969 + 3 ^ 40 * 6487453 * 2
def baseEnd_6487453 : Nat := 3331181612452711544002253

theorem tailTrace_6487453 : CollatzResearch.WordTrace tailWord_6487453 prefixEnd_6487453 3331181612452711544002253 := by
  unfold tailWord_6487453
  simp only [CollatzResearch.WordTrace]
  refine ⟨236616849766073224607611013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157744566510715483071740675 236616849766073224607611013)
  ·
    refine ⟨44365659331138729613927065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236616849766073224607611013 44365659331138729613927065)
    ·
      refine ⟨33274244498354047210445299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44365659331138729613927065 33274244498354047210445299)
      ·
        refine ⟨49911366747531070815667949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33274244498354047210445299 49911366747531070815667949)
        ·
          refine ⟨18716762530324151555875481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49911366747531070815667949 18716762530324151555875481)
          ·
            refine ⟨14037571897743113666906611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18716762530324151555875481 14037571897743113666906611)
            ·
              refine ⟨21056357846614670500359917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14037571897743113666906611 21056357846614670500359917)
              ·
                refine ⟨7896134192480501437634969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21056357846614670500359917 7896134192480501437634969)
                ·
                  refine ⟨5922100644360376078226227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7896134192480501437634969 5922100644360376078226227)
                  ·
                    refine ⟨8883150966540564117339341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5922100644360376078226227 8883150966540564117339341)
                    ·
                      refine ⟨3331181612452711544002253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883150966540564117339341 3331181612452711544002253)
                      ·
                        rfl

theorem cell23_6487453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_6487453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487453 prefixEnd_6487453 := by exact prefixLift 6487453
  have htrace : WordTrace (prefixWord ++ tailWord_6487453) baseStart_6487453 baseEnd_6487453 := by
    simpa [prefixWord, tailWord_6487453, baseEnd_6487453] using wordTrace_append hprefix tailTrace_6487453
  have hstable : (prefixWord ++ tailWord_6487453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487453).length < 2 ^ (prefixWord ++ tailWord_6487453).sum := by decide
  have hdescent : baseEnd_6487453 < baseStart_6487453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487472 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_6487472 : Nat := 118140960795 + 6487472 * 2 ^ 59
def prefixEnd_6487472 : Nat := 4983230072969 + 3 ^ 40 * 6487472 * 2
def baseEnd_6487472 : Nat := 3331191368585146969664665

theorem tailTrace_6487472 : CollatzResearch.WordTrace tailWord_6487472 prefixEnd_6487472 3331191368585146969664665 := by
  unfold tailWord_6487472
  simp only [CollatzResearch.WordTrace]
  refine ⟨118308771376502195426276335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157745028502002927235035113 118308771376502195426276335)
  ·
    refine ⟨177463157064753293139414503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118308771376502195426276335 177463157064753293139414503)
    ·
      refine ⟨266194735597129939709121755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177463157064753293139414503 266194735597129939709121755)
      ·
        refine ⟨399292103395694909563682633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266194735597129939709121755 399292103395694909563682633)
        ·
          refine ⟨299469077546771182172761975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399292103395694909563682633 299469077546771182172761975)
          ·
            refine ⟨449203616320156773259142963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299469077546771182172761975 449203616320156773259142963)
            ·
              refine ⟨673805424480235159888714445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449203616320156773259142963 673805424480235159888714445)
              ·
                refine ⟨252677034180088184958267917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673805424480235159888714445 252677034180088184958267917)
                ·
                  refine ⟨94753887817533069359350469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252677034180088184958267917 94753887817533069359350469)
                  ·
                    refine ⟨17766353965787450504878213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94753887817533069359350469 17766353965787450504878213)
                    ·
                      refine ⟨3331191368585146969664665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17766353965787450504878213 3331191368585146969664665)
                      ·
                        rfl

theorem cell23_6487472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_6487472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487472 prefixEnd_6487472 := by exact prefixLift 6487472
  have htrace : WordTrace (prefixWord ++ tailWord_6487472) baseStart_6487472 baseEnd_6487472 := by
    simpa [prefixWord, tailWord_6487472, baseEnd_6487472] using wordTrace_append hprefix tailTrace_6487472
  have hstable : (prefixWord ++ tailWord_6487472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487472).length < 2 ^ (prefixWord ++ tailWord_6487472).sum := by decide
  have hdescent : baseEnd_6487472 < baseStart_6487472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487510 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_6487510 : Nat := 118140960795 + 6487510 * 2 ^ 59
def prefixEnd_6487510 : Nat := 4983230072969 + 3 ^ 40 * 6487510 * 2
def baseEnd_6487510 : Nat := 3331210880850017820989491

theorem tailTrace_6487510 : CollatzResearch.WordTrace tailWord_6487510 prefixEnd_6487510 3331210880850017820989491 := by
  unfold tailWord_6487510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788683045429170208902249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157745952484577815561623989 14788683045429170208902249)
  ·
    refine ⟨11091512284071877656676687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14788683045429170208902249 11091512284071877656676687)
    ·
      refine ⟨16637268426107816485015031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11091512284071877656676687 16637268426107816485015031)
      ·
        refine ⟨24955902639161724727522547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16637268426107816485015031 24955902639161724727522547)
        ·
          refine ⟨37433853958742587091283821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24955902639161724727522547 37433853958742587091283821)
          ·
            refine ⟨14037695234528470159231433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37433853958742587091283821 14037695234528470159231433)
            ·
              refine ⟨10528271425896352619423575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14037695234528470159231433 10528271425896352619423575)
              ·
                refine ⟨15792407138844528929135363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528271425896352619423575 15792407138844528929135363)
                ·
                  refine ⟨23688610708266793393703045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15792407138844528929135363 23688610708266793393703045)
                  ·
                    refine ⟨4441614507800023761319321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23688610708266793393703045 4441614507800023761319321)
                    ·
                      refine ⟨3331210880850017820989491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441614507800023761319321 3331210880850017820989491)
                      ·
                        rfl

theorem cell23_6487510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_6487510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487510 prefixEnd_6487510 := by exact prefixLift 6487510
  have htrace : WordTrace (prefixWord ++ tailWord_6487510) baseStart_6487510 baseEnd_6487510 := by
    simpa [prefixWord, tailWord_6487510, baseEnd_6487510] using wordTrace_append hprefix tailTrace_6487510
  have hstable : (prefixWord ++ tailWord_6487510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487510).length < 2 ^ (prefixWord ++ tailWord_6487510).sum := by decide
  have hdescent : baseEnd_6487510 < baseStart_6487510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487569 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_6487569 : Nat := 118140960795 + 6487569 * 2 ^ 59
def prefixEnd_6487569 : Nat := 4983230072969 + 3 ^ 40 * 6487569 * 2
def baseEnd_6487569 : Nat := 3331241176208633090151719

theorem tailTrace_6487569 : CollatzResearch.WordTrace tailWord_6487569 prefixEnd_6487569 3331241176208633090151719 := by
  unfold tailWord_6487569
  simp only [CollatzResearch.WordTrace]
  refine ⟨236621080633652976418833761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157747387089101984279222507 236621080633652976418833761)
  ·
    refine ⟨177465810475239732314125321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236621080633652976418833761 177465810475239732314125321)
    ·
      refine ⟨133099357856429799235593991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177465810475239732314125321 133099357856429799235593991)
      ·
        refine ⟨199649036784644698853390987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133099357856429799235593991 199649036784644698853390987)
        ·
          refine ⟨299473555176967048280086481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199649036784644698853390987 299473555176967048280086481)
          ·
            refine ⟨224605166382725286210064861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299473555176967048280086481 224605166382725286210064861)
            ·
              refine ⟨84226937393521982328774323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224605166382725286210064861 84226937393521982328774323)
              ·
                refine ⟨126340406090282973493161485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84226937393521982328774323 126340406090282973493161485)
                ·
                  refine ⟨47377652283856115059935557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126340406090282973493161485 47377652283856115059935557)
                  ·
                    refine ⟨8883309803223021573737917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47377652283856115059935557 8883309803223021573737917)
                    ·
                      refine ⟨3331241176208633090151719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883309803223021573737917 3331241176208633090151719)
                      ·
                        rfl

theorem cell23_6487569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_6487569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487569 prefixEnd_6487569 := by exact prefixLift 6487569
  have htrace : WordTrace (prefixWord ++ tailWord_6487569) baseStart_6487569 baseEnd_6487569 := by
    simpa [prefixWord, tailWord_6487569, baseEnd_6487569] using wordTrace_append hprefix tailTrace_6487569
  have hstable : (prefixWord ++ tailWord_6487569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487569).length < 2 ^ (prefixWord ++ tailWord_6487569).sum := by decide
  have hdescent : baseEnd_6487569 < baseStart_6487569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487586 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_6487586 : Nat := 118140960795 + 6487586 * 2 ^ 59
def prefixEnd_6487586 : Nat := 4983230072969 + 3 ^ 40 * 6487586 * 2
def baseEnd_6487586 : Nat := 3331249905379759523639141

theorem tailTrace_6487586 : CollatzResearch.WordTrace tailWord_6487586 prefixEnd_6487586 3331249905379759523639141 := by
  unfold tailWord_6487586
  simp only [CollatzResearch.WordTrace]
  refine ⟨59155425168647847080550653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157747800449727592214801741 59155425168647847080550653)
  ·
    refine ⟨22183284438242942655206495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59155425168647847080550653 22183284438242942655206495)
    ·
      refine ⟨33274926657364413982809743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22183284438242942655206495 33274926657364413982809743)
      ·
        refine ⟨49912389986046620974214615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33274926657364413982809743 49912389986046620974214615)
        ·
          refine ⟨74868584979069931461321923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49912389986046620974214615 74868584979069931461321923)
          ·
            refine ⟨112302877468604897191982885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74868584979069931461321923 112302877468604897191982885)
            ·
              refine ⟨21056789525363418223496791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112302877468604897191982885 21056789525363418223496791)
              ·
                refine ⟨31585184288045127335245187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21056789525363418223496791 31585184288045127335245187)
                ·
                  refine ⟨47377776432067691002867781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31585184288045127335245187 47377776432067691002867781)
                  ·
                    refine ⟨8883333081012692063037709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47377776432067691002867781 8883333081012692063037709)
                    ·
                      refine ⟨3331249905379759523639141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883333081012692063037709 3331249905379759523639141)
                      ·
                        rfl

theorem cell23_6487586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_6487586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487586 prefixEnd_6487586 := by exact prefixLift 6487586
  have htrace : WordTrace (prefixWord ++ tailWord_6487586) baseStart_6487586 baseEnd_6487586 := by
    simpa [prefixWord, tailWord_6487586, baseEnd_6487586] using wordTrace_append hprefix tailTrace_6487586
  have hstable : (prefixWord ++ tailWord_6487586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487586).length < 2 ^ (prefixWord ++ tailWord_6487586).sum := by decide
  have hdescent : baseEnd_6487586 < baseStart_6487586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487610 : List Nat := [3, 1, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_6487610 : Nat := 118140960795 + 6487610 * 2 ^ 59
def prefixEnd_6487610 : Nat := 4983230072969 + 3 ^ 40 * 6487610 * 2
def baseEnd_6487610 : Nat := 1110420742971822476579677

theorem tailTrace_6487610 : CollatzResearch.WordTrace tailWord_6487610 prefixEnd_6487610 1110420742971822476579677 := by
  unfold tailWord_6487610
  simp only [CollatzResearch.WordTrace]
  refine ⟨59155644006626110105269071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157748384017669626947384189 59155644006626110105269071)
  ·
    refine ⟨88733466009939165157903607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59155644006626110105269071 88733466009939165157903607)
    ·
      refine ⟨133100199014908747736855411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88733466009939165157903607 133100199014908747736855411)
      ·
        refine ⟨199650298522363121605283117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133100199014908747736855411 199650298522363121605283117)
        ·
          refine ⟨74868861945886170601981169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199650298522363121605283117 74868861945886170601981169)
          ·
            refine ⟨56151646459414627951485877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74868861945886170601981169 56151646459414627951485877)
            ·
              refine ⟨5264216855570121370451801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56151646459414627951485877 5264216855570121370451801)
              ·
                refine ⟨3948162641677591027838851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5264216855570121370451801 3948162641677591027838851)
                ·
                  refine ⟨5922243962516386541758277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948162641677591027838851 5922243962516386541758277)
                  ·
                    refine ⟨1110420742971822476579677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5922243962516386541758277 1110420742971822476579677)
                    ·
                      rfl

theorem cell23_6487610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_6487610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487610 prefixEnd_6487610 := by exact prefixLift 6487610
  have htrace : WordTrace (prefixWord ++ tailWord_6487610) baseStart_6487610 baseEnd_6487610 := by
    simpa [prefixWord, tailWord_6487610, baseEnd_6487610] using wordTrace_append hprefix tailTrace_6487610
  have hstable : (prefixWord ++ tailWord_6487610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487610).length < 2 ^ (prefixWord ++ tailWord_6487610).sum := by decide
  have hdescent : baseEnd_6487610 < baseStart_6487610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487636 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_6487636 : Nat := 118140960795 + 6487636 * 2 ^ 59
def prefixEnd_6487636 : Nat := 4983230072969 + 3 ^ 40 * 6487636 * 2
def baseEnd_6487636 : Nat := 1110425193137494776004637

theorem tailTrace_6487636 : CollatzResearch.WordTrace tailWord_6487636 prefixEnd_6487636 1110425193137494776004637 := by
  unfold tailWord_6487636
  simp only [CollatzResearch.WordTrace]
  refine ⟨118311762162205123430761381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157749016216273497907681841 118311762162205123430761381)
  ·
    refine ⟨22183455405413460643267759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118311762162205123430761381 22183455405413460643267759)
    ·
      refine ⟨33275183108120190964901639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22183455405413460643267759 33275183108120190964901639)
      ·
        refine ⟨49912774662180286447352459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33275183108120190964901639 49912774662180286447352459)
        ·
          refine ⟨74869161993270429671028689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49912774662180286447352459 74869161993270429671028689)
          ·
            refine ⟨56151871494952822253271517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74869161993270429671028689 56151871494952822253271517)
            ·
              refine ⟨21056951810607308344976819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56151871494952822253271517 21056951810607308344976819)
              ·
                refine ⟨31585427715910962517465229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21056951810607308344976819 31585427715910962517465229)
                ·
                  refine ⟨11844535393466610944049461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31585427715910962517465229 11844535393466610944049461)
                  ·
                    refine ⟨1110425193137494776004637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11844535393466610944049461 1110425193137494776004637)
                    ·
                      rfl

theorem cell23_6487636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_6487636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487636 prefixEnd_6487636 := by exact prefixLift 6487636
  have htrace : WordTrace (prefixWord ++ tailWord_6487636) baseStart_6487636 baseEnd_6487636 := by
    simpa [prefixWord, tailWord_6487636, baseEnd_6487636] using wordTrace_append hprefix tailTrace_6487636
  have hstable : (prefixWord ++ tailWord_6487636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487636).length < 2 ^ (prefixWord ++ tailWord_6487636).sum := by decide
  have hdescent : baseEnd_6487636 < baseStart_6487636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487690 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_6487690 : Nat := 118140960795 + 6487690 * 2 ^ 59
def prefixEnd_6487690 : Nat := 4983230072969 + 3 ^ 40 * 6487690 * 2
def baseEnd_6487690 : Nat := 3331303307367827116738663

theorem tailTrace_6487690 : CollatzResearch.WordTrace tailWord_6487690 prefixEnd_6487690 3331303307367827116738663 := by
  unfold tailWord_6487690
  simp only [CollatzResearch.WordTrace]
  refine ⟨59156373466553653520997131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157750329244143076055992349 59156373466553653520997131)
  ·
    refine ⟨88734560199830480281495697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59156373466553653520997131 88734560199830480281495697)
    ·
      refine ⟨66550920149872860211121773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88734560199830480281495697 66550920149872860211121773)
      ·
        refine ⟨24956595056202322579170665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66550920149872860211121773 24956595056202322579170665)
        ·
          refine ⟨18717446292151741934377999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24956595056202322579170665 18717446292151741934377999)
          ·
            refine ⟨28076169438227612901566999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18717446292151741934377999 28076169438227612901566999)
            ·
              refine ⟨42114254157341419352350499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28076169438227612901566999 42114254157341419352350499)
              ·
                refine ⟨63171381236012129028525749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42114254157341419352350499 63171381236012129028525749)
                ·
                  refine ⟨5922316990876137096424289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63171381236012129028525749 5922316990876137096424289)
                  ·
                    refine ⟨4441737743157102822318217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5922316990876137096424289 4441737743157102822318217)
                    ·
                      refine ⟨3331303307367827116738663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441737743157102822318217 3331303307367827116738663)
                      ·
                        rfl

theorem cell23_6487690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_6487690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487690 prefixEnd_6487690 := by exact prefixLift 6487690
  have htrace : WordTrace (prefixWord ++ tailWord_6487690) baseStart_6487690 baseEnd_6487690 := by
    simpa [prefixWord, tailWord_6487690, baseEnd_6487690] using wordTrace_append hprefix tailTrace_6487690
  have hstable : (prefixWord ++ tailWord_6487690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487690).length < 2 ^ (prefixWord ++ tailWord_6487690).sum := by decide
  have hdescent : baseEnd_6487690 < baseStart_6487690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487734 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6487734 : Nat := 118140960795 + 6487734 * 2 ^ 59
def prefixEnd_6487734 : Nat := 4983230072969 + 3 ^ 40 * 6487734 * 2
def baseEnd_6487734 : Nat := 1110441966838874981529487

theorem tailTrace_6487734 : CollatzResearch.WordTrace tailWord_6487734 prefixEnd_6487734 1110441966838874981529487 := by
  unfold tailWord_6487734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14789193667378450599911891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157751399118703473065726837 14789193667378450599911891)
  ·
    refine ⟨22183790501067675899867837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14789193667378450599911891 22183790501067675899867837)
    ·
      refine ⟨8318921437900378462450439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22183790501067675899867837 8318921437900378462450439)
      ·
        refine ⟨12478382156850567693675659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8318921437900378462450439 12478382156850567693675659)
        ·
          refine ⟨18717573235275851540513489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12478382156850567693675659 18717573235275851540513489)
          ·
            refine ⟨14038179926456888655385117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18717573235275851540513489 14038179926456888655385117)
            ·
              refine ⟨5264317472421333245769419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14038179926456888655385117 5264317472421333245769419)
              ·
                refine ⟨7896476208631999868654129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5264317472421333245769419 7896476208631999868654129)
                ·
                  refine ⟨5922357156473999901490597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7896476208631999868654129 5922357156473999901490597)
                  ·
                    refine ⟨1110441966838874981529487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5922357156473999901490597 1110441966838874981529487)
                    ·
                      rfl

theorem cell23_6487734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6487734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487734 prefixEnd_6487734 := by exact prefixLift 6487734
  have htrace : WordTrace (prefixWord ++ tailWord_6487734) baseStart_6487734 baseEnd_6487734 := by
    simpa [prefixWord, tailWord_6487734, baseEnd_6487734] using wordTrace_append hprefix tailTrace_6487734
  have hstable : (prefixWord ++ tailWord_6487734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487734).length < 2 ^ (prefixWord ++ tailWord_6487734).sum := by decide
  have hdescent : baseEnd_6487734 < baseStart_6487734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487740 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_6487740 : Nat := 118140960795 + 6487740 * 2 ^ 59
def prefixEnd_6487740 : Nat := 4983230072969 + 3 ^ 40 * 6487740 * 2
def baseEnd_6487740 : Nat := 3331328981400551921113433

theorem tailTrace_6487740 : CollatzResearch.WordTrace tailWord_6487740 prefixEnd_6487740 3331328981400551921113433 := by
  unfold tailWord_6487740
  simp only [CollatzResearch.WordTrace]
  refine ⟨118313658758016736311654337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157751545010688981748872449 118313658758016736311654337)
  ·
    refine ⟨88735244068512552233740753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118313658758016736311654337 88735244068512552233740753)
    ·
      refine ⟨66551433051384414175305565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88735244068512552233740753 66551433051384414175305565)
      ·
        refine ⟨24956787394269155315739587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66551433051384414175305565 24956787394269155315739587)
        ·
          refine ⟨37435181091403732973609381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24956787394269155315739587 37435181091403732973609381)
          ·
            refine ⟨7019096454638199932551759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37435181091403732973609381 7019096454638199932551759)
            ·
              refine ⟨10528644681957299898827639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019096454638199932551759 10528644681957299898827639)
              ·
                refine ⟨15792967022935949848241459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528644681957299898827639 15792967022935949848241459)
                ·
                  refine ⟨23689450534403924772362189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15792967022935949848241459 23689450534403924772362189)
                  ·
                    refine ⟨8883543950401471789635821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23689450534403924772362189 8883543950401471789635821)
                    ·
                      refine ⟨3331328981400551921113433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883543950401471789635821 3331328981400551921113433)
                      ·
                        rfl

theorem cell23_6487740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_6487740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487740 prefixEnd_6487740 := by exact prefixLift 6487740
  have htrace : WordTrace (prefixWord ++ tailWord_6487740) baseStart_6487740 baseEnd_6487740 := by
    simpa [prefixWord, tailWord_6487740, baseEnd_6487740] using wordTrace_append hprefix tailTrace_6487740
  have hstable : (prefixWord ++ tailWord_6487740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487740).length < 2 ^ (prefixWord ++ tailWord_6487740).sum := by decide
  have hdescent : baseEnd_6487740 < baseStart_6487740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487757 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6487757 : Nat := 118140960795 + 6487757 * 2 ^ 59
def prefixEnd_6487757 : Nat := 4983230072969 + 3 ^ 40 * 6487757 * 2
def baseEnd_6487757 : Nat := 3331337710571678354600855

theorem tailTrace_6487757 : CollatzResearch.WordTrace tailWord_6487757 prefixEnd_6487757 3331337710571678354600855 := by
  unfold tailWord_6487757
  simp only [CollatzResearch.WordTrace]
  refine ⟨236627937556971884526677525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157751958371314589684451683 236627937556971884526677525)
  ·
    refine ⟨11091934572983057087188009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236627937556971884526677525 11091934572983057087188009)
    ·
      refine ⟨8318950929737292815391007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11091934572983057087188009 8318950929737292815391007)
      ·
        refine ⟨12478426394605939223086511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8318950929737292815391007 12478426394605939223086511)
        ·
          refine ⟨18717639591908908834629767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12478426394605939223086511 18717639591908908834629767)
          ·
            refine ⟨28076459387863363251944651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18717639591908908834629767 28076459387863363251944651)
            ·
              refine ⟨42114689081795044877916977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28076459387863363251944651 42114689081795044877916977)
              ·
                refine ⟨31586016811346283658437733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42114689081795044877916977 31586016811346283658437733)
                ·
                  refine ⟨5922378152127428185957075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31586016811346283658437733 5922378152127428185957075)
                  ·
                    refine ⟨8883567228191142278935613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5922378152127428185957075 8883567228191142278935613)
                    ·
                      refine ⟨3331337710571678354600855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883567228191142278935613 3331337710571678354600855)
                      ·
                        rfl

theorem cell23_6487757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6487757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487757 prefixEnd_6487757 := by exact prefixLift 6487757
  have htrace : WordTrace (prefixWord ++ tailWord_6487757) baseStart_6487757 baseEnd_6487757 := by
    simpa [prefixWord, tailWord_6487757, baseEnd_6487757] using wordTrace_append hprefix tailTrace_6487757
  have hstable : (prefixWord ++ tailWord_6487757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487757).length < 2 ^ (prefixWord ++ tailWord_6487757).sum := by decide
  have hdescent : baseEnd_6487757 < baseStart_6487757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487776 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_6487776 : Nat := 118140960795 + 6487776 * 2 ^ 59
def prefixEnd_6487776 : Nat := 4983230072969 + 3 ^ 40 * 6487776 * 2
def baseEnd_6487776 : Nat := 3331347466704113780263267

theorem tailTrace_6487776 : CollatzResearch.WordTrace tailWord_6487776 prefixEnd_6487776 3331347466704113780263267 := by
  unfold tailWord_6487776
  simp only [CollatzResearch.WordTrace]
  refine ⟨118314315271951525385809591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157752420362602033847746121 118314315271951525385809591)
  ·
    refine ⟨177471472907927288078714387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118314315271951525385809591 177471472907927288078714387)
    ·
      refine ⟨266207209361890932118071581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177471472907927288078714387 266207209361890932118071581)
      ·
        refine ⟨99827703510709099544276843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266207209361890932118071581 99827703510709099544276843)
        ·
          refine ⟨149741555266063649316415265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99827703510709099544276843 149741555266063649316415265)
          ·
            refine ⟨112306166449547736987311449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149741555266063649316415265 112306166449547736987311449)
            ·
              refine ⟨84229624837160802740483587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112306166449547736987311449 84229624837160802740483587)
              ·
                refine ⟨126344437255741204110725381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84229624837160802740483587 126344437255741204110725381)
                ·
                  refine ⟨23689581985451475770761009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126344437255741204110725381 23689581985451475770761009)
                  ·
                    refine ⟨17767186489088606828070757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23689581985451475770761009 17767186489088606828070757)
                    ·
                      refine ⟨3331347466704113780263267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17767186489088606828070757 3331347466704113780263267)
                      ·
                        rfl

theorem cell23_6487776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_6487776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487776 prefixEnd_6487776 := by exact prefixLift 6487776
  have htrace : WordTrace (prefixWord ++ tailWord_6487776) baseStart_6487776 baseEnd_6487776 := by
    simpa [prefixWord, tailWord_6487776, baseEnd_6487776] using wordTrace_append hprefix tailTrace_6487776
  have hstable : (prefixWord ++ tailWord_6487776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487776).length < 2 ^ (prefixWord ++ tailWord_6487776).sum := by decide
  have hdescent : baseEnd_6487776 < baseStart_6487776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487780 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_6487780 : Nat := 118140960795 + 6487780 * 2 ^ 59
def prefixEnd_6487780 : Nat := 4983230072969 + 3 ^ 40 * 6487780 * 2
def baseEnd_6487780 : Nat := 3331349520626731764613249

theorem tailTrace_6487780 : CollatzResearch.WordTrace tailWord_6487780 prefixEnd_6487780 3331349520626731764613249 := by
  unfold tailWord_6487780
  simp only [CollatzResearch.WordTrace]
  refine ⟨118314388217944279727382397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157752517623925706303176529 118314388217944279727382397)
  ·
    refine ⟨44367895581729104897768399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118314388217944279727382397 44367895581729104897768399)
    ·
      refine ⟨66551843372593657346652599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44367895581729104897768399 66551843372593657346652599)
      ·
        refine ⟨99827765058890486019978899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66551843372593657346652599 99827765058890486019978899)
        ·
          refine ⟨149741647588335729029968349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99827765058890486019978899 149741647588335729029968349)
          ·
            refine ⟨56153117845625898386238131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149741647588335729029968349 56153117845625898386238131)
            ·
              refine ⟨84229676768438847579357197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56153117845625898386238131 84229676768438847579357197)
              ·
                refine ⟨31586128788164567842258949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84229676768438847579357197 31586128788164567842258949)
                ·
                  refine ⟨5922399147780856470423553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31586128788164567842258949 5922399147780856470423553)
                  ·
                    refine ⟨4441799360835642352817665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5922399147780856470423553 4441799360835642352817665)
                    ·
                      refine ⟨3331349520626731764613249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441799360835642352817665 3331349520626731764613249)
                      ·
                        rfl

theorem cell23_6487780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_6487780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487780 prefixEnd_6487780 := by exact prefixLift 6487780
  have htrace : WordTrace (prefixWord ++ tailWord_6487780) baseStart_6487780 baseEnd_6487780 := by
    simpa [prefixWord, tailWord_6487780, baseEnd_6487780] using wordTrace_append hprefix tailTrace_6487780
  have hstable : (prefixWord ++ tailWord_6487780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487780).length < 2 ^ (prefixWord ++ tailWord_6487780).sum := by decide
  have hdescent : baseEnd_6487780 < baseStart_6487780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487870 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_6487870 : Nat := 118140960795 + 6487870 * 2 ^ 59
def prefixEnd_6487870 : Nat := 4983230072969 + 3 ^ 40 * 6487870 * 2
def baseEnd_6487870 : Nat := 3331395733885636412487835

theorem tailTrace_6487870 : CollatzResearch.WordTrace tailWord_6487870 prefixEnd_6487870 3331395733885636412487835 := by
  unfold tailWord_6487870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29579007375695313103192633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157754706003708336550360709 29579007375695313103192633)
  ·
    refine ⟨22184255531771484827394475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29579007375695313103192633 22184255531771484827394475)
    ·
      refine ⟨33276383297657227241091713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22184255531771484827394475 33276383297657227241091713)
      ·
        refine ⟨24957287473242920430818785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33276383297657227241091713 24957287473242920430818785)
        ·
          refine ⟨18717965604932190323114089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24957287473242920430818785 18717965604932190323114089)
          ·
            refine ⟨14038474203699142742335567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18717965604932190323114089 14038474203699142742335567)
            ·
              refine ⟨21057711305548714113503351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14038474203699142742335567 21057711305548714113503351)
              ·
                refine ⟨31586566958323071170255027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21057711305548714113503351 31586566958323071170255027)
                ·
                  refine ⟨47379850437484606755382541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31586566958323071170255027 47379850437484606755382541)
                  ·
                    refine ⟨17767443914056727533268453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47379850437484606755382541 17767443914056727533268453)
                    ·
                      refine ⟨3331395733885636412487835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17767443914056727533268453 3331395733885636412487835)
                      ·
                        rfl

theorem cell23_6487870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_6487870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487870 prefixEnd_6487870 := by exact prefixLift 6487870
  have htrace : WordTrace (prefixWord ++ tailWord_6487870) baseStart_6487870 baseEnd_6487870 := by
    simpa [prefixWord, tailWord_6487870, baseEnd_6487870] using wordTrace_append hprefix tailTrace_6487870
  have hstable : (prefixWord ++ tailWord_6487870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487870).length < 2 ^ (prefixWord ++ tailWord_6487870).sum := by decide
  have hdescent : baseEnd_6487870 < baseStart_6487870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487893 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 8]
def baseStart_6487893 : Nat := 118140960795 + 6487893 * 2 ^ 59
def prefixEnd_6487893 : Nat := 4983230072969 + 3 ^ 40 * 6487893 * 2
def baseEnd_6487893 : Nat := 370156393771187758055581

theorem tailTrace_6487893 : CollatzResearch.WordTrace tailWord_6487893 prefixEnd_6487893 370156393771187758055581 := by
  unfold tailWord_6487893
  simp only [CollatzResearch.WordTrace]
  refine ⟨236632897884479179753628333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157755265256319453169085555 236632897884479179753628333)
  ·
    refine ⟨88737336706679692407610625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236632897884479179753628333 88737336706679692407610625)
    ·
      refine ⟨66553002530009769305707969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88737336706679692407610625 66553002530009769305707969)
      ·
        refine ⟨49914751897507326979280977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66553002530009769305707969 49914751897507326979280977)
        ·
          refine ⟨37436063923130495234460733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49914751897507326979280977 37436063923130495234460733)
          ·
            refine ⟨14038523971173935712922775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37436063923130495234460733 14038523971173935712922775)
            ·
              refine ⟨21057785956760903569384163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14038523971173935712922775 21057785956760903569384163)
              ·
                refine ⟨31586678935141355354076245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21057785956760903569384163 31586678935141355354076245)
                ·
                  refine ⟨370156393771187758055581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31586678935141355354076245 370156393771187758055581)
                  ·
                    rfl

theorem cell23_6487893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_6487893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487893 prefixEnd_6487893 := by exact prefixLift 6487893
  have htrace : WordTrace (prefixWord ++ tailWord_6487893) baseStart_6487893 baseEnd_6487893 := by
    simpa [prefixWord, tailWord_6487893, baseEnd_6487893] using wordTrace_append hprefix tailTrace_6487893
  have hstable : (prefixWord ++ tailWord_6487893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487893).length < 2 ^ (prefixWord ++ tailWord_6487893).sum := by decide
  have hdescent : baseEnd_6487893 < baseStart_6487893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487930 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2]
def baseStart_6487930 : Nat := 118140960795 + 6487930 * 2 ^ 59
def prefixEnd_6487930 : Nat := 4983230072969 + 3 ^ 40 * 6487930 * 2
def baseEnd_6487930 : Nat := 3331426542724906177737559

theorem tailTrace_6487930 : CollatzResearch.WordTrace tailWord_6487930 prefixEnd_6487930 3331426542724906177737559 := by
  unfold tailWord_6487930
  simp only [CollatzResearch.WordTrace]
  refine ⟨59158561846336283768181311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157756164923563423381816829 59158561846336283768181311)
  ·
    refine ⟨88737842769504425652271967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59158561846336283768181311 88737842769504425652271967)
    ·
      refine ⟨133106764154256638478407951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88737842769504425652271967 133106764154256638478407951)
      ·
        refine ⟨199660146231384957717611927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133106764154256638478407951 199660146231384957717611927)
        ·
          refine ⟨299490219347077436576417891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199660146231384957717611927 299490219347077436576417891)
          ·
            refine ⟨449235329020616154864626837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299490219347077436576417891 449235329020616154864626837)
            ·
              refine ⟨21057906047841382259279383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 449235329020616154864626837 21057906047841382259279383)
              ·
                refine ⟨31586859071762073388919075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21057906047841382259279383 31586859071762073388919075)
                ·
                  refine ⟨47380288607643110083378613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31586859071762073388919075 47380288607643110083378613)
                  ·
                    refine ⟨4441902056966541570316745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47380288607643110083378613 4441902056966541570316745)
                    ·
                      refine ⟨3331426542724906177737559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441902056966541570316745 3331426542724906177737559)
                      ·
                        rfl

theorem cell23_6487930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_6487930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487930 prefixEnd_6487930 := by exact prefixLift 6487930
  have htrace : WordTrace (prefixWord ++ tailWord_6487930) baseStart_6487930 baseEnd_6487930 := by
    simpa [prefixWord, tailWord_6487930, baseEnd_6487930] using wordTrace_append hprefix tailTrace_6487930
  have hstable : (prefixWord ++ tailWord_6487930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487930).length < 2 ^ (prefixWord ++ tailWord_6487930).sum := by decide
  have hdescent : baseEnd_6487930 < baseStart_6487930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487940 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_6487940 : Nat := 118140960795 + 6487940 * 2 ^ 59
def prefixEnd_6487940 : Nat := 4983230072969 + 3 ^ 40 * 6487940 * 2
def baseEnd_6487940 : Nat := 1110477225843817046204171

theorem tailTrace_6487940 : CollatzResearch.WordTrace tailWord_6487940 prefixEnd_6487940 1110477225843817046204171 := by
  unfold tailWord_6487940
  simp only [CollatzResearch.WordTrace]
  refine ⟨118317306057654453390294637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157756408076872604520392849 118317306057654453390294637)
  ·
    refine ⟨44368989771620420021360489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118317306057654453390294637 44368989771620420021360489)
    ·
      refine ⟨33276742328715315016020367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44368989771620420021360489 33276742328715315016020367)
      ·
        refine ⟨49915113493072972524030551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33276742328715315016020367 49915113493072972524030551)
        ·
          refine ⟨74872670239609458786045827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49915113493072972524030551 74872670239609458786045827)
          ·
            refine ⟨112309005359414188179068741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74872670239609458786045827 112309005359414188179068741)
            ·
              refine ⟨21057938504890160283575389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112309005359414188179068741 21057938504890160283575389)
              ·
                refine ⟨7896726939333810106340771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21057938504890160283575389 7896726939333810106340771)
                ·
                  refine ⟨11845090409000715159511157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7896726939333810106340771 11845090409000715159511157)
                  ·
                    refine ⟨1110477225843817046204171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11845090409000715159511157 1110477225843817046204171)
                    ·
                      rfl

theorem cell23_6487940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_6487940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487940 prefixEnd_6487940 := by exact prefixLift 6487940
  have htrace : WordTrace (prefixWord ++ tailWord_6487940) baseStart_6487940 baseEnd_6487940 := by
    simpa [prefixWord, tailWord_6487940, baseEnd_6487940] using wordTrace_append hprefix tailTrace_6487940
  have hstable : (prefixWord ++ tailWord_6487940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487940).length < 2 ^ (prefixWord ++ tailWord_6487940).sum := by decide
  have hdescent : baseEnd_6487940 < baseStart_6487940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487954 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6487954 : Nat := 118140960795 + 6487954 * 2 ^ 59
def prefixEnd_6487954 : Nat := 4983230072969 + 3 ^ 40 * 6487954 * 2
def baseEnd_6487954 : Nat := 3331438866260614083837449

theorem tailTrace_6487954 : CollatzResearch.WordTrace tailWord_6487954 prefixEnd_6487954 3331438866260614083837449 := by
  unfold tailWord_6487954
  simp only [CollatzResearch.WordTrace]
  refine ⟨59158780684314546792899729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157756748491505458114399277 59158780684314546792899729)
  ·
    refine ⟨44369085513235910094674797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59158780684314546792899729 44369085513235910094674797)
    ·
      refine ⟨16638407067463466285503049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44369085513235910094674797 16638407067463466285503049)
      ·
        refine ⟨12478805300597599714127287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16638407067463466285503049 12478805300597599714127287)
        ·
          refine ⟨18718207950896399571190931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12478805300597599714127287 18718207950896399571190931)
          ·
            refine ⟨28077311926344599356786397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18718207950896399571190931 28077311926344599356786397)
            ·
              refine ⟨10528991972379224758794899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28077311926344599356786397 10528991972379224758794899)
              ·
                refine ⟨15793487958568837138192349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528991972379224758794899 15793487958568837138192349)
                ·
                  refine ⟨5922557984463313926822131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15793487958568837138192349 5922557984463313926822131)
                  ·
                    refine ⟨8883836976694970890233197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5922557984463313926822131 8883836976694970890233197)
                    ·
                      refine ⟨3331438866260614083837449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8883836976694970890233197 3331438866260614083837449)
                      ·
                        rfl

theorem cell23_6487954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6487954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487954 prefixEnd_6487954 := by exact prefixLift 6487954
  have htrace : WordTrace (prefixWord ++ tailWord_6487954) baseStart_6487954 baseEnd_6487954 := by
    simpa [prefixWord, tailWord_6487954, baseEnd_6487954] using wordTrace_append hprefix tailTrace_6487954
  have hstable : (prefixWord ++ tailWord_6487954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487954).length < 2 ^ (prefixWord ++ tailWord_6487954).sum := by decide
  have hdescent : baseEnd_6487954 < baseStart_6487954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487973 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_6487973 : Nat := 118140960795 + 6487973 * 2 ^ 59
def prefixEnd_6487973 : Nat := 4983230072969 + 3 ^ 40 * 6487973 * 2
def baseEnd_6487973 : Nat := 3331448622393049509499861

theorem tailTrace_6487973 : CollatzResearch.WordTrace tailWord_6487973 prefixEnd_6487973 3331448622393049509499861 := by
  unfold tailWord_6487973
  simp only [CollatzResearch.WordTrace]
  refine ⟨236635815724189353416540573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157757210482792902277693715 236635815724189353416540573)
  ·
    refine ⟨88738430896571007531202715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236635815724189353416540573 88738430896571007531202715)
    ·
      refine ⟨133107646344856511296804073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88738430896571007531202715 133107646344856511296804073)
      ·
        refine ⟨99830734758642383472603055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133107646344856511296804073 99830734758642383472603055)
        ·
          refine ⟨149746102137963575208904583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99830734758642383472603055 149746102137963575208904583)
          ·
            refine ⟨224619153206945362813356875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149746102137963575208904583 224619153206945362813356875)
            ·
              refine ⟨336928729810418044220035313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224619153206945362813356875 336928729810418044220035313)
              ·
                refine ⟨252696547357813533165026485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336928729810418044220035313 252696547357813533165026485)
                ·
                  refine ⟨23690301314795018734221233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252696547357813533165026485 23690301314795018734221233)
                  ·
                    refine ⟨17767725986096264050665925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23690301314795018734221233 17767725986096264050665925)
                    ·
                      refine ⟨3331448622393049509499861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17767725986096264050665925 3331448622393049509499861)
                      ·
                        rfl

theorem cell23_6487973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_6487973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487973 prefixEnd_6487973 := by exact prefixLift 6487973
  have htrace : WordTrace (prefixWord ++ tailWord_6487973) baseStart_6487973 baseEnd_6487973 := by
    simpa [prefixWord, tailWord_6487973, baseEnd_6487973] using wordTrace_append hprefix tailTrace_6487973
  have hstable : (prefixWord ++ tailWord_6487973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487973).length < 2 ^ (prefixWord ++ tailWord_6487973).sum := by decide
  have hdescent : baseEnd_6487973 < baseStart_6487973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6487997 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_6487997 : Nat := 118140960795 + 6487997 * 2 ^ 59
def prefixEnd_6487997 : Nat := 4983230072969 + 3 ^ 40 * 6487997 * 2
def baseEnd_6487997 : Nat := 3331460945928757415599751

theorem tailTrace_6487997 : CollatzResearch.WordTrace tailWord_6487997 prefixEnd_6487997 3331460945928757415599751 := by
  unfold tailWord_6487997
  simp only [CollatzResearch.WordTrace]
  refine ⟨236636691076102405515414245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157757794050734937010276163 236636691076102405515414245)
  ·
    refine ⟨44369379576769201034140171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236636691076102405515414245 44369379576769201034140171)
    ·
      refine ⟨66554069365153801551210257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44369379576769201034140171 66554069365153801551210257)
      ·
        refine ⟨49915552023865351163407693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66554069365153801551210257 49915552023865351163407693)
        ·
          refine ⟨18718332008949506686277885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49915552023865351163407693 18718332008949506686277885)
          ·
            refine ⟨7019374503356065007354207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18718332008949506686277885 7019374503356065007354207)
            ·
              refine ⟨10529061755034097511031311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019374503356065007354207 10529061755034097511031311)
              ·
                refine ⟨15793592632551146266546967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10529061755034097511031311 15793592632551146266546967)
                ·
                  refine ⟨23690388948826719399820451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15793592632551146266546967 23690388948826719399820451)
                  ·
                    refine ⟨35535583423240079099730677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23690388948826719399820451 35535583423240079099730677)
                    ·
                      refine ⟨3331460945928757415599751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35535583423240079099730677 3331460945928757415599751)
                      ·
                        rfl

theorem cell23_6487997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_6487997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6487997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6487997 prefixEnd_6487997 := by exact prefixLift 6487997
  have htrace : WordTrace (prefixWord ++ tailWord_6487997) baseStart_6487997 baseEnd_6487997 := by
    simpa [prefixWord, tailWord_6487997, baseEnd_6487997] using wordTrace_append hprefix tailTrace_6487997
  have hstable : (prefixWord ++ tailWord_6487997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6487997).length < 2 ^ (prefixWord ++ tailWord_6487997).sum := by decide
  have hdescent : baseEnd_6487997 < baseStart_6487997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6487997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488034 : List Nat := [3, 3, 3, 1, 2, 1, 3, 7]
def baseStart_6488034 : Nat := 118140960795 + 6488034 * 2 ^ 59
def prefixEnd_6488034 : Nat := 4983230072969 + 3 ^ 40 * 6488034 * 2
def baseEnd_6488034 : Nat := 123388146100480510031003

theorem tailTrace_6488034 : CollatzResearch.WordTrace tailWord_6488034 prefixEnd_6488034 123388146100480510031003 := by
  unfold tailWord_6488034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59159510144242090208627789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157758693717978907223007437 59159510144242090208627789)
  ·
    refine ⟨22184816304090783828235421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59159510144242090208627789 22184816304090783828235421)
    ·
      refine ⟨8319306114034043935588283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22184816304090783828235421 8319306114034043935588283)
      ·
        refine ⟨12478959171051065903382425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8319306114034043935588283 12478959171051065903382425)
        ·
          refine ⟨9359219378288299427536819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12478959171051065903382425 9359219378288299427536819)
          ·
            refine ⟨14038829067432449141305229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359219378288299427536819 14038829067432449141305229)
            ·
              refine ⟨5264560900287168427989461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14038829067432449141305229 5264560900287168427989461)
              ·
                refine ⟨123388146100480510031003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5264560900287168427989461 123388146100480510031003)
                ·
                  rfl

theorem cell23_6488034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 7].length) (baseStart_6488034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488034 prefixEnd_6488034 := by exact prefixLift 6488034
  have htrace : WordTrace (prefixWord ++ tailWord_6488034) baseStart_6488034 baseEnd_6488034 := by
    simpa [prefixWord, tailWord_6488034, baseEnd_6488034] using wordTrace_append hprefix tailTrace_6488034
  have hstable : (prefixWord ++ tailWord_6488034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488034).length < 2 ^ (prefixWord ++ tailWord_6488034).sum := by decide
  have hdescent : baseEnd_6488034 < baseStart_6488034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488045 : List Nat := [1, 5, 1, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6488045 : Nat := 118140960795 + 6488045 * 2 ^ 59
def prefixEnd_6488045 : Nat := 4983230072969 + 3 ^ 40 * 6488045 * 2
def baseEnd_6488045 : Nat := 3331485593000173227799531

theorem tailTrace_6488045 : CollatzResearch.WordTrace tailWord_6488045 prefixEnd_6488045 3331485593000173227799531 := by
  unfold tailWord_6488045
  simp only [CollatzResearch.WordTrace]
  refine ⟨236638441779928509713161589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157758961186619006475441059 236638441779928509713161589)
  ·
    refine ⟨22184853916868297785608899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236638441779928509713161589 22184853916868297785608899)
    ·
      refine ⟨33277280875302446678413349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22184853916868297785608899 33277280875302446678413349)
      ·
        refine ⟨6239490164119208752202503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33277280875302446678413349 6239490164119208752202503)
        ·
          refine ⟨9359235246178813128303755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6239490164119208752202503 9359235246178813128303755)
          ·
            refine ⟨14038852869268219692455633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359235246178813128303755 14038852869268219692455633)
            ·
              refine ⟨10529139651951164769341725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14038852869268219692455633 10529139651951164769341725)
              ·
                refine ⟨3948427369481686788503147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10529139651951164769341725 3948427369481686788503147)
                ·
                  refine ⟨5922641054222530182754721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948427369481686788503147 5922641054222530182754721)
                  ·
                    refine ⟨4441980790666897637066041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5922641054222530182754721 4441980790666897637066041)
                    ·
                      refine ⟨3331485593000173227799531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4441980790666897637066041 3331485593000173227799531)
                      ·
                        rfl

theorem cell23_6488045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6488045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488045 prefixEnd_6488045 := by exact prefixLift 6488045
  have htrace : WordTrace (prefixWord ++ tailWord_6488045) baseStart_6488045 baseEnd_6488045 := by
    simpa [prefixWord, tailWord_6488045, baseEnd_6488045] using wordTrace_append hprefix tailTrace_6488045
  have hstable : (prefixWord ++ tailWord_6488045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488045).length < 2 ^ (prefixWord ++ tailWord_6488045).sum := by decide
  have hdescent : baseEnd_6488045 < baseStart_6488045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488090 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 7]
def baseStart_6488090 : Nat := 118140960795 + 6488090 * 2 ^ 59
def prefixEnd_6488090 : Nat := 4983230072969 + 3 ^ 40 * 6488090 * 2
def baseEnd_6488090 : Nat := 370167633292180616859647

theorem tailTrace_6488090 : CollatzResearch.WordTrace tailWord_6488090 prefixEnd_6488090 370167633292180616859647 := by
  unfold tailWord_6488090
  simp only [CollatzResearch.WordTrace]
  refine ⟨59160020766191370599637431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157760055376510321599033149 59160020766191370599637431)
  ·
    refine ⟨88740031149287055899456147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59160020766191370599637431 88740031149287055899456147)
    ·
      refine ⟨133110046723930583849184221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88740031149287055899456147 133110046723930583849184221)
      ·
        refine ⟨49916267521473968943444083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133110046723930583849184221 49916267521473968943444083)
        ·
          refine ⟨74874401282210953415166125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49916267521473968943444083 74874401282210953415166125)
          ·
            refine ⟨28077900480829107530687297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74874401282210953415166125 28077900480829107530687297)
            ·
              refine ⟨21058425360621830648015473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28077900480829107530687297 21058425360621830648015473)
              ·
                refine ⟨15793819020466372986011605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21058425360621830648015473 15793819020466372986011605)
                ·
                  refine ⟨370167633292180616859647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15793819020466372986011605 370167633292180616859647)
                  ·
                    rfl

theorem cell23_6488090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_6488090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488090 prefixEnd_6488090 := by exact prefixLift 6488090
  have htrace : WordTrace (prefixWord ++ tailWord_6488090) baseStart_6488090 baseEnd_6488090 := by
    simpa [prefixWord, tailWord_6488090, baseEnd_6488090] using wordTrace_append hprefix tailTrace_6488090
  have hstable : (prefixWord ++ tailWord_6488090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488090).length < 2 ^ (prefixWord ++ tailWord_6488090).sum := by decide
  have hdescent : baseEnd_6488090 < baseStart_6488090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488104 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6488104 : Nat := 118140960795 + 6488104 * 2 ^ 59
def prefixEnd_6488104 : Nat := 4983230072969 + 3 ^ 40 * 6488104 * 2
def baseEnd_6488104 : Nat := 3331515888358788496961759

theorem tailTrace_6488104 : CollatzResearch.WordTrace tailWord_6488104 prefixEnd_6488104 3331515888358788496961759 := by
  unfold tailWord_6488104
  simp only [CollatzResearch.WordTrace]
  refine ⟨118320296843357381394779683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157760395791143175193039577 118320296843357381394779683)
  ·
    refine ⟨177480445265036072092169525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118320296843357381394779683 177480445265036072092169525)
    ·
      refine ⟨16638791743597131758640893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177480445265036072092169525 16638791743597131758640893)
      ·
        refine ⟨6239546903848924409490335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16638791743597131758640893 6239546903848924409490335)
        ·
          refine ⟨9359320355773386614235503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6239546903848924409490335 9359320355773386614235503)
          ·
            refine ⟨14038980533660079921353255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359320355773386614235503 14038980533660079921353255)
            ·
              refine ⟨21058470800490119882029883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14038980533660079921353255 21058470800490119882029883)
              ·
                refine ⟨31587706200735179823044825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21058470800490119882029883 31587706200735179823044825)
                ·
                  refine ⟨23690779650551384867283619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31587706200735179823044825 23690779650551384867283619)
                  ·
                    refine ⟨35536169475827077300925429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23690779650551384867283619 35536169475827077300925429)
                    ·
                      refine ⟨3331515888358788496961759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35536169475827077300925429 3331515888358788496961759)
                      ·
                        rfl

theorem cell23_6488104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6488104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488104 prefixEnd_6488104 := by exact prefixLift 6488104
  have htrace : WordTrace (prefixWord ++ tailWord_6488104) baseStart_6488104 baseEnd_6488104 := by
    simpa [prefixWord, tailWord_6488104, baseEnd_6488104] using wordTrace_append hprefix tailTrace_6488104
  have hstable : (prefixWord ++ tailWord_6488104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488104).length < 2 ^ (prefixWord ++ tailWord_6488104).sum := by decide
  have hdescent : baseEnd_6488104 < baseStart_6488104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488124 : List Nat := [2, 2, 2, 2, 2, 1, 5, 2, 5]
def baseStart_6488124 : Nat := 118140960795 + 6488124 * 2 ^ 59
def prefixEnd_6488124 : Nat := 4983230072969 + 3 ^ 40 * 6488124 * 2
def baseEnd_6488124 : Nat := 370169573107986490967963

theorem tailTrace_6488124 : CollatzResearch.WordTrace tailWord_6488124 prefixEnd_6488124 370169573107986490967963 := by
  unfold tailWord_6488124
  simp only [CollatzResearch.WordTrace]
  refine ⟨118320661573321153102643713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157760882097761537470191617 118320661573321153102643713)
  ·
    refine ⟨88740496179990864826982785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118320661573321153102643713 88740496179990864826982785)
    ·
      refine ⟨66555372134993148620237089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88740496179990864826982785 66555372134993148620237089)
      ·
        refine ⟨49916529101244861465177817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66555372134993148620237089 49916529101244861465177817)
        ·
          refine ⟨37437396825933646098883363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49916529101244861465177817 37437396825933646098883363)
          ·
            refine ⟨56156095238900469148325045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37437396825933646098883363 56156095238900469148325045)
            ·
              refine ⟨5264633928646918982655473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56156095238900469148325045 5264633928646918982655473)
              ·
                refine ⟨3948475446485189236991605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5264633928646918982655473 3948475446485189236991605)
                ·
                  refine ⟨370169573107986490967963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3948475446485189236991605 370169573107986490967963)
                  ·
                    rfl

theorem cell23_6488124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_6488124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488124 prefixEnd_6488124 := by exact prefixLift 6488124
  have htrace : WordTrace (prefixWord ++ tailWord_6488124) baseStart_6488124 baseEnd_6488124 := by
    simpa [prefixWord, tailWord_6488124, baseEnd_6488124] using wordTrace_append hprefix tailTrace_6488124
  have hstable : (prefixWord ++ tailWord_6488124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488124).length < 2 ^ (prefixWord ++ tailWord_6488124).sum := by decide
  have hdescent : baseEnd_6488124 < baseStart_6488124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488134 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6488134 : Nat := 118140960795 + 6488134 * 2 ^ 59
def prefixEnd_6488134 : Nat := 4983230072969 + 3 ^ 40 * 6488134 * 2
def baseEnd_6488134 : Nat := 3331531292778423379586621

theorem tailTrace_6488134 : CollatzResearch.WordTrace tailWord_6488134 prefixEnd_6488134 3331531292778423379586621 := by
  unfold tailWord_6488134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7395052746143939934785983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157761125251070718608767637 7395052746143939934785983)
  ·
    refine ⟨11092579119215909902178975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7395052746143939934785983 11092579119215909902178975)
    ·
      refine ⟨16638868678823864853268463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11092579119215909902178975 16638868678823864853268463)
      ·
        refine ⟨24958303018235797279902695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16638868678823864853268463 24958303018235797279902695)
        ·
          refine ⟨37437454527353695919854043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24958303018235797279902695 37437454527353695919854043)
          ·
            refine ⟨56156181791030543879781065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37437454527353695919854043 56156181791030543879781065)
            ·
              refine ⟨42117136343272907909835799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56156181791030543879781065 42117136343272907909835799)
              ·
                refine ⟨63175704514909361864753699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42117136343272907909835799 63175704514909361864753699)
                ·
                  refine ⟨94763556772364042797130549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63175704514909361864753699 94763556772364042797130549)
                  ·
                    refine ⟨8884083447409129012230989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94763556772364042797130549 8884083447409129012230989)
                    ·
                      refine ⟨3331531292778423379586621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8884083447409129012230989 3331531292778423379586621)
                      ·
                        rfl

theorem cell23_6488134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6488134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488134 prefixEnd_6488134 := by exact prefixLift 6488134
  have htrace : WordTrace (prefixWord ++ tailWord_6488134) baseStart_6488134 baseEnd_6488134 := by
    simpa [prefixWord, tailWord_6488134, baseEnd_6488134] using wordTrace_append hprefix tailTrace_6488134
  have hstable : (prefixWord ++ tailWord_6488134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488134).length < 2 ^ (prefixWord ++ tailWord_6488134).sum := by decide
  have hdescent : baseEnd_6488134 < baseStart_6488134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488140 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6488140 : Nat := 118140960795 + 6488140 * 2 ^ 59
def prefixEnd_6488140 : Nat := 4983230072969 + 3 ^ 40 * 6488140 * 2
def baseEnd_6488140 : Nat := 3331534373662350356111593

theorem tailTrace_6488140 : CollatzResearch.WordTrace tailWord_6488140 prefixEnd_6488140 3331534373662350356111593 := by
  unfold tailWord_6488140
  simp only [CollatzResearch.WordTrace]
  refine ⟨118320953357292170468934937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157761271143056227291913249 118320953357292170468934937)
  ·
    refine ⟨88740715017969127851701203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118320953357292170468934937 88740715017969127851701203)
    ·
      refine ⟨133111072526953691777551805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88740715017969127851701203 133111072526953691777551805)
      ·
        refine ⟨49916652197607634416581927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133111072526953691777551805 49916652197607634416581927)
        ·
          refine ⟨74874978296411451624872891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49916652197607634416581927 74874978296411451624872891)
          ·
            refine ⟨112312467444617177437309337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74874978296411451624872891 112312467444617177437309337)
            ·
              refine ⟨84234350583462883077982003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112312467444617177437309337 84234350583462883077982003)
              ·
                refine ⟨126351525875194324616973005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84234350583462883077982003 126351525875194324616973005)
                ·
                  refine ⟨47381822203197871731364877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126351525875194324616973005 47381822203197871731364877)
                  ·
                    refine ⟨17768183326199201899261829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47381822203197871731364877 17768183326199201899261829)
                    ·
                      refine ⟨3331534373662350356111593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17768183326199201899261829 3331534373662350356111593)
                      ·
                        rfl

theorem cell23_6488140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6488140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488140 prefixEnd_6488140 := by exact prefixLift 6488140
  have htrace : WordTrace (prefixWord ++ tailWord_6488140) baseStart_6488140 baseEnd_6488140 := by
    simpa [prefixWord, tailWord_6488140, baseEnd_6488140] using wordTrace_append hprefix tailTrace_6488140
  have hstable : (prefixWord ++ tailWord_6488140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488140).length < 2 ^ (prefixWord ++ tailWord_6488140).sum := by decide
  have hdescent : baseEnd_6488140 < baseStart_6488140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488174 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_6488174 : Nat := 118140960795 + 6488174 * 2 ^ 59
def prefixEnd_6488174 : Nat := 4983230072969 + 3 ^ 40 * 6488174 * 2
def baseEnd_6488174 : Nat := 3331551832004603223086437

theorem tailTrace_6488174 : CollatzResearch.WordTrace tailWord_6488174 prefixEnd_6488174 3331551832004603223086437 := by
  unfold tailWord_6488174
  simp only [CollatzResearch.WordTrace]
  refine ⟨29580393349557645593075947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157762097864307443163071717 29580393349557645593075947)
  ·
    refine ⟨44370590024336468389613921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29580393349557645593075947 44370590024336468389613921)
    ·
      refine ⟨33277942518252351292210441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44370590024336468389613921 33277942518252351292210441)
      ·
        refine ⟨24958456888689263469157831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33277942518252351292210441 24958456888689263469157831)
        ·
          refine ⟨37437685333033895203736747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24958456888689263469157831 37437685333033895203736747)
          ·
            refine ⟨56156527999550842805605121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37437685333033895203736747 56156527999550842805605121)
            ·
              refine ⟨42117395999663132104203841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56156527999550842805605121 42117395999663132104203841)
              ·
                refine ⟨31588046999747349078152881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42117395999663132104203841 31588046999747349078152881)
                ·
                  refine ⟨23691035249810511808614661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31588046999747349078152881 23691035249810511808614661)
                  ·
                    refine ⟨4442069109339470964115249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23691035249810511808614661 4442069109339470964115249)
                    ·
                      refine ⟨3331551832004603223086437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442069109339470964115249 3331551832004603223086437)
                      ·
                        rfl

theorem cell23_6488174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_6488174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488174 prefixEnd_6488174 := by exact prefixLift 6488174
  have htrace : WordTrace (prefixWord ++ tailWord_6488174) baseStart_6488174 baseEnd_6488174 := by
    simpa [prefixWord, tailWord_6488174, baseEnd_6488174] using wordTrace_append hprefix tailTrace_6488174
  have hstable : (prefixWord ++ tailWord_6488174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488174).length < 2 ^ (prefixWord ++ tailWord_6488174).sum := by decide
  have hdescent : baseEnd_6488174 < baseStart_6488174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488177 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_6488177 : Nat := 118140960795 + 6488177 * 2 ^ 59
def prefixEnd_6488177 : Nat := 4983230072969 + 3 ^ 40 * 6488177 * 2
def baseEnd_6488177 : Nat := 3331553372446566711348923

theorem tailTrace_6488177 : CollatzResearch.WordTrace tailWord_6488177 prefixEnd_6488177 3331553372446566711348923 := by
  unfold tailWord_6488177
  simp only [CollatzResearch.WordTrace]
  refine ⟨236643256215450296256966785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157762170810300197504644523 236643256215450296256966785)
  ·
    refine ⟨177482442161587722192725089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236643256215450296256966785 177482442161587722192725089)
    ·
      refine ⟨133111831621190791644543817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177482442161587722192725089 133111831621190791644543817)
      ·
        refine ⟨99833873715893093733407863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133111831621190791644543817 99833873715893093733407863)
        ·
          refine ⟨149750810573839640600111795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99833873715893093733407863 149750810573839640600111795)
          ·
            refine ⟨224626215860759460900167693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149750810573839640600111795 224626215860759460900167693)
            ·
              refine ⟨84234830947784797837562885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224626215860759460900167693 84234830947784797837562885)
              ·
                refine ⟨15794030802709649594543041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84234830947784797837562885 15794030802709649594543041)
                ·
                  refine ⟨11845523102032237195907281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15794030802709649594543041 11845523102032237195907281)
                  ·
                    refine ⟨8884142326524177896930461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11845523102032237195907281 8884142326524177896930461)
                    ·
                      refine ⟨3331553372446566711348923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8884142326524177896930461 3331553372446566711348923)
                      ·
                        rfl

theorem cell23_6488177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_6488177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488177 prefixEnd_6488177 := by exact prefixLift 6488177
  have htrace : WordTrace (prefixWord ++ tailWord_6488177) baseStart_6488177 baseEnd_6488177 := by
    simpa [prefixWord, tailWord_6488177, baseEnd_6488177] using wordTrace_append hprefix tailTrace_6488177
  have hstable : (prefixWord ++ tailWord_6488177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488177).length < 2 ^ (prefixWord ++ tailWord_6488177).sum := by decide
  have hdescent : baseEnd_6488177 < baseStart_6488177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488197 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 6]
def baseStart_6488197 : Nat := 118140960795 + 6488197 * 2 ^ 59
def prefixEnd_6488197 : Nat := 4983230072969 + 3 ^ 40 * 6488197 * 2
def baseEnd_6488197 : Nat := 370173738006628514788759

theorem tailTrace_6488197 : CollatzResearch.WordTrace tailWord_6488197 prefixEnd_6488197 370173738006628514788759 := by
  unfold tailWord_6488197
  simp only [CollatzResearch.WordTrace]
  refine ⟨236643985675377839672694845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157762657116918559781796563 236643985675377839672694845)
  ·
    refine ⟨88741494628266689877260567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236643985675377839672694845 88741494628266689877260567)
    ·
      refine ⟨133112241942400034815890851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88741494628266689877260567 133112241942400034815890851)
      ·
        refine ⟨199668362913600052223836277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133112241942400034815890851 199668362913600052223836277)
        ·
          refine ⟨18718909023150004895984651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199668362913600052223836277 18718909023150004895984651)
          ·
            refine ⟨28078363534725007343976977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18718909023150004895984651 28078363534725007343976977)
            ·
              refine ⟨21058772651043755507982733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28078363534725007343976977 21058772651043755507982733)
              ·
                refine ⟨7897039744141408315493525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21058772651043755507982733 7897039744141408315493525)
                ·
                  refine ⟨370173738006628514788759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7897039744141408315493525 370173738006628514788759)
                  ·
                    rfl

theorem cell23_6488197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_6488197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488197 prefixEnd_6488197 := by exact prefixLift 6488197
  have htrace : WordTrace (prefixWord ++ tailWord_6488197) baseStart_6488197 baseEnd_6488197 := by
    simpa [prefixWord, tailWord_6488197, baseEnd_6488197] using wordTrace_append hprefix tailTrace_6488197
  have hstable : (prefixWord ++ tailWord_6488197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488197).length < 2 ^ (prefixWord ++ tailWord_6488197).sum := by decide
  have hdescent : baseEnd_6488197 < baseStart_6488197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488218 : List Nat := [3, 1, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_6488218 : Nat := 118140960795 + 6488218 * 2 ^ 59
def prefixEnd_6488218 : Nat := 4983230072969 + 3 ^ 40 * 6488218 * 2
def baseEnd_6488218 : Nat := 1110524808384467016978745

theorem tailTrace_6488218 : CollatzResearch.WordTrace tailWord_6488218 prefixEnd_6488218 1110524808384467016978745 := by
  unfold tailWord_6488218
  simp only [CollatzResearch.WordTrace]
  refine ⟨59161187902075440064802327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157763167738867840172806205 59161187902075440064802327)
  ·
    refine ⟨88741781853113160097203491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59161187902075440064802327 88741781853113160097203491)
    ·
      refine ⟨133112672779669740145805237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88741781853113160097203491 133112672779669740145805237)
      ·
        refine ⟨12479313073094038138669241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133112672779669740145805237 12479313073094038138669241)
        ·
          refine ⟨9359484804820528604001931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12479313073094038138669241 9359484804820528604001931)
          ·
            refine ⟨14039227207230792906002897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359484804820528604001931 14039227207230792906002897)
            ·
              refine ⟨10529420405423094679502173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14039227207230792906002897 10529420405423094679502173)
              ·
                refine ⟨3948532652033660504813315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10529420405423094679502173 3948532652033660504813315)
                ·
                  refine ⟨5922798978050490757219973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948532652033660504813315 5922798978050490757219973)
                  ·
                    refine ⟨1110524808384467016978745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5922798978050490757219973 1110524808384467016978745)
                    ·
                      rfl

theorem cell23_6488218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_6488218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488218 prefixEnd_6488218 := by exact prefixLift 6488218
  have htrace : WordTrace (prefixWord ++ tailWord_6488218) baseStart_6488218 baseEnd_6488218 := by
    simpa [prefixWord, tailWord_6488218, baseEnd_6488218] using wordTrace_append hprefix tailTrace_6488218
  have hstable : (prefixWord ++ tailWord_6488218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488218).length < 2 ^ (prefixWord ++ tailWord_6488218).sum := by decide
  have hdescent : baseEnd_6488218 < baseStart_6488218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488231 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 6]
def baseStart_6488231 : Nat := 118140960795 + 6488231 * 2 ^ 59
def prefixEnd_6488231 : Nat := 4983230072969 + 3 ^ 40 * 6488231 * 2
def baseEnd_6488231 : Nat := 370175677822434388897075

theorem tailTrace_6488231 : CollatzResearch.WordTrace tailWord_6488231 prefixEnd_6488231 370175677822434388897075 := by
  unfold tailWord_6488231
  simp only [CollatzResearch.WordTrace]
  refine ⟨236645225757254663479432547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157763483838169775652955031 236645225757254663479432547)
  ·
    refine ⟨354967838635881995219148821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236645225757254663479432547 354967838635881995219148821)
    ·
      refine ⟨16639117436056968525897601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 354967838635881995219148821 16639117436056968525897601)
      ·
        refine ⟨12479338077042726394423201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16639117436056968525897601 12479338077042726394423201)
        ·
          refine ⟨9359503557782044795817401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12479338077042726394423201 9359503557782044795817401)
          ·
            refine ⟨7019627668336533596863051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9359503557782044795817401 7019627668336533596863051)
            ·
              refine ⟨10529441502504800395294577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019627668336533596863051 10529441502504800395294577)
              ·
                refine ⟨7897081126878600296470933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10529441502504800395294577 7897081126878600296470933)
                ·
                  refine ⟨370175677822434388897075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7897081126878600296470933 370175677822434388897075)
                  ·
                    rfl

theorem cell23_6488231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 6].length) (baseStart_6488231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488231 prefixEnd_6488231 := by exact prefixLift 6488231
  have htrace : WordTrace (prefixWord ++ tailWord_6488231) baseStart_6488231 baseEnd_6488231 := by
    simpa [prefixWord, tailWord_6488231, baseEnd_6488231] using wordTrace_append hprefix tailTrace_6488231
  have hstable : (prefixWord ++ tailWord_6488231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488231).length < 2 ^ (prefixWord ++ tailWord_6488231).sum := by decide
  have hdescent : baseEnd_6488231 < baseStart_6488231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488274 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_6488274 : Nat := 118140960795 + 6488274 * 2 ^ 59
def prefixEnd_6488274 : Nat := 4983230072969 + 3 ^ 40 * 6488274 * 2
def baseEnd_6488274 : Nat := 1110534393356684277278659

theorem tailTrace_6488274 : CollatzResearch.WordTrace tailWord_6488274 prefixEnd_6488274 1110534393356684277278659 := by
  unfold tailWord_6488274
  simp only [CollatzResearch.WordTrace]
  refine ⟨59161698524024720455811969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157764529397399254548831917 59161698524024720455811969)
  ·
    refine ⟨44371273893018540341858977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59161698524024720455811969 44371273893018540341858977)
    ·
      refine ⟨33278455419763905256394233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44371273893018540341858977 33278455419763905256394233)
      ·
        refine ⟨24958841564822928942295675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33278455419763905256394233 24958841564822928942295675)
        ·
          refine ⟨37438262347234393413443513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24958841564822928942295675 37438262347234393413443513)
          ·
            refine ⟨28078696760425795060082635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37438262347234393413443513 28078696760425795060082635)
            ·
              refine ⟨42118045140638692590123953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28078696760425795060082635 42118045140638692590123953)
              ·
                refine ⟨31588533855479019442592965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42118045140638692590123953 31588533855479019442592965)
                ·
                  refine ⟨5922850097902316145486181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31588533855479019442592965 5922850097902316145486181)
                  ·
                    refine ⟨1110534393356684277278659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5922850097902316145486181 1110534393356684277278659)
                    ·
                      rfl

theorem cell23_6488274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_6488274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488274 prefixEnd_6488274 := by exact prefixLift 6488274
  have htrace : WordTrace (prefixWord ++ tailWord_6488274) baseStart_6488274 baseEnd_6488274 := by
    simpa [prefixWord, tailWord_6488274, baseEnd_6488274] using wordTrace_append hprefix tailTrace_6488274
  have hstable : (prefixWord ++ tailWord_6488274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488274).length < 2 ^ (prefixWord ++ tailWord_6488274).sum := by decide
  have hdescent : baseEnd_6488274 < baseStart_6488274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488297 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 3]
def baseStart_6488297 : Nat := 118140960795 + 6488297 * 2 ^ 59
def prefixEnd_6488297 : Nat := 4983230072969 + 3 ^ 40 * 6488297 * 2
def baseEnd_6488297 : Nat := 3331614990125106241848371

theorem tailTrace_6488297 : CollatzResearch.WordTrace tailWord_6488297 prefixEnd_6488297 3331614990125106241848371 := by
  unfold tailWord_6488297
  simp only [CollatzResearch.WordTrace]
  refine ⟨236647632975015556751335145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157765088650010371167556763 236647632975015556751335145)
  ·
    refine ⟨177485724731261667563501359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236647632975015556751335145 177485724731261667563501359)
    ·
      refine ⟨266228587096892501345252039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177485724731261667563501359 266228587096892501345252039)
      ·
        refine ⟨399342880645338752017878059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266228587096892501345252039 399342880645338752017878059)
        ·
          refine ⟨599014320968008128026817089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399342880645338752017878059 599014320968008128026817089)
          ·
            refine ⟨449260740726006096020112817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599014320968008128026817089 449260740726006096020112817)
            ·
              refine ⟨336945555544504572015084613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449260740726006096020112817 336945555544504572015084613)
              ·
                refine ⟨63177291664594607252828365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336945555544504572015084613 63177291664594607252828365)
                ·
                  refine ⟨23691484374222977719810637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63177291664594607252828365 23691484374222977719810637)
                  ·
                    refine ⟨8884306640333616644928989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23691484374222977719810637 8884306640333616644928989)
                    ·
                      refine ⟨3331614990125106241848371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8884306640333616644928989 3331614990125106241848371)
                      ·
                        rfl

theorem cell23_6488297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_6488297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488297 prefixEnd_6488297 := by exact prefixLift 6488297
  have htrace : WordTrace (prefixWord ++ tailWord_6488297) baseStart_6488297 baseEnd_6488297 := by
    simpa [prefixWord, tailWord_6488297, baseEnd_6488297] using wordTrace_append hprefix tailTrace_6488297
  have hstable : (prefixWord ++ tailWord_6488297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488297).length < 2 ^ (prefixWord ++ tailWord_6488297).sum := by decide
  have hdescent : baseEnd_6488297 < baseStart_6488297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488341 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_6488341 : Nat := 118140960795 + 6488341 * 2 ^ 59
def prefixEnd_6488341 : Nat := 4983230072969 + 3 ^ 40 * 6488341 * 2
def baseEnd_6488341 : Nat := 3331637583273904069698169

theorem tailTrace_6488341 : CollatzResearch.WordTrace tailWord_6488341 prefixEnd_6488341 3331637583273904069698169 := by
  unfold tailWord_6488341
  simp only [CollatzResearch.WordTrace]
  refine ⟨236649237786856152265936877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157766158524570768177291251 236649237786856152265936877)
  ·
    refine ⟨88743464170071057099726329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236649237786856152265936877 88743464170071057099726329)
    ·
      refine ⟨66557598127553292824794747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88743464170071057099726329 66557598127553292824794747)
      ·
        refine ⟨99836397191329939237192121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66557598127553292824794747 99836397191329939237192121)
        ·
          refine ⟨74877297893497454427894091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99836397191329939237192121 74877297893497454427894091)
          ·
            refine ⟨112315946840246181641841137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74877297893497454427894091 112315946840246181641841137)
            ·
              refine ⟨84236960130184636231380853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112315946840246181641841137 84236960130184636231380853)
              ·
                refine ⟨7897215012204809646691955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84236960130184636231380853 7897215012204809646691955)
                ·
                  refine ⟨11845822518307214470037933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7897215012204809646691955 11845822518307214470037933)
                  ·
                    refine ⟨4442183444365205426264225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11845822518307214470037933 4442183444365205426264225)
                    ·
                      refine ⟨3331637583273904069698169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442183444365205426264225 3331637583273904069698169)
                      ·
                        rfl

theorem cell23_6488341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_6488341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488341 prefixEnd_6488341 := by exact prefixLift 6488341
  have htrace : WordTrace (prefixWord ++ tailWord_6488341) baseStart_6488341 baseEnd_6488341 := by
    simpa [prefixWord, tailWord_6488341, baseEnd_6488341] using wordTrace_append hprefix tailTrace_6488341
  have hstable : (prefixWord ++ tailWord_6488341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488341).length < 2 ^ (prefixWord ++ tailWord_6488341).sum := by decide
  have hdescent : baseEnd_6488341 < baseStart_6488341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488349 : List Nat := [1, 4, 2, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_6488349 : Nat := 118140960795 + 6488349 * 2 ^ 59
def prefixEnd_6488349 : Nat := 4983230072969 + 3 ^ 40 * 6488349 * 2
def baseEnd_6488349 : Nat := 3331641691119140038398133

theorem tailTrace_6488349 : CollatzResearch.WordTrace tailWord_6488349 prefixEnd_6488349 3331641691119140038398133 := by
  unfold tailWord_6488349
  simp only [CollatzResearch.WordTrace]
  refine ⟨236649529570827169632228101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157766353047218113088152067 236649529570827169632228101)
  ·
    refine ⟨44371786794530094306042769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236649529570827169632228101 44371786794530094306042769)
    ·
      refine ⟨33278840095897570729532077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44371786794530094306042769 33278840095897570729532077)
      ·
        refine ⟨12479565035961589023574529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33278840095897570729532077 12479565035961589023574529)
        ·
          refine ⟨9359673776971191767680897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12479565035961589023574529 9359673776971191767680897)
          ·
            refine ⟨7019755332728393825760673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9359673776971191767680897 7019755332728393825760673)
            ·
              refine ⟨5264816499546295369320505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7019755332728393825760673 5264816499546295369320505)
              ·
                refine ⟨3948612374659721526990379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5264816499546295369320505 3948612374659721526990379)
                ·
                  refine ⟨5922918561989582290485569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948612374659721526990379 5922918561989582290485569)
                  ·
                    refine ⟨4442188921492186717864177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5922918561989582290485569 4442188921492186717864177)
                    ·
                      refine ⟨3331641691119140038398133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442188921492186717864177 3331641691119140038398133)
                      ·
                        rfl

theorem cell23_6488349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_6488349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488349 prefixEnd_6488349 := by exact prefixLift 6488349
  have htrace : WordTrace (prefixWord ++ tailWord_6488349) baseStart_6488349 baseEnd_6488349 := by
    simpa [prefixWord, tailWord_6488349, baseEnd_6488349] using wordTrace_append hprefix tailTrace_6488349
  have hstable : (prefixWord ++ tailWord_6488349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488349).length < 2 ^ (prefixWord ++ tailWord_6488349).sum := by decide
  have hdescent : baseEnd_6488349 < baseStart_6488349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488354 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_6488354 : Nat := 118140960795 + 6488354 * 2 ^ 59
def prefixEnd_6488354 : Nat := 4983230072969 + 3 ^ 40 * 6488354 * 2
def baseEnd_6488354 : Nat := 3331644258522412518835609

theorem tailTrace_6488354 : CollatzResearch.WordTrace tailWord_6488354 prefixEnd_6488354 3331644258522412518835609 := by
  unfold tailWord_6488354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59162427983952263871540029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157766474623872703657440077 59162427983952263871540029)
  ·
    refine ⟨22185910493982098951827511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59162427983952263871540029 22185910493982098951827511)
    ·
      refine ⟨33278865740973148427741267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22185910493982098951827511 33278865740973148427741267)
      ·
        refine ⟨49918298611459722641611901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33278865740973148427741267 49918298611459722641611901)
        ·
          refine ⟨18719361979297395990604463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49918298611459722641611901 18719361979297395990604463)
          ·
            refine ⟨28079042968946093985906695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18719361979297395990604463 28079042968946093985906695)
            ·
              refine ⟨42118564453419140978860043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28079042968946093985906695 42118564453419140978860043)
              ·
                refine ⟨63177846680128711468290065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42118564453419140978860043 63177846680128711468290065)
                ·
                  refine ⟨47383385010096533601217549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63177846680128711468290065 47383385010096533601217549)
                  ·
                    refine ⟨17768769378786200100456581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47383385010096533601217549 17768769378786200100456581)
                    ·
                      refine ⟨3331644258522412518835609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17768769378786200100456581 3331644258522412518835609)
                      ·
                        rfl

theorem cell23_6488354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_6488354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488354 prefixEnd_6488354 := by exact prefixLift 6488354
  have htrace : WordTrace (prefixWord ++ tailWord_6488354) baseStart_6488354 baseEnd_6488354 := by
    simpa [prefixWord, tailWord_6488354, baseEnd_6488354] using wordTrace_append hprefix tailTrace_6488354
  have hstable : (prefixWord ++ tailWord_6488354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488354).length < 2 ^ (prefixWord ++ tailWord_6488354).sum := by decide
  have hdescent : baseEnd_6488354 < baseStart_6488354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488367 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_6488367 : Nat := 118140960795 + 6488367 * 2 ^ 59
def prefixEnd_6488367 : Nat := 4983230072969 + 3 ^ 40 * 6488367 * 2
def baseEnd_6488367 : Nat := 3331650933770920967973049

theorem tailTrace_6488367 : CollatzResearch.WordTrace tailWord_6488367 prefixEnd_6488367 3331650933770920967973049 := by
  unfold tailWord_6488367
  simp only [CollatzResearch.WordTrace]
  refine ⟨236650186084761958706383355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157766790723174639137588903 236650186084761958706383355)
  ·
    refine ⟨354975279127142938059575033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236650186084761958706383355 354975279127142938059575033)
    ·
      refine ⟨266231459345357203544681275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354975279127142938059575033 266231459345357203544681275)
      ·
        refine ⟨399347189018035805317021913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266231459345357203544681275 399347189018035805317021913)
        ·
          refine ⟨299510391763526853987766435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399347189018035805317021913 299510391763526853987766435)
          ·
            refine ⟨449265587645290280981649653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299510391763526853987766435 449265587645290280981649653)
            ·
              refine ⟨42118648841745963842029655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449265587645290280981649653 42118648841745963842029655)
              ·
                refine ⟨63177973262618945763044483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42118648841745963842029655 63177973262618945763044483)
                ·
                  refine ⟨94766959893928418644566725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63177973262618945763044483 94766959893928418644566725)
                  ·
                    refine ⟨17768804980111578495856261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94766959893928418644566725 17768804980111578495856261)
                    ·
                      refine ⟨3331650933770920967973049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17768804980111578495856261 3331650933770920967973049)
                      ·
                        rfl

theorem cell23_6488367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_6488367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488367 prefixEnd_6488367 := by exact prefixLift 6488367
  have htrace : WordTrace (prefixWord ++ tailWord_6488367) baseStart_6488367 baseEnd_6488367 := by
    simpa [prefixWord, tailWord_6488367, baseEnd_6488367] using wordTrace_append hprefix tailTrace_6488367
  have hstable : (prefixWord ++ tailWord_6488367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488367).length < 2 ^ (prefixWord ++ tailWord_6488367).sum := by decide
  have hdescent : baseEnd_6488367 < baseStart_6488367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488371 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 1, 4, 2]
def baseStart_6488371 : Nat := 118140960795 + 6488371 * 2 ^ 59
def prefixEnd_6488371 : Nat := 4983230072969 + 3 ^ 40 * 6488371 * 2
def baseEnd_6488371 : Nat := 3331652987693538952323031

theorem tailTrace_6488371 : CollatzResearch.WordTrace tailWord_6488371 prefixEnd_6488371 3331652987693538952323031 := by
  unfold tailWord_6488371
  simp only [CollatzResearch.WordTrace]
  refine ⟨236650331976747467389528967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157766887984498311593019311 236650331976747467389528967)
  ·
    refine ⟨354975497965121201084293451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236650331976747467389528967 354975497965121201084293451)
    ·
      refine ⟨532463246947681801626440177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354975497965121201084293451 532463246947681801626440177)
      ·
        refine ⟨399347435210761351219830133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532463246947681801626440177 399347435210761351219830133)
        ·
          refine ⟨37438822051008876676859075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 399347435210761351219830133 37438822051008876676859075)
          ·
            refine ⟨56158233076513315015288613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37438822051008876676859075 56158233076513315015288613)
            ·
              refine ⟨10529668701846246565366615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56158233076513315015288613 10529668701846246565366615)
              ·
                refine ⟨15794503052769369848049923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10529668701846246565366615 15794503052769369848049923)
                ·
                  refine ⟨23691754579154054772074885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15794503052769369848049923 23691754579154054772074885)
                  ·
                    refine ⟨4442203983591385269764041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23691754579154054772074885 4442203983591385269764041)
                    ·
                      refine ⟨3331652987693538952323031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442203983591385269764041 3331652987693538952323031)
                      ·
                        rfl

theorem cell23_6488371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4, 2].length) (baseStart_6488371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488371 prefixEnd_6488371 := by exact prefixLift 6488371
  have htrace : WordTrace (prefixWord ++ tailWord_6488371) baseStart_6488371 baseEnd_6488371 := by
    simpa [prefixWord, tailWord_6488371, baseEnd_6488371] using wordTrace_append hprefix tailTrace_6488371
  have hstable : (prefixWord ++ tailWord_6488371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488371).length < 2 ^ (prefixWord ++ tailWord_6488371).sum := by decide
  have hdescent : baseEnd_6488371 < baseStart_6488371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488424 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 1, 7]
def baseStart_6488424 : Nat := 118140960795 + 6488424 * 2 ^ 59
def prefixEnd_6488424 : Nat := 4983230072969 + 3 ^ 40 * 6488424 * 2
def baseEnd_6488424 : Nat := 1110560067389409081653429

theorem tailTrace_6488424 : CollatzResearch.WordTrace tailWord_6488424 prefixEnd_6488424 1110560067389409081653429 := by
  unfold tailWord_6488424
  simp only [CollatzResearch.WordTrace]
  refine ⟨118326132522777728720604163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157768176697036971627472217 118326132522777728720604163)
  ·
    refine ⟨177489198784166593080906245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118326132522777728720604163 177489198784166593080906245)
    ·
      refine ⟨33279224772031236202669921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177489198784166593080906245 33279224772031236202669921)
      ·
        refine ⟨24959418579023427152002441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33279224772031236202669921 24959418579023427152002441)
        ·
          refine ⟨18719563934267570364001831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24959418579023427152002441 18719563934267570364001831)
          ·
            refine ⟨28079345901401355546002747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18719563934267570364001831 28079345901401355546002747)
            ·
              refine ⟨42119018852102033319004121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28079345901401355546002747 42119018852102033319004121)
              ·
                refine ⟨31589264139076524989253091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42119018852102033319004121 31589264139076524989253091)
                ·
                  refine ⟨47383896208614787483879637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31589264139076524989253091 47383896208614787483879637)
                  ·
                    refine ⟨1110560067389409081653429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47383896208614787483879637 1110560067389409081653429)
                    ·
                      rfl

theorem cell23_6488424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_6488424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488424 prefixEnd_6488424 := by exact prefixLift 6488424
  have htrace : WordTrace (prefixWord ++ tailWord_6488424) baseStart_6488424 baseEnd_6488424 := by
    simpa [prefixWord, tailWord_6488424, baseEnd_6488424] using wordTrace_append hprefix tailTrace_6488424
  have hstable : (prefixWord ++ tailWord_6488424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488424).length < 2 ^ (prefixWord ++ tailWord_6488424).sum := by decide
  have hdescent : baseEnd_6488424 < baseStart_6488424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488458 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_6488458 : Nat := 118140960795 + 6488458 * 2 ^ 59
def prefixEnd_6488458 : Nat := 4983230072969 + 3 ^ 40 * 6488458 * 2
def baseEnd_6488458 : Nat := 1110565886836826703978377

theorem tailTrace_6488458 : CollatzResearch.WordTrace tailWord_6488458 prefixEnd_6488458 1110565886836826703978377 := by
  unfold tailWord_6488458
  simp only [CollatzResearch.WordTrace]
  refine ⟨59163376281858070311986507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157769003418288187498630685 59163376281858070311986507)
  ·
    refine ⟨88745064422787105467979761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59163376281858070311986507 88745064422787105467979761)
    ·
      refine ⟨66558798317090329100984821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88745064422787105467979761 66558798317090329100984821)
      ·
        refine ⟨6239887342227218353217327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66558798317090329100984821 6239887342227218353217327)
        ·
          refine ⟨9359831013340827529825991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6239887342227218353217327 9359831013340827529825991)
          ·
            refine ⟨14039746520011241294738987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359831013340827529825991 14039746520011241294738987)
            ·
              refine ⟨21059619780016861942108481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14039746520011241294738987 21059619780016861942108481)
              ·
                refine ⟨15794714835012646456581361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21059619780016861942108481 15794714835012646456581361)
                ·
                  refine ⟨11846036126259484842436021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15794714835012646456581361 11846036126259484842436021)
                  ·
                    refine ⟨1110565886836826703978377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11846036126259484842436021 1110565886836826703978377)
                    ·
                      rfl

theorem cell23_6488458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_6488458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488458 prefixEnd_6488458 := by exact prefixLift 6488458
  have htrace : WordTrace (prefixWord ++ tailWord_6488458) baseStart_6488458 baseEnd_6488458 := by
    simpa [prefixWord, tailWord_6488458, baseEnd_6488458] using wordTrace_append hprefix tailTrace_6488458
  have hstable : (prefixWord ++ tailWord_6488458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488458).length < 2 ^ (prefixWord ++ tailWord_6488458).sum := by decide
  have hdescent : baseEnd_6488458 < baseStart_6488458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488471 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 3, 4]
def baseStart_6488471 : Nat := 118140960795 + 6488471 * 2 ^ 59
def prefixEnd_6488471 : Nat := 4983230072969 + 3 ^ 40 * 6488471 * 2
def baseEnd_6488471 : Nat := 1110568111919662853690857

theorem tailTrace_6488471 : CollatzResearch.WordTrace tailWord_6488471 prefixEnd_6488471 1110568111919662853690857 := by
  unfold tailWord_6488471
  simp only [CollatzResearch.WordTrace]
  refine ⟨236653979276385184468169267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157769319517590122978779511 236653979276385184468169267)
  ·
    refine ⟨354980968914577776702253901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236653979276385184468169267 354980968914577776702253901)
    ·
      refine ⟨133117863342966666263345213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354980968914577776702253901 133117863342966666263345213)
      ·
        refine ⟨49919198753612499848754455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133117863342966666263345213 49919198753612499848754455)
        ·
          refine ⟨74878798130418749773131683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49919198753612499848754455 74878798130418749773131683)
          ·
            refine ⟨112318197195628124659697525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74878798130418749773131683 112318197195628124659697525)
            ·
              refine ⟨10529830987090136686846643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112318197195628124659697525 10529830987090136686846643)
              ·
                refine ⟨15794746480635205030269965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10529830987090136686846643 15794746480635205030269965)
                ·
                  refine ⟨5923029930238201886351237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15794746480635205030269965 5923029930238201886351237)
                  ·
                    refine ⟨1110568111919662853690857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923029930238201886351237 1110568111919662853690857)
                    ·
                      rfl

theorem cell23_6488471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_6488471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488471 prefixEnd_6488471 := by exact prefixLift 6488471
  have htrace : WordTrace (prefixWord ++ tailWord_6488471) baseStart_6488471 baseEnd_6488471 := by
    simpa [prefixWord, tailWord_6488471, baseEnd_6488471] using wordTrace_append hprefix tailTrace_6488471
  have hstable : (prefixWord ++ tailWord_6488471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488471).length < 2 ^ (prefixWord ++ tailWord_6488471).sum := by decide
  have hdescent : baseEnd_6488471 < baseStart_6488471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488551 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6488551 : Nat := 118140960795 + 6488551 * 2 ^ 59
def prefixEnd_6488551 : Nat := 4983230072969 + 3 ^ 40 * 6488551 * 2
def baseEnd_6488551 : Nat := 3331745414211348248072203

theorem tailTrace_6488551 : CollatzResearch.WordTrace tailWord_6488551 prefixEnd_6488551 3331745414211348248072203 := by
  unfold tailWord_6488551
  simp only [CollatzResearch.WordTrace]
  refine ⟨236656897116095358131081507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157771264744063572087387671 236656897116095358131081507)
  ·
    refine ⟨354985345674143037196622261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236656897116095358131081507 354985345674143037196622261)
    ·
      refine ⟨33279876156950909737183337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 354985345674143037196622261 33279876156950909737183337)
      ·
        refine ⟨24959907117713182302887503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33279876156950909737183337 24959907117713182302887503)
        ·
          refine ⟨37439860676569773454331255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24959907117713182302887503 37439860676569773454331255)
          ·
            refine ⟨56159791014854660181496883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37439860676569773454331255 56159791014854660181496883)
            ·
              refine ⟨84239686522281990272245325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56159791014854660181496883 84239686522281990272245325)
              ·
                refine ⟨31589882445855746352091997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84239686522281990272245325 31589882445855746352091997)
                ·
                  refine ⟨11846205917195904882034499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31589882445855746352091997 11846205917195904882034499)
                  ·
                    refine ⟨17769308875793857323051749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11846205917195904882034499 17769308875793857323051749)
                    ·
                      refine ⟨3331745414211348248072203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17769308875793857323051749 3331745414211348248072203)
                      ·
                        rfl

theorem cell23_6488551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6488551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488551 prefixEnd_6488551 := by exact prefixLift 6488551
  have htrace : WordTrace (prefixWord ++ tailWord_6488551) baseStart_6488551 baseEnd_6488551 := by
    simpa [prefixWord, tailWord_6488551, baseEnd_6488551] using wordTrace_append hprefix tailTrace_6488551
  have hstable : (prefixWord ++ tailWord_6488551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488551).length < 2 ^ (prefixWord ++ tailWord_6488551).sum := by decide
  have hdescent : baseEnd_6488551 < baseStart_6488551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488561 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 4, 4]
def baseStart_6488561 : Nat := 118140960795 + 6488561 * 2 ^ 59
def prefixEnd_6488561 : Nat := 4983230072969 + 3 ^ 40 * 6488561 * 2
def baseEnd_6488561 : Nat := 1110583516339297736315719

theorem tailTrace_6488561 : CollatzResearch.WordTrace tailWord_6488561 prefixEnd_6488561 1110583516339297736315719 := by
  unfold tailWord_6488561
  simp only [CollatzResearch.WordTrace]
  refine ⟨236657261846059129838945537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157771507897372753225963691 236657261846059129838945537)
  ·
    refine ⟨177492946384544347379209153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236657261846059129838945537 177492946384544347379209153)
    ·
      refine ⟨133119709788408260534406865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177492946384544347379209153 133119709788408260534406865)
      ·
        refine ⟨99839782341306195400805149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133119709788408260534406865 99839782341306195400805149)
        ·
          refine ⟨37439918377989823275301931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99839782341306195400805149 37439918377989823275301931)
          ·
            refine ⟨56159877566984734912952897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37439918377989823275301931 56159877566984734912952897)
            ·
              refine ⟨42119908175238551184714673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56159877566984734912952897 42119908175238551184714673)
              ·
                refine ⟨31589931131428913388536005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42119908175238551184714673 31589931131428913388536005)
                ·
                  refine ⟨5923112087142921260350501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31589931131428913388536005 5923112087142921260350501)
                  ·
                    refine ⟨1110583516339297736315719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923112087142921260350501 1110583516339297736315719)
                    ·
                      rfl

theorem cell23_6488561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_6488561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488561 prefixEnd_6488561 := by exact prefixLift 6488561
  have htrace : WordTrace (prefixWord ++ tailWord_6488561) baseStart_6488561 baseEnd_6488561 := by
    simpa [prefixWord, tailWord_6488561, baseEnd_6488561] using wordTrace_append hprefix tailTrace_6488561
  have hstable : (prefixWord ++ tailWord_6488561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488561).length < 2 ^ (prefixWord ++ tailWord_6488561).sum := by decide
  have hdescent : baseEnd_6488561 < baseStart_6488561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488565 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6488565 : Nat := 118140960795 + 6488565 * 2 ^ 59
def prefixEnd_6488565 : Nat := 4983230072969 + 3 ^ 40 * 6488565 * 2
def baseEnd_6488565 : Nat := 1110584200980170397765713

theorem tailTrace_6488565 : CollatzResearch.WordTrace tailWord_6488565 prefixEnd_6488565 1110584200980170397765713 := by
  unfold tailWord_6488565
  simp only [CollatzResearch.WordTrace]
  refine ⟨236657407738044638522091149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157771605158696425681394099 236657407738044638522091149)
  ·
    refine ⟨88746527901766739445784181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236657407738044638522091149 88746527901766739445784181)
    ·
      refine ⟨8319986990790631823042267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88746527901766739445784181 8319986990790631823042267)
      ·
        refine ⟨12479980486185947734563401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8319986990790631823042267 12479980486185947734563401)
        ·
          refine ⟨9359985364639460800922551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12479980486185947734563401 9359985364639460800922551)
          ·
            refine ⟨14039978046959191201383827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359985364639460800922551 14039978046959191201383827)
            ·
              refine ⟨21059967070438786802075741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14039978046959191201383827 21059967070438786802075741)
              ·
                refine ⟨7897487651414545050778403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21059967070438786802075741 7897487651414545050778403)
                ·
                  refine ⟨11846231477121817576167605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7897487651414545050778403 11846231477121817576167605)
                  ·
                    refine ⟨1110584200980170397765713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11846231477121817576167605 1110584200980170397765713)
                    ·
                      rfl

theorem cell23_6488565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6488565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488565 prefixEnd_6488565 := by exact prefixLift 6488565
  have htrace : WordTrace (prefixWord ++ tailWord_6488565) baseStart_6488565 baseEnd_6488565 := by
    simpa [prefixWord, tailWord_6488565, baseEnd_6488565] using wordTrace_append hprefix tailTrace_6488565
  have hstable : (prefixWord ++ tailWord_6488565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488565).length < 2 ^ (prefixWord ++ tailWord_6488565).sum := by decide
  have hdescent : baseEnd_6488565 < baseStart_6488565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488568 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 5, 2, 2]
def baseStart_6488568 : Nat := 118140960795 + 6488568 * 2 ^ 59
def prefixEnd_6488568 : Nat := 4983230072969 + 3 ^ 40 * 6488568 * 2
def baseEnd_6488568 : Nat := 3331754143382474681559625

theorem tailTrace_6488568 : CollatzResearch.WordTrace tailWord_6488568 prefixEnd_6488568 3331754143382474681559625 := by
  unfold tailWord_6488568
  simp only [CollatzResearch.WordTrace]
  refine ⟨118328758578516885017225179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157771678104689180022966905 118328758578516885017225179)
  ·
    refine ⟨177493137867775327525837769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118328758578516885017225179 177493137867775327525837769)
    ·
      refine ⟨133119853400831495644378327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177493137867775327525837769 133119853400831495644378327)
      ·
        refine ⟨199679780101247243466567491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133119853400831495644378327 199679780101247243466567491)
        ·
          refine ⟨299519670151870865199851237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199679780101247243466567491 299519670151870865199851237)
          ·
            refine ⟨56159938153475787224972107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299519670151870865199851237 56159938153475787224972107)
            ·
              refine ⟨84239907230213680837458161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56159938153475787224972107 84239907230213680837458161)
              ·
                refine ⟨63179930422660260628093621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84239907230213680837458161 63179930422660260628093621)
                ·
                  refine ⟨5923118477124399433883777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63179930422660260628093621 5923118477124399433883777)
                  ·
                    refine ⟨4442338857843299575412833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5923118477124399433883777 4442338857843299575412833)
                    ·
                      refine ⟨3331754143382474681559625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442338857843299575412833 3331754143382474681559625)
                      ·
                        rfl

theorem cell23_6488568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_6488568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488568 prefixEnd_6488568 := by exact prefixLift 6488568
  have htrace : WordTrace (prefixWord ++ tailWord_6488568) baseStart_6488568 baseEnd_6488568 := by
    simpa [prefixWord, tailWord_6488568, baseEnd_6488568] using wordTrace_append hprefix tailTrace_6488568
  have hstable : (prefixWord ++ tailWord_6488568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488568).length < 2 ^ (prefixWord ++ tailWord_6488568).sum := by decide
  have hdescent : baseEnd_6488568 < baseStart_6488568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488584 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_6488584 : Nat := 118140960795 + 6488584 * 2 ^ 59
def prefixEnd_6488584 : Nat := 4983230072969 + 3 ^ 40 * 6488584 * 2
def baseEnd_6488584 : Nat := 3331762359072946618959551

theorem tailTrace_6488584 : CollatzResearch.WordTrace tailWord_6488584 prefixEnd_6488584 3331762359072946618959551 := by
  unfold tailWord_6488584
  simp only [CollatzResearch.WordTrace]
  refine ⟨118329050362487902383516403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157772067149983869844688537 118329050362487902383516403)
  ·
    refine ⟨177493575543731853575274605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118329050362487902383516403 177493575543731853575274605)
    ·
      refine ⟨66560090828899445090727977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177493575543731853575274605 66560090828899445090727977)
      ·
        refine ⟨49920068121674583818045983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66560090828899445090727977 49920068121674583818045983)
        ·
          refine ⟨74880102182511875727068975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49920068121674583818045983 74880102182511875727068975)
          ·
            refine ⟨112320153273767813590603463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74880102182511875727068975 112320153273767813590603463)
            ·
              refine ⟨168480229910651720385905195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112320153273767813590603463 168480229910651720385905195)
              ·
                refine ⟨252720344865977580578857793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168480229910651720385905195 252720344865977580578857793)
                ·
                  refine ⟨189540258649483185434143345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252720344865977580578857793 189540258649483185434143345)
                  ·
                    refine ⟨142155193987112389075607509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189540258649483185434143345 142155193987112389075607509)
                    ·
                      refine ⟨3331762359072946618959551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142155193987112389075607509 3331762359072946618959551)
                      ·
                        rfl

theorem cell23_6488584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_6488584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488584 prefixEnd_6488584 := by exact prefixLift 6488584
  have htrace : WordTrace (prefixWord ++ tailWord_6488584) baseStart_6488584 baseEnd_6488584 := by
    simpa [prefixWord, tailWord_6488584, baseEnd_6488584] using wordTrace_append hprefix tailTrace_6488584
  have hstable : (prefixWord ++ tailWord_6488584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488584).length < 2 ^ (prefixWord ++ tailWord_6488584).sum := by decide
  have hdescent : baseEnd_6488584 < baseStart_6488584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488605 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_6488605 : Nat := 118140960795 + 6488605 * 2 ^ 59
def prefixEnd_6488605 : Nat := 4983230072969 + 3 ^ 40 * 6488605 * 2
def baseEnd_6488605 : Nat := 3331773142166691036796955

theorem tailTrace_6488605 : CollatzResearch.WordTrace tailWord_6488605 prefixEnd_6488605 3331773142166691036796955 := by
  unfold tailWord_6488605
  simp only [CollatzResearch.WordTrace]
  refine ⟨236658866657899725353547269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157772577771933150235698179 236658866657899725353547269)
  ·
    refine ⟨44373537498356198503790113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236658866657899725353547269 44373537498356198503790113)
    ·
      refine ⟨33280153123767148877842585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44373537498356198503790113 33280153123767148877842585)
      ·
        refine ⟨24960114842825361658381939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33280153123767148877842585 24960114842825361658381939)
        ·
          refine ⟨37440172264238042487572909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24960114842825361658381939 37440172264238042487572909)
          ·
            refine ⟨14040064599089265932839841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37440172264238042487572909 14040064599089265932839841)
            ·
              refine ⟨10530048449316949449629881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14040064599089265932839841 10530048449316949449629881)
              ·
                refine ⟨7897536336987712087222411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10530048449316949449629881 7897536336987712087222411)
                ·
                  refine ⟨11846304505481568130833617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7897536336987712087222411 11846304505481568130833617)
                  ·
                    refine ⟨8884728379111176098125213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11846304505481568130833617 8884728379111176098125213)
                    ·
                      refine ⟨3331773142166691036796955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8884728379111176098125213 3331773142166691036796955)
                      ·
                        rfl

theorem cell23_6488605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_6488605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488605 prefixEnd_6488605 := by exact prefixLift 6488605
  have htrace : WordTrace (prefixWord ++ tailWord_6488605) baseStart_6488605 baseEnd_6488605 := by
    simpa [prefixWord, tailWord_6488605, baseEnd_6488605] using wordTrace_append hprefix tailTrace_6488605
  have hstable : (prefixWord ++ tailWord_6488605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488605).length < 2 ^ (prefixWord ++ tailWord_6488605).sum := by decide
  have hdescent : baseEnd_6488605 < baseStart_6488605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488661 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6488661 : Nat := 118140960795 + 6488661 * 2 ^ 59
def prefixEnd_6488661 : Nat := 4983230072969 + 3 ^ 40 * 6488661 * 2
def baseEnd_6488661 : Nat := 3331801897083342817696697

theorem tailTrace_6488661 : CollatzResearch.WordTrace tailWord_6488661 prefixEnd_6488661 3331801897083342817696697 := by
  unfold tailWord_6488661
  simp only [CollatzResearch.WordTrace]
  refine ⟨236660909145696846917585837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157773939430464564611723891 236660909145696846917585837)
  ·
    refine ⟨88747840929636317594094689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236660909145696846917585837 88747840929636317594094689)
    ·
      refine ⟨66560880697227238195571017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88747840929636317594094689 66560880697227238195571017)
      ·
        refine ⟨49920660522920428646678263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66560880697227238195571017 49920660522920428646678263)
        ·
          refine ⟨74880990784380642970017395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49920660522920428646678263 74880990784380642970017395)
          ·
            refine ⟨112321486176570964455026093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74880990784380642970017395 112321486176570964455026093)
            ·
              refine ⟨42120557316214111670634785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112321486176570964455026093 42120557316214111670634785)
              ·
                refine ⟨31590417987160583752976089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42120557316214111670634785 31590417987160583752976089)
                ·
                  refine ⟨23692813490370437814732067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31590417987160583752976089 23692813490370437814732067)
                  ·
                    refine ⟨35539220235555656722098101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23692813490370437814732067 35539220235555656722098101)
                    ·
                      refine ⟨3331801897083342817696697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35539220235555656722098101 3331801897083342817696697)
                      ·
                        rfl

theorem cell23_6488661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6488661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488661 prefixEnd_6488661 := by exact prefixLift 6488661
  have htrace : WordTrace (prefixWord ++ tailWord_6488661) baseStart_6488661 baseEnd_6488661 := by
    simpa [prefixWord, tailWord_6488661, baseEnd_6488661] using wordTrace_append hprefix tailTrace_6488661
  have hstable : (prefixWord ++ tailWord_6488661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488661).length < 2 ^ (prefixWord ++ tailWord_6488661).sum := by decide
  have hdescent : baseEnd_6488661 < baseStart_6488661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488708 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_6488708 : Nat := 118140960795 + 6488708 * 2 ^ 59
def prefixEnd_6488708 : Nat := 4983230072969 + 3 ^ 40 * 6488708 * 2
def baseEnd_6488708 : Nat := 3331826030674104133808981

theorem tailTrace_6488708 : CollatzResearch.WordTrace tailWord_6488708 prefixEnd_6488708 3331826030674104133808981 := by
  unfold tailWord_6488708
  simp only [CollatzResearch.WordTrace]
  refine ⟨118331311688263286972273389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157775082251017715963031185 118331311688263286972273389)
  ·
    refine ⟨44374241883098732614602521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118331311688263286972273389 44374241883098732614602521)
    ·
      refine ⟨33280681412324049460951891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44374241883098732614602521 33280681412324049460951891)
      ·
        refine ⟨49921022118486074191427837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33280681412324049460951891 49921022118486074191427837)
        ·
          refine ⟨18720383294432277821785439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49921022118486074191427837 18720383294432277821785439)
          ·
            refine ⟨28080574941648416732678159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18720383294432277821785439 28080574941648416732678159)
            ·
              refine ⟨42120862412472625099017239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28080574941648416732678159 42120862412472625099017239)
              ·
                refine ⟨63181293618708937648525859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42120862412472625099017239 63181293618708937648525859)
                ·
                  refine ⟨94771940428063406472788789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63181293618708937648525859 94771940428063406472788789)
                  ·
                    refine ⟨8884869415130944356823949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94771940428063406472788789 8884869415130944356823949)
                    ·
                      refine ⟨3331826030674104133808981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8884869415130944356823949 3331826030674104133808981)
                      ·
                        rfl

theorem cell23_6488708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_6488708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488708 prefixEnd_6488708 := by exact prefixLift 6488708
  have htrace : WordTrace (prefixWord ++ tailWord_6488708) baseStart_6488708 baseEnd_6488708 := by
    simpa [prefixWord, tailWord_6488708, baseEnd_6488708] using wordTrace_append hprefix tailTrace_6488708
  have hstable : (prefixWord ++ tailWord_6488708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488708).length < 2 ^ (prefixWord ++ tailWord_6488708).sum := by decide
  have hdescent : baseEnd_6488708 < baseStart_6488708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488711 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 1, 7]
def baseStart_6488711 : Nat := 118140960795 + 6488711 * 2 ^ 59
def prefixEnd_6488711 : Nat := 4983230072969 + 3 ^ 40 * 6488711 * 2
def baseEnd_6488711 : Nat := 1110609190372022540690489

theorem tailTrace_6488711 : CollatzResearch.WordTrace tailWord_6488711 prefixEnd_6488711 1110609190372022540690489 := by
  unfold tailWord_6488711
  simp only [CollatzResearch.WordTrace]
  refine ⟨236662732795515705456905987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157775155197010470304603991 236662732795515705456905987)
  ·
    refine ⟨354994099193273558185358981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236662732795515705456905987 354994099193273558185358981)
    ·
      refine ⟨66561393598738792159754809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354994099193273558185358981 66561393598738792159754809)
      ·
        refine ⟨49921045199054094119816107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66561393598738792159754809 49921045199054094119816107)
        ·
          refine ⟨74881567798581141179724161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49921045199054094119816107 74881567798581141179724161)
          ·
            refine ⟨56161175848935855884793121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74881567798581141179724161 56161175848935855884793121)
            ·
              refine ⟨42120881886701891913594841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56161175848935855884793121 42120881886701891913594841)
              ·
                refine ⟨31590661415026418935196131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42120881886701891913594841 31590661415026418935196131)
                ·
                  refine ⟨47385992122539628402794197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31590661415026418935196131 47385992122539628402794197)
                  ·
                    refine ⟨1110609190372022540690489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47385992122539628402794197 1110609190372022540690489)
                    ·
                      rfl

theorem cell23_6488711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_6488711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488711 prefixEnd_6488711 := by exact prefixLift 6488711
  have htrace : WordTrace (prefixWord ++ tailWord_6488711) baseStart_6488711 baseEnd_6488711 := by
    simpa [prefixWord, tailWord_6488711, baseEnd_6488711] using wordTrace_append hprefix tailTrace_6488711
  have hstable : (prefixWord ++ tailWord_6488711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488711).length < 2 ^ (prefixWord ++ tailWord_6488711).sum := by decide
  have hdescent : baseEnd_6488711 < baseStart_6488711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488743 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6488743 : Nat := 118140960795 + 6488743 * 2 ^ 59
def prefixEnd_6488743 : Nat := 4983230072969 + 3 ^ 40 * 6488743 * 2
def baseEnd_6488743 : Nat := 3331844002497011496871321

theorem tailTrace_6488743 : CollatzResearch.WordTrace tailWord_6488743 prefixEnd_6488743 3331844002497011496871321 := by
  unfold tailWord_6488743
  simp only [CollatzResearch.WordTrace]
  refine ⟨236663899931399774922070883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157775933287599849948047255 236663899931399774922070883)
  ·
    refine ⟨354995849897099662383106325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236663899931399774922070883 354995849897099662383106325)
    ·
      refine ⟨16640430463926546674208109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 354995849897099662383106325 16640430463926546674208109)
      ·
        refine ⟨6240161423972455002828041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16640430463926546674208109 6240161423972455002828041)
        ·
          refine ⟨4680121067979341252121031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6240161423972455002828041 4680121067979341252121031)
          ·
            refine ⟨7020181601969011878181547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680121067979341252121031 7020181601969011878181547)
            ·
              refine ⟨10530272402953517817272321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7020181601969011878181547 10530272402953517817272321)
              ·
                refine ⟨7897704302215138362954241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10530272402953517817272321 7897704302215138362954241)
                ·
                  refine ⟨5923278226661353772215681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7897704302215138362954241 5923278226661353772215681)
                  ·
                    refine ⟨4442458669996015329161761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5923278226661353772215681 4442458669996015329161761)
                    ·
                      refine ⟨3331844002497011496871321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442458669996015329161761 3331844002497011496871321)
                      ·
                        rfl

theorem cell23_6488743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6488743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488743 prefixEnd_6488743 := by exact prefixLift 6488743
  have htrace : WordTrace (prefixWord ++ tailWord_6488743) baseStart_6488743 baseEnd_6488743 := by
    simpa [prefixWord, tailWord_6488743, baseEnd_6488743] using wordTrace_append hprefix tailTrace_6488743
  have hstable : (prefixWord ++ tailWord_6488743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488743).length < 2 ^ (prefixWord ++ tailWord_6488743).sum := by decide
  have hdescent : baseEnd_6488743 < baseStart_6488743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488761 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6488761 : Nat := 118140960795 + 6488761 * 2 ^ 59
def prefixEnd_6488761 : Nat := 4983230072969 + 3 ^ 40 * 6488761 * 2
def baseEnd_6488761 : Nat := 3331853245148792426446237

theorem tailTrace_6488761 : CollatzResearch.WordTrace tailWord_6488761 prefixEnd_6488761 3331853245148792426446237 := by
  unfold tailWord_6488761
  simp only [CollatzResearch.WordTrace]
  refine ⟨236664556445334563996226137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157776370963556375997484091 236664556445334563996226137)
  ·
    refine ⟨177498417334000922997169603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236664556445334563996226137 177498417334000922997169603)
    ·
      refine ⟨266247626001001384495754405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177498417334000922997169603 266247626001001384495754405)
      ·
        refine ⟨49921429875187759592953951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266247626001001384495754405 49921429875187759592953951)
        ·
          refine ⟨74882144812781639389430927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49921429875187759592953951 74882144812781639389430927)
          ·
            refine ⟨112323217219172459084146391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74882144812781639389430927 112323217219172459084146391)
            ·
              refine ⟨168484825828758688626219587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112323217219172459084146391 168484825828758688626219587)
              ·
                refine ⟨252727238743138032939329381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168484825828758688626219587 252727238743138032939329381)
                ·
                  refine ⟨47386357264338381176124259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252727238743138032939329381 47386357264338381176124259)
                  ·
                    refine ⟨71079535896507571764186389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47386357264338381176124259 71079535896507571764186389)
                    ·
                      refine ⟨3331853245148792426446237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71079535896507571764186389 3331853245148792426446237)
                      ·
                        rfl

theorem cell23_6488761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6488761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488761 prefixEnd_6488761 := by exact prefixLift 6488761
  have htrace : WordTrace (prefixWord ++ tailWord_6488761) baseStart_6488761 baseEnd_6488761 := by
    simpa [prefixWord, tailWord_6488761, baseEnd_6488761] using wordTrace_append hprefix tailTrace_6488761
  have hstable : (prefixWord ++ tailWord_6488761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488761).length < 2 ^ (prefixWord ++ tailWord_6488761).sum := by decide
  have hdescent : baseEnd_6488761 < baseStart_6488761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488765 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_6488765 : Nat := 118140960795 + 6488765 * 2 ^ 59
def prefixEnd_6488765 : Nat := 4983230072969 + 3 ^ 40 * 6488765 * 2
def baseEnd_6488765 : Nat := 3331855299071410410796219

theorem tailTrace_6488765 : CollatzResearch.WordTrace tailWord_6488765 prefixEnd_6488765 3331855299071410410796219 := by
  unfold tailWord_6488765
  simp only [CollatzResearch.WordTrace]
  refine ⟨236664702337320072679371749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157776468224880048452914499 236664702337320072679371749)
  ·
    refine ⟨44374631688247513627382203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236664702337320072679371749 44374631688247513627382203)
    ·
      refine ⟨66561947532371270441073305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44374631688247513627382203 66561947532371270441073305)
      ·
        refine ⟨49921460649278452830804979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66561947532371270441073305 49921460649278452830804979)
        ·
          refine ⟨74882190973917679246207469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49921460649278452830804979 74882190973917679246207469)
          ·
            refine ⟨28080821615219129717327801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74882190973917679246207469 28080821615219129717327801)
            ·
              refine ⟨21060616211414347287995851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28080821615219129717327801 21060616211414347287995851)
              ·
                refine ⟨31590924317121520931993777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21060616211414347287995851 31590924317121520931993777)
                ·
                  refine ⟨23693193237841140698995333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31590924317121520931993777 23693193237841140698995333)
                  ·
                    refine ⟨4442473732095213881061625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23693193237841140698995333 4442473732095213881061625)
                    ·
                      refine ⟨3331855299071410410796219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442473732095213881061625 3331855299071410410796219)
                      ·
                        rfl

theorem cell23_6488765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_6488765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488765 prefixEnd_6488765 := by exact prefixLift 6488765
  have htrace : WordTrace (prefixWord ++ tailWord_6488765) baseStart_6488765 baseEnd_6488765 := by
    simpa [prefixWord, tailWord_6488765, baseEnd_6488765] using wordTrace_append hprefix tailTrace_6488765
  have hstable : (prefixWord ++ tailWord_6488765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488765).length < 2 ^ (prefixWord ++ tailWord_6488765).sum := by decide
  have hdescent : baseEnd_6488765 < baseStart_6488765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488768 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3]
def baseStart_6488768 : Nat := 118140960795 + 6488768 * 2 ^ 59
def prefixEnd_6488768 : Nat := 4983230072969 + 3 ^ 40 * 6488768 * 2
def baseEnd_6488768 : Nat := 3331856839513373899058705

theorem tailTrace_6488768 : CollatzResearch.WordTrace tailWord_6488768 prefixEnd_6488768 3331856839513373899058705 := by
  unfold tailWord_6488768
  simp only [CollatzResearch.WordTrace]
  refine ⟨118332405878154602095865479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157776541170872802794487305 118332405878154602095865479)
  ·
    refine ⟨177498608817231903143798219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118332405878154602095865479 177498608817231903143798219)
    ·
      refine ⟨266247913225847854715697329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177498608817231903143798219 266247913225847854715697329)
      ·
        refine ⟨199685934919385891036772997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266247913225847854715697329 199685934919385891036772997)
        ·
          refine ⟨37441112797384854569394937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199685934919385891036772997 37441112797384854569394937)
          ·
            refine ⟨28080834598038640927046203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37441112797384854569394937 28080834598038640927046203)
            ·
              refine ⟨42121251897057961390569305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28080834598038640927046203 42121251897057961390569305)
              ·
                refine ⟨31590938922793471042926979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42121251897057961390569305 31590938922793471042926979)
                ·
                  refine ⟨47386408384190206564390469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31590938922793471042926979 47386408384190206564390469)
                  ·
                    refine ⟨8884951572035663730823213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47386408384190206564390469 8884951572035663730823213)
                    ·
                      refine ⟨3331856839513373899058705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8884951572035663730823213 3331856839513373899058705)
                      ·
                        rfl

theorem cell23_6488768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_6488768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488768 prefixEnd_6488768 := by exact prefixLift 6488768
  have htrace : WordTrace (prefixWord ++ tailWord_6488768) baseStart_6488768 baseEnd_6488768 := by
    simpa [prefixWord, tailWord_6488768, baseEnd_6488768] using wordTrace_append hprefix tailTrace_6488768
  have hstable : (prefixWord ++ tailWord_6488768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488768).length < 2 ^ (prefixWord ++ tailWord_6488768).sum := by decide
  have hdescent : baseEnd_6488768 < baseStart_6488768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488792 : List Nat := [2, 1, 2, 2, 3, 2, 3, 3, 1, 4]
def baseStart_6488792 : Nat := 118140960795 + 6488792 * 2 ^ 59
def prefixEnd_6488792 : Nat := 4983230072969 + 3 ^ 40 * 6488792 * 2
def baseEnd_6488792 : Nat := 1110623054349693935052865

theorem tailTrace_6488792 : CollatzResearch.WordTrace tailWord_6488792 prefixEnd_6488792 1110623054349693935052865 := by
  unfold tailWord_6488792
  simp only [CollatzResearch.WordTrace]
  refine ⟨118332843554111128145302315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157777124738814837527069753 118332843554111128145302315)
  ·
    refine ⟨177499265331166692217953473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118332843554111128145302315 177499265331166692217953473)
    ·
      refine ⟨133124448998375019163465105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177499265331166692217953473 133124448998375019163465105)
      ·
        refine ⟨99843336748781264372598829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133124448998375019163465105 99843336748781264372598829)
        ·
          refine ⟨37441251280792974139724561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99843336748781264372598829 37441251280792974139724561)
          ·
            refine ⟨28080938460594730604793421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37441251280792974139724561 28080938460594730604793421)
            ·
              refine ⟨10530351922723023976797533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28080938460594730604793421 10530351922723023976797533)
              ·
                refine ⟨3948881971021133991299075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10530351922723023976797533 3948881971021133991299075)
                ·
                  refine ⟨5923322956531700986948613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948881971021133991299075 5923322956531700986948613)
                  ·
                    refine ⟨1110623054349693935052865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923322956531700986948613 1110623054349693935052865)
                    ·
                      rfl

theorem cell23_6488792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_6488792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488792 prefixEnd_6488792 := by exact prefixLift 6488792
  have htrace : WordTrace (prefixWord ++ tailWord_6488792) baseStart_6488792 baseEnd_6488792 := by
    simpa [prefixWord, tailWord_6488792, baseEnd_6488792] using wordTrace_append hprefix tailTrace_6488792
  have hstable : (prefixWord ++ tailWord_6488792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488792).length < 2 ^ (prefixWord ++ tailWord_6488792).sum := by decide
  have hdescent : baseEnd_6488792 < baseStart_6488792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488811 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7]
def baseStart_6488811 : Nat := 118140960795 + 6488811 * 2 ^ 59
def prefixEnd_6488811 : Nat := 4983230072969 + 3 ^ 40 * 6488811 * 2
def baseEnd_6488811 : Nat := 3331878919181517230821007

theorem tailTrace_6488811 : CollatzResearch.WordTrace tailWord_6488811 prefixEnd_6488811 3331878919181517230821007 := by
  unfold tailWord_6488811
  simp only [CollatzResearch.WordTrace]
  refine ⟨236666380095153422535546287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157777586730102281690364191 236666380095153422535546287)
  ·
    refine ⟨354999570142730133803319431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236666380095153422535546287 354999570142730133803319431)
    ·
      refine ⟨532499355214095200704979147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354999570142730133803319431 532499355214095200704979147)
      ·
        refine ⟨798749032821142801057468721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532499355214095200704979147 798749032821142801057468721)
        ·
          refine ⟨599061774615857100793101541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798749032821142801057468721 599061774615857100793101541)
          ·
            refine ⟨112324082740473206398706539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 599061774615857100793101541 112324082740473206398706539)
            ·
              refine ⟨168486124110709809598059809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112324082740473206398706539 168486124110709809598059809)
              ·
                refine ⟨126364593083032357198544857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168486124110709809598059809 126364593083032357198544857)
                ·
                  refine ⟨94773444812274267898908643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126364593083032357198544857 94773444812274267898908643)
                  ·
                    refine ⟨142160167218411401848362965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94773444812274267898908643 142160167218411401848362965)
                    ·
                      refine ⟨3331878919181517230821007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142160167218411401848362965 3331878919181517230821007)
                      ·
                        rfl

theorem cell23_6488811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_6488811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488811 prefixEnd_6488811 := by exact prefixLift 6488811
  have htrace : WordTrace (prefixWord ++ tailWord_6488811) baseStart_6488811 baseEnd_6488811 := by
    simpa [prefixWord, tailWord_6488811, baseEnd_6488811] using wordTrace_append hprefix tailTrace_6488811
  have hstable : (prefixWord ++ tailWord_6488811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488811).length < 2 ^ (prefixWord ++ tailWord_6488811).sum := by decide
  have hdescent : baseEnd_6488811 < baseStart_6488811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488842 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_6488842 : Nat := 118140960795 + 6488842 * 2 ^ 59
def prefixEnd_6488842 : Nat := 4983230072969 + 3 ^ 40 * 6488842 * 2
def baseEnd_6488842 : Nat := 3331894837081806609533365

theorem tailTrace_6488842 : CollatzResearch.WordTrace tailWord_6488842 prefixEnd_6488842 3331894837081806609533365 := by
  unfold tailWord_6488842
  simp only [CollatzResearch.WordTrace]
  refine ⟨59166877689510278707481195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157778340505360743219949853 59166877689510278707481195)
  ·
    refine ⟨88750316534265418061221793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59166877689510278707481195 88750316534265418061221793)
    ·
      refine ⟨66562737400699063545916345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88750316534265418061221793 66562737400699063545916345)
      ·
        refine ⟨49922053050524297659437259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66562737400699063545916345 49922053050524297659437259)
        ·
          refine ⟨74883079575786446489155889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49922053050524297659437259 74883079575786446489155889)
          ·
            refine ⟨56162309681839834866866917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74883079575786446489155889 56162309681839834866866917)
            ·
              refine ⟨10530433065344969037537547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56162309681839834866866917 10530433065344969037537547)
              ·
                refine ⟨15795649598017453556306321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10530433065344969037537547 15795649598017453556306321)
                ·
                  refine ⟨11846737198513090167229741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15795649598017453556306321 11846737198513090167229741)
                  ·
                    refine ⟨4442526449442408812711153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11846737198513090167229741 4442526449442408812711153)
                    ·
                      refine ⟨3331894837081806609533365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442526449442408812711153 3331894837081806609533365)
                      ·
                        rfl

theorem cell23_6488842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_6488842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488842 prefixEnd_6488842 := by exact prefixLift 6488842
  have htrace : WordTrace (prefixWord ++ tailWord_6488842) baseStart_6488842 baseEnd_6488842 := by
    simpa [prefixWord, tailWord_6488842, baseEnd_6488842] using wordTrace_append hprefix tailTrace_6488842
  have hstable : (prefixWord ++ tailWord_6488842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488842).length < 2 ^ (prefixWord ++ tailWord_6488842).sum := by decide
  have hdescent : baseEnd_6488842 < baseStart_6488842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488866 : List Nat := [3, 3, 1, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_6488866 : Nat := 118140960795 + 6488866 * 2 ^ 59
def prefixEnd_6488866 : Nat := 4983230072969 + 3 ^ 40 * 6488866 * 2
def baseEnd_6488866 : Nat := 3331907160617514515633255

theorem tailTrace_6488866 : CollatzResearch.WordTrace tailWord_6488866 prefixEnd_6488866 3331907160617514515633255 := by
  unfold tailWord_6488866
  simp only [CollatzResearch.WordTrace]
  refine ⟨59167096527488541732199613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157778924073302777952532301 59167096527488541732199613)
  ·
    refine ⟨22187661197808203149574855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59167096527488541732199613 22187661197808203149574855)
    ·
      refine ⟨33281491796712304724362283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22187661197808203149574855 33281491796712304724362283)
      ·
        refine ⟨49922237695068457086543425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33281491796712304724362283 49922237695068457086543425)
        ·
          refine ⟨37441678271301342814907569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49922237695068457086543425 37441678271301342814907569)
          ·
            refine ⟨28081258703476007111180677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37441678271301342814907569 28081258703476007111180677)
            ·
              refine ⟨5265236006901751333346377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28081258703476007111180677 5265236006901751333346377)
              ·
                refine ⟨3948927005176313500009783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265236006901751333346377 3948927005176313500009783)
                ·
                  refine ⟨5923390507764470250014675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948927005176313500009783 5923390507764470250014675)
                  ·
                    refine ⟨8885085761646705375022013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923390507764470250014675 8885085761646705375022013)
                    ·
                      refine ⟨3331907160617514515633255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885085761646705375022013 3331907160617514515633255)
                      ·
                        rfl

theorem cell23_6488866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_6488866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488866 prefixEnd_6488866 := by exact prefixLift 6488866
  have htrace : WordTrace (prefixWord ++ tailWord_6488866) baseStart_6488866 baseEnd_6488866 := by
    simpa [prefixWord, tailWord_6488866, baseEnd_6488866] using wordTrace_append hprefix tailTrace_6488866
  have hstable : (prefixWord ++ tailWord_6488866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488866).length < 2 ^ (prefixWord ++ tailWord_6488866).sum := by decide
  have hdescent : baseEnd_6488866 < baseStart_6488866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488885 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_6488885 : Nat := 118140960795 + 6488885 * 2 ^ 59
def prefixEnd_6488885 : Nat := 4983230072969 + 3 ^ 40 * 6488885 * 2
def baseEnd_6488885 : Nat := 3331916916749949941295667

theorem tailTrace_6488885 : CollatzResearch.WordTrace tailWord_6488885 prefixEnd_6488885 3331916916749949941295667 := by
  unfold tailWord_6488885
  simp only [CollatzResearch.WordTrace]
  refine ⟨236669079096885333173740109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157779386064590222115826739 236669079096885333173740109)
  ·
    refine ⟨88750904661331999940152541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236669079096885333173740109 88750904661331999940152541)
    ·
      refine ⟨33281589247999499977557203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88750904661331999940152541 33281589247999499977557203)
      ·
        refine ⟨49922383871999249966335805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33281589247999499977557203 49922383871999249966335805)
        ·
          refine ⟨18720893951999718737375927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49922383871999249966335805 18720893951999718737375927)
          ·
            refine ⟨28081340927999578106063891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18720893951999718737375927 28081340927999578106063891)
            ·
              refine ⟨42122011391999367159095837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28081340927999578106063891 42122011391999367159095837)
              ·
                refine ⟨15795754271999762684660939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42122011391999367159095837 15795754271999762684660939)
                ·
                  refine ⟨23693631407999644026991409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15795754271999762684660939 23693631407999644026991409)
                  ·
                    refine ⟨17770223555999733020243557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23693631407999644026991409 17770223555999733020243557)
                    ·
                      refine ⟨3331916916749949941295667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17770223555999733020243557 3331916916749949941295667)
                      ·
                        rfl

theorem cell23_6488885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_6488885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488885 prefixEnd_6488885 := by exact prefixLift 6488885
  have htrace : WordTrace (prefixWord ++ tailWord_6488885) baseStart_6488885 baseEnd_6488885 := by
    simpa [prefixWord, tailWord_6488885, baseEnd_6488885] using wordTrace_append hprefix tailTrace_6488885
  have hstable : (prefixWord ++ tailWord_6488885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488885).length < 2 ^ (prefixWord ++ tailWord_6488885).sum := by decide
  have hdescent : baseEnd_6488885 < baseStart_6488885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488895 : List Nat := [1, 1, 2, 2, 5, 2, 3, 7]
def baseStart_6488895 : Nat := 118140960795 + 6488895 * 2 ^ 59
def prefixEnd_6488895 : Nat := 4983230072969 + 3 ^ 40 * 6488895 * 2
def baseEnd_6488895 : Nat := 123404520428018329710023

theorem tailTrace_6488895 : CollatzResearch.WordTrace tailWord_6488895 prefixEnd_6488895 123404520428018329710023 := by
  unfold tailWord_6488895
  simp only [CollatzResearch.WordTrace]
  refine ⟨236669443826849104881604139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157779629217899403254402759 236669443826849104881604139)
  ·
    refine ⟨355004165740273657322406209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236669443826849104881604139 355004165740273657322406209)
    ·
      refine ⟨266253124305205242991804657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355004165740273657322406209 266253124305205242991804657)
      ·
        refine ⟨199689843228903932243853493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266253124305205242991804657 199689843228903932243853493)
        ·
          refine ⟨18720922802709743647861265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199689843228903932243853493 18720922802709743647861265)
          ·
            refine ⟨14040692102032307735895949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18720922802709743647861265 14040692102032307735895949)
            ·
              refine ⟨5265259538262115400960981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14040692102032307735895949 5265259538262115400960981)
              ·
                refine ⟨123404520428018329710023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5265259538262115400960981 123404520428018329710023)
                ·
                  rfl

theorem cell23_6488895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 7].length) (baseStart_6488895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488895 prefixEnd_6488895 := by exact prefixLift 6488895
  have htrace : WordTrace (prefixWord ++ tailWord_6488895) baseStart_6488895 baseEnd_6488895 := by
    simpa [prefixWord, tailWord_6488895, baseEnd_6488895] using wordTrace_append hprefix tailTrace_6488895
  have hstable : (prefixWord ++ tailWord_6488895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488895).length < 2 ^ (prefixWord ++ tailWord_6488895).sum := by decide
  have hdescent : baseEnd_6488895 < baseStart_6488895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488905 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 3]
def baseStart_6488905 : Nat := 118140960795 + 6488905 * 2 ^ 59
def prefixEnd_6488905 : Nat := 4983230072969 + 3 ^ 40 * 6488905 * 2
def baseEnd_6488905 : Nat := 3331927186363039863045575

theorem tailTrace_6488905 : CollatzResearch.WordTrace tailWord_6488905 prefixEnd_6488905 3331927186363039863045575 := by
  unfold tailWord_6488905
  simp only [CollatzResearch.WordTrace]
  refine ⟨236669808556812876589468169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157779872371208584392978779 236669808556812876589468169)
  ·
    refine ⟨177502356417609657442101127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236669808556812876589468169 177502356417609657442101127)
    ·
      refine ⟨266253534626414486163151691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177502356417609657442101127 266253534626414486163151691)
      ·
        refine ⟨399380301939621729244727537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266253534626414486163151691 399380301939621729244727537)
        ·
          refine ⟨299535226454716296933545653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399380301939621729244727537 299535226454716296933545653)
          ·
            refine ⟨28081427480129652837519905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299535226454716296933545653 28081427480129652837519905)
            ·
              refine ⟨21061070610097239628139929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28081427480129652837519905 21061070610097239628139929)
              ·
                refine ⟨15795802957572929721104947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21061070610097239628139929 15795802957572929721104947)
                ·
                  refine ⟨23693704436359394581657421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15795802957572929721104947 23693704436359394581657421)
                  ·
                    refine ⟨8885139163634772968121533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23693704436359394581657421 8885139163634772968121533)
                    ·
                      refine ⟨3331927186363039863045575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885139163634772968121533 3331927186363039863045575)
                      ·
                        rfl

theorem cell23_6488905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_6488905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488905 prefixEnd_6488905 := by exact prefixLift 6488905
  have htrace : WordTrace (prefixWord ++ tailWord_6488905) baseStart_6488905 baseEnd_6488905 := by
    simpa [prefixWord, tailWord_6488905, baseEnd_6488905] using wordTrace_append hprefix tailTrace_6488905
  have hstable : (prefixWord ++ tailWord_6488905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488905).length < 2 ^ (prefixWord ++ tailWord_6488905).sum := by decide
  have hdescent : baseEnd_6488905 < baseStart_6488905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488916 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_6488916 : Nat := 118140960795 + 6488916 * 2 ^ 59
def prefixEnd_6488916 : Nat := 4983230072969 + 3 ^ 40 * 6488916 * 2
def baseEnd_6488916 : Nat := 1110644278216746440002675

theorem tailTrace_6488916 : CollatzResearch.WordTrace tailWord_6488916 prefixEnd_6488916 1110644278216746440002675 := by
  unfold tailWord_6488916
  simp only [CollatzResearch.WordTrace]
  refine ⟨118335104879886512734059301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157780139839848683645412401 118335104879886512734059301)
  ·
    refine ⟨22187832164978721137636119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118335104879886512734059301 22187832164978721137636119)
    ·
      refine ⟨33281748247468081706454179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22187832164978721137636119 33281748247468081706454179)
      ·
        refine ⟨49922622371202122559681269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33281748247468081706454179 49922622371202122559681269)
        ·
          refine ⟨4680245847300198989970119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49922622371202122559681269 4680245847300198989970119)
          ·
            refine ⟨7020368770950298484955179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680245847300198989970119 7020368770950298484955179)
            ·
              refine ⟨10530553156425447727432769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7020368770950298484955179 10530553156425447727432769)
              ·
                refine ⟨7897914867319085795574577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10530553156425447727432769 7897914867319085795574577)
                ·
                  refine ⟨5923436150489314346680933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7897914867319085795574577 5923436150489314346680933)
                  ·
                    refine ⟨1110644278216746440002675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923436150489314346680933 1110644278216746440002675)
                    ·
                      rfl

theorem cell23_6488916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_6488916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488916 prefixEnd_6488916 := by exact prefixLift 6488916
  have htrace : WordTrace (prefixWord ++ tailWord_6488916) baseStart_6488916 baseEnd_6488916 := by
    simpa [prefixWord, tailWord_6488916, baseEnd_6488916] using wordTrace_append hprefix tailTrace_6488916
  have hstable : (prefixWord ++ tailWord_6488916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488916).length < 2 ^ (prefixWord ++ tailWord_6488916).sum := by decide
  have hdescent : baseEnd_6488916 < baseStart_6488916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488922 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_6488922 : Nat := 118140960795 + 6488922 * 2 ^ 59
def prefixEnd_6488922 : Nat := 4983230072969 + 3 ^ 40 * 6488922 * 2
def baseEnd_6488922 : Nat := 3331935915534166296532997

theorem tailTrace_6488922 : CollatzResearch.WordTrace tailWord_6488922 prefixEnd_6488922 3331935915534166296532997 := by
  unfold tailWord_6488922
  simp only [CollatzResearch.WordTrace]
  refine ⟨59167607149437822123209255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157780285731834192328558013 59167607149437822123209255)
  ·
    refine ⟨88751410724156733184813883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59167607149437822123209255 88751410724156733184813883)
    ·
      refine ⟨133127116086235099777220825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88751410724156733184813883 133127116086235099777220825)
      ·
        refine ⟨99845337064676324832915619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133127116086235099777220825 99845337064676324832915619)
        ·
          refine ⟨149768005597014487249373429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99845337064676324832915619 149768005597014487249373429)
          ·
            refine ⟨14040750524720108179628759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149768005597014487249373429 14040750524720108179628759)
            ·
              refine ⟨21061125787080162269443139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14040750524720108179628759 21061125787080162269443139)
              ·
                refine ⟨31591688680620243404164709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21061125787080162269443139 31591688680620243404164709)
                ·
                  refine ⟨5923441627616295638280883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31591688680620243404164709 5923441627616295638280883)
                  ·
                    refine ⟨8885162441424443457421325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923441627616295638280883 8885162441424443457421325)
                    ·
                      refine ⟨3331935915534166296532997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885162441424443457421325 3331935915534166296532997)
                      ·
                        rfl

theorem cell23_6488922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_6488922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488922 prefixEnd_6488922 := by exact prefixLift 6488922
  have htrace : WordTrace (prefixWord ++ tailWord_6488922) baseStart_6488922 baseEnd_6488922 := by
    simpa [prefixWord, tailWord_6488922, baseEnd_6488922] using wordTrace_append hprefix tailTrace_6488922
  have hstable : (prefixWord ++ tailWord_6488922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488922).length < 2 ^ (prefixWord ++ tailWord_6488922).sum := by decide
  have hdescent : baseEnd_6488922 < baseStart_6488922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
