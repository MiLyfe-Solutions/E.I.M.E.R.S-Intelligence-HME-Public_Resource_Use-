import V185TrunkScan20Chunk155

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_949725 : List Nat := [1, 4, 3, 1, 1, 3, 1, 4, 2]
def baseStart_949725 : Nat := 118140960795 + 949725 * 2 ^ 59
def prefixEnd_949725 : Nat := 4983230072969 + 3 ^ 40 * 949725 * 2
def baseEnd_949725 : Nat := 433480368525690604684267

theorem tailTrace_949725 : CollatzResearch.WordTrace tailWord_949725 prefixEnd_949725 433480368525690604684267 := by
  unfold tailWord_949725
  simp only [CollatzResearch.WordTrace]
  refine ⟨34639316484315999961698629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23092877656210666641132419 34639316484315999961698629)
  ·
    refine ⟨6494871840809249992818493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34639316484315999961698629 6494871840809249992818493)
    ·
      refine ⟨2435576940303468747306935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6494871840809249992818493 2435576940303468747306935)
      ·
        refine ⟨3653365410455203120960403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435576940303468747306935 3653365410455203120960403)
        ·
          refine ⟨5480048115682804681440605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653365410455203120960403 5480048115682804681440605)
          ·
            refine ⟨2055018043381051755540227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5480048115682804681440605 2055018043381051755540227)
            ·
              refine ⟨3082527065071577633310341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055018043381051755540227 3082527065071577633310341)
              ·
                refine ⟨577973824700920806245689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3082527065071577633310341 577973824700920806245689)
                ·
                  refine ⟨433480368525690604684267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577973824700920806245689 433480368525690604684267)
                  ·
                    rfl

theorem cell20_949725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_949725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949725 prefixEnd_949725 := by exact prefixLift 949725
  have htrace : WordTrace (prefixWord ++ tailWord_949725) baseStart_949725 baseEnd_949725 := by
    simpa [prefixWord, tailWord_949725, baseEnd_949725] using wordTrace_append hprefix tailTrace_949725
  have hstable : (prefixWord ++ tailWord_949725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949725).length < 2 ^ (prefixWord ++ tailWord_949725).sum := by decide
  have hdescent : baseEnd_949725 < baseStart_949725 := by decide
  rcases family_descends (prefixWord ++ tailWord_949725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949746 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_949746 : Nat := 118140960795 + 949746 * 2 ^ 59
def prefixEnd_949746 : Nat := 4983230072969 + 3 ^ 40 * 949746 * 2
def baseEnd_949746 : Nat := 433489953497907864984181

theorem tailTrace_949746 : CollatzResearch.WordTrace tailWord_949746 prefixEnd_949746 433489953497907864984181 := by
  unfold tailWord_949746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8660020604309980137053273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23093388278159947032142061 8660020604309980137053273)
  ·
    refine ⟨6495015453232485102789955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8660020604309980137053273 6495015453232485102789955)
    ·
      refine ⟨9742523179848727654184933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6495015453232485102789955 9742523179848727654184933)
      ·
        refine ⟨1826723096221636435159675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9742523179848727654184933 1826723096221636435159675)
        ·
          refine ⟨2740084644332454652739513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826723096221636435159675 2740084644332454652739513)
          ·
            refine ⟨2055063483249340989554635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2740084644332454652739513 2055063483249340989554635)
            ·
              refine ⟨3082595224874011484331953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055063483249340989554635 3082595224874011484331953)
              ·
                refine ⟨2311946418655508613248965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082595224874011484331953 2311946418655508613248965)
                ·
                  refine ⟨433489953497907864984181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311946418655508613248965 433489953497907864984181)
                  ·
                    rfl

theorem cell20_949746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_949746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949746 prefixEnd_949746 := by exact prefixLift 949746
  have htrace : WordTrace (prefixWord ++ tailWord_949746) baseStart_949746 baseEnd_949746 := by
    simpa [prefixWord, tailWord_949746, baseEnd_949746] using wordTrace_append hprefix tailTrace_949746
  have hstable : (prefixWord ++ tailWord_949746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949746).length < 2 ^ (prefixWord ++ tailWord_949746).sum := by decide
  have hdescent : baseEnd_949746 < baseStart_949746 := by decide
  rcases family_descends (prefixWord ++ tailWord_949746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949784 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_949784 : Nat := 118140960795 + 949784 * 2 ^ 59
def prefixEnd_949784 : Nat := 4983230072969 + 3 ^ 40 * 949784 * 2
def baseEnd_949784 : Nat := 433507297733348621717359

theorem tailTrace_949784 : CollatzResearch.WordTrace tailWord_949784 prefixEnd_949784 433507297733348621717359 := by
  unfold tailWord_949784
  simp only [CollatzResearch.WordTrace]
  refine ⟨17320734195551126519048203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23094312260734835358730937 17320734195551126519048203)
  ·
    refine ⟨25981101293326689778572305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17320734195551126519048203 25981101293326689778572305)
    ·
      refine ⟨19485825969995017333929229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25981101293326689778572305 19485825969995017333929229)
      ·
        refine ⟨7307184738748131500223461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19485825969995017333929229 7307184738748131500223461)
        ·
          refine ⟨1370097138515274656291899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7307184738748131500223461 1370097138515274656291899)
          ·
            refine ⟨2055145707772911984437849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370097138515274656291899 2055145707772911984437849)
            ·
              refine ⟨1541359280829683988328387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055145707772911984437849 1541359280829683988328387)
              ·
                refine ⟨2312038921244525982492581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541359280829683988328387 2312038921244525982492581)
                ·
                  refine ⟨433507297733348621717359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312038921244525982492581 433507297733348621717359)
                  ·
                    rfl

theorem cell20_949784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_949784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949784 prefixEnd_949784 := by exact prefixLift 949784
  have htrace : WordTrace (prefixWord ++ tailWord_949784) baseStart_949784 baseEnd_949784 := by
    simpa [prefixWord, tailWord_949784, baseEnd_949784] using wordTrace_append hprefix tailTrace_949784
  have hstable : (prefixWord ++ tailWord_949784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949784).length < 2 ^ (prefixWord ++ tailWord_949784).sum := by decide
  have hdescent : baseEnd_949784 < baseStart_949784 := by decide
  rcases family_descends (prefixWord ++ tailWord_949784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949912 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_949912 : Nat := 118140960795 + 949912 * 2 ^ 59
def prefixEnd_949912 : Nat := 4983230072969 + 3 ^ 40 * 949912 * 2
def baseEnd_949912 : Nat := 433565720421149065450169

theorem tailTrace_949912 : CollatzResearch.WordTrace tailWord_949912 prefixEnd_949912 433565720421149065450169 := by
  unfold tailWord_949912
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323068467319265449377995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23097424623092353932503993 17323068467319265449377995)
  ·
    refine ⟨25984602700978898174066993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17323068467319265449377995 25984602700978898174066993)
    ·
      refine ⟨19488452025734173630550245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25984602700978898174066993 19488452025734173630550245)
      ·
        refine ⟨3654084754825157555728171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19488452025734173630550245 3654084754825157555728171)
        ·
          refine ⟨5481127132237736333592257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654084754825157555728171 5481127132237736333592257)
          ·
            refine ⟨4110845349178302250194193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5481127132237736333592257 4110845349178302250194193)
            ·
              refine ⟨3083134011883726687645645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110845349178302250194193 3083134011883726687645645)
              ·
                refine ⟨1156175254456397507867117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3083134011883726687645645 1156175254456397507867117)
                ·
                  refine ⟨433565720421149065450169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156175254456397507867117 433565720421149065450169)
                  ·
                    rfl

theorem cell20_949912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_949912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949912 prefixEnd_949912 := by exact prefixLift 949912
  have htrace : WordTrace (prefixWord ++ tailWord_949912) baseStart_949912 baseEnd_949912 := by
    simpa [prefixWord, tailWord_949912, baseEnd_949912] using wordTrace_append hprefix tailTrace_949912
  have hstable : (prefixWord ++ tailWord_949912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949912).length < 2 ^ (prefixWord ++ tailWord_949912).sum := by decide
  have hdescent : baseEnd_949912 < baseStart_949912 := by decide
  rcases family_descends (prefixWord ++ tailWord_949912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949950 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_949950 : Nat := 118140960795 + 949950 * 2 ^ 59
def prefixEnd_949950 : Nat := 4983230072969 + 3 ^ 40 * 949950 * 2
def baseEnd_949950 : Nat := 433583064656589822183347

theorem tailTrace_949950 : CollatzResearch.WordTrace tailWord_949950 prefixEnd_949950 433583064656589822183347 := by
  unfold tailWord_949950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330940363562607923579913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23098348605667242259092869 4330940363562607923579913)
  ·
    refine ⟨3248205272671955942684935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4330940363562607923579913 3248205272671955942684935)
    ·
      refine ⟨4872307909007933914027403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3248205272671955942684935 4872307909007933914027403)
      ·
        refine ⟨7308461863511900871041105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872307909007933914027403 7308461863511900871041105)
        ·
          refine ⟨5481346397633925653280829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7308461863511900871041105 5481346397633925653280829)
          ·
            refine ⟨2055504899112722119980311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5481346397633925653280829 2055504899112722119980311)
            ·
              refine ⟨3083257348669083179970467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055504899112722119980311 3083257348669083179970467)
              ·
                refine ⟨4624886023003624769955701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083257348669083179970467 4624886023003624769955701)
                ·
                  refine ⟨433583064656589822183347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624886023003624769955701 433583064656589822183347)
                  ·
                    rfl

theorem cell20_949950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_949950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949950 prefixEnd_949950 := by exact prefixLift 949950
  have htrace : WordTrace (prefixWord ++ tailWord_949950) baseStart_949950 baseEnd_949950 := by
    simpa [prefixWord, tailWord_949950, baseEnd_949950] using wordTrace_append hprefix tailTrace_949950
  have hstable : (prefixWord ++ tailWord_949950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949950).length < 2 ^ (prefixWord ++ tailWord_949950).sum := by decide
  have hdescent : baseEnd_949950 < baseStart_949950 := by decide
  rcases family_descends (prefixWord ++ tailWord_949950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950026 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_950026 : Nat := 118140960795 + 950026 * 2 ^ 59
def prefixEnd_950026 : Nat := 4983230072969 + 3 ^ 40 * 950026 * 2
def baseEnd_950026 : Nat := 433617753127471335649703

theorem tailTrace_950026 : CollatzResearch.WordTrace tailWord_950026 prefixEnd_950026 433617753127471335649703 := by
  unfold tailWord_950026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662573714056382092101483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23100196570817018912270621 8662573714056382092101483)
  ·
    refine ⟨12993860571084573138152225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8662573714056382092101483 12993860571084573138152225)
    ·
      refine ⟨9745395428313429853614169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12993860571084573138152225 9745395428313429853614169)
      ·
        refine ⟨7309046571235072390210627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9745395428313429853614169 7309046571235072390210627)
        ·
          refine ⟨10963569856852608585315941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309046571235072390210627 10963569856852608585315941)
          ·
            refine ⟨2055669348159864109746739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10963569856852608585315941 2055669348159864109746739)
            ·
              refine ⟨3083504022239796164620109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055669348159864109746739 3083504022239796164620109)
              ·
                refine ⟨1156314008339923561732541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3083504022239796164620109 1156314008339923561732541)
                ·
                  refine ⟨433617753127471335649703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156314008339923561732541 433617753127471335649703)
                  ·
                    rfl

theorem cell20_950026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_950026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950026 prefixEnd_950026 := by exact prefixLift 950026
  have htrace : WordTrace (prefixWord ++ tailWord_950026) baseStart_950026 baseEnd_950026 := by
    simpa [prefixWord, tailWord_950026, baseEnd_950026] using wordTrace_append hprefix tailTrace_950026
  have hstable : (prefixWord ++ tailWord_950026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950026).length < 2 ^ (prefixWord ++ tailWord_950026).sum := by decide
  have hdescent : baseEnd_950026 < baseStart_950026 := by decide
  rcases family_descends (prefixWord ++ tailWord_950026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950050 : List Nat := [3, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_950050 : Nat := 118140960795 + 950050 * 2 ^ 59
def prefixEnd_950050 : Nat := 4983230072969 + 3 ^ 40 * 950050 * 2
def baseEnd_950050 : Nat := 433628707381433918849605

theorem tailTrace_950050 : CollatzResearch.WordTrace tailWord_950050 prefixEnd_950050 433628707381433918849605 := by
  unfold tailWord_950050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662792552034645116819901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23100780138759053644853069 8662792552034645116819901)
  ·
    refine ⟨3248547207012991918807463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8662792552034645116819901 3248547207012991918807463)
    ·
      refine ⟨4872820810519487878211195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3248547207012991918807463 4872820810519487878211195)
      ·
        refine ⟨7309231215779231817316793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872820810519487878211195 7309231215779231817316793)
        ·
          refine ⟨5481923411834423862987595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7309231215779231817316793 5481923411834423862987595)
          ·
            refine ⟨8222885117751635794481393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481923411834423862987595 8222885117751635794481393)
            ·
              refine ⟨6167163838313726845861045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222885117751635794481393 6167163838313726845861045)
              ·
                refine ⟨578171609841911891799473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6167163838313726845861045 578171609841911891799473)
                ·
                  refine ⟨433628707381433918849605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578171609841911891799473 433628707381433918849605)
                  ·
                    rfl

theorem cell20_950050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_950050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950050 prefixEnd_950050 := by exact prefixLift 950050
  have htrace : WordTrace (prefixWord ++ tailWord_950050) baseStart_950050 baseEnd_950050 := by
    simpa [prefixWord, tailWord_950050, baseEnd_950050] using wordTrace_append hprefix tailTrace_950050
  have hstable : (prefixWord ++ tailWord_950050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950050).length < 2 ^ (prefixWord ++ tailWord_950050).sum := by decide
  have hdescent : baseEnd_950050 < baseStart_950050 := by decide
  rcases family_descends (prefixWord ++ tailWord_950050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950085 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 3]
def baseStart_950085 : Nat := 118140960795 + 950085 * 2 ^ 59
def prefixEnd_950085 : Nat := 4983230072969 + 3 ^ 40 * 950085 * 2
def baseEnd_950085 : Nat := 433644682335129352682795

theorem tailTrace_950085 : CollatzResearch.WordTrace tailWord_950085 prefixEnd_950085 433644682335129352682795 := by
  unfold tailWord_950085
  simp only [CollatzResearch.WordTrace]
  refine ⟨34652446763011781444803709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23101631175341187629869139 34652446763011781444803709)
  ·
    refine ⟨12994667536129418041801391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34652446763011781444803709 12994667536129418041801391)
    ·
      refine ⟨19492001304194127062702087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12994667536129418041801391 19492001304194127062702087)
      ·
        refine ⟨29238001956291190594053131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19492001304194127062702087 29238001956291190594053131)
        ·
          refine ⟨43857002934436785891079697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29238001956291190594053131 43857002934436785891079697)
          ·
            refine ⟨32892752200827589418309773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43857002934436785891079697 32892752200827589418309773)
            ·
              refine ⟨12334782075310346031866165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32892752200827589418309773 12334782075310346031866165)
              ·
                refine ⟨1156385819560344940487453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12334782075310346031866165 1156385819560344940487453)
                ·
                  refine ⟨433644682335129352682795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156385819560344940487453 433644682335129352682795)
                  ·
                    rfl

theorem cell20_950085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_950085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950085 prefixEnd_950085 := by exact prefixLift 950085
  have htrace : WordTrace (prefixWord ++ tailWord_950085) baseStart_950085 baseEnd_950085 := by
    simpa [prefixWord, tailWord_950085, baseEnd_950085] using wordTrace_append hprefix tailTrace_950085
  have hstable : (prefixWord ++ tailWord_950085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950085).length < 2 ^ (prefixWord ++ tailWord_950085).sum := by decide
  have hdescent : baseEnd_950085 < baseStart_950085 := by decide
  rcases family_descends (prefixWord ++ tailWord_950085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950116 : List Nat := [2, 3, 1, 1, 5, 1, 7]
def baseStart_950116 : Nat := 118140960795 + 950116 * 2 ^ 59
def prefixEnd_950116 : Nat := 4983230072969 + 3 ^ 40 * 950116 * 2
def baseEnd_950116 : Nat := 48184314619981224738815

theorem tailTrace_950116 : CollatzResearch.WordTrace tailWord_950116 prefixEnd_950116 48184314619981224738815 := by
  unfold tailWord_950116
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326788712949736869591101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23102384950599649159454801 17326788712949736869591101)
  ·
    refine ⟨6497545767356151326096663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17326788712949736869591101 6497545767356151326096663)
    ·
      refine ⟨9746318651034226989144995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6497545767356151326096663 9746318651034226989144995)
      ·
        refine ⟨14619477976551340483717493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9746318651034226989144995 14619477976551340483717493)
        ·
          refine ⟨1370576060301688170348515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14619477976551340483717493 1370576060301688170348515)
          ·
            refine ⟨2055864090452532255522773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370576060301688170348515 2055864090452532255522773)
            ·
              refine ⟨48184314619981224738815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2055864090452532255522773 48184314619981224738815)
              ·
                rfl

theorem cell20_950116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 7].length) (baseStart_950116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950116 prefixEnd_950116 := by exact prefixLift 950116
  have htrace : WordTrace (prefixWord ++ tailWord_950116) baseStart_950116 baseEnd_950116 := by
    simpa [prefixWord, tailWord_950116, baseEnd_950116] using wordTrace_append hprefix tailTrace_950116
  have hstable : (prefixWord ++ tailWord_950116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950116).length < 2 ^ (prefixWord ++ tailWord_950116).sum := by decide
  have hdescent : baseEnd_950116 < baseStart_950116 := by decide
  rcases family_descends (prefixWord ++ tailWord_950116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950126 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_950126 : Nat := 118140960795 + 950126 * 2 ^ 59
def prefixEnd_950126 : Nat := 4983230072969 + 3 ^ 40 * 950126 * 2
def baseEnd_950126 : Nat := 433663395852315432315961

theorem tailTrace_950126 : CollatzResearch.WordTrace tailWord_950126 prefixEnd_950126 433663395852315432315961 := by
  unfold tailWord_950126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331742769482905680880779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23102628103908830298030821 4331742769482905680880779)
  ·
    refine ⟨6497614154224358521321169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331742769482905680880779 6497614154224358521321169)
    ·
      refine ⟨4873210615668268890990877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6497614154224358521321169 4873210615668268890990877)
      ·
        refine ⟨1827453980875600834121579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4873210615668268890990877 1827453980875600834121579)
        ·
          refine ⟨2741180971313401251182369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827453980875600834121579 2741180971313401251182369)
          ·
            refine ⟨2055885728485050938386777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2741180971313401251182369 2055885728485050938386777)
            ·
              refine ⟨1541914296363788203790083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055885728485050938386777 1541914296363788203790083)
              ·
                refine ⟨2312871444545682305685125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541914296363788203790083 2312871444545682305685125)
                ·
                  refine ⟨433663395852315432315961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312871444545682305685125 433663395852315432315961)
                  ·
                    rfl

theorem cell20_950126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_950126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950126 prefixEnd_950126 := by exact prefixLift 950126
  have htrace : WordTrace (prefixWord ++ tailWord_950126) baseStart_950126 baseEnd_950126 := by
    simpa [prefixWord, tailWord_950126, baseEnd_950126] using wordTrace_append hprefix tailTrace_950126
  have hstable : (prefixWord ++ tailWord_950126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950126).length < 2 ^ (prefixWord ++ tailWord_950126).sum := by decide
  have hdescent : baseEnd_950126 < baseStart_950126 := by decide
  rcases family_descends (prefixWord ++ tailWord_950126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950137 : List Nat := [1, 2, 1, 3, 2, 2, 2, 7]
def baseStart_950137 : Nat := 118140960795 + 950137 * 2 ^ 59
def prefixEnd_950137 : Nat := 4983230072969 + 3 ^ 40 * 950137 * 2
def baseEnd_950137 : Nat := 144556138850682760983083

theorem tailTrace_950137 : CollatzResearch.WordTrace tailWord_950137 prefixEnd_950137 144556138850682760983083 := by
  unfold tailWord_950137
  simp only [CollatzResearch.WordTrace]
  refine ⟨34654343358823394325696665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23102895572548929550464443 34654343358823394325696665)
  ·
    refine ⟨25990757519117545744272499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34654343358823394325696665 25990757519117545744272499)
    ·
      refine ⟨38986136278676318616408749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25990757519117545744272499 38986136278676318616408749)
      ·
        refine ⟨14619801104503619481153281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38986136278676318616408749 14619801104503619481153281)
        ·
          refine ⟨10964850828377714610864961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14619801104503619481153281 10964850828377714610864961)
          ·
            refine ⟨8223638121283285958148721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10964850828377714610864961 8223638121283285958148721)
            ·
              refine ⟨6167728590962464468611541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223638121283285958148721 6167728590962464468611541)
              ·
                refine ⟨144556138850682760983083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6167728590962464468611541 144556138850682760983083)
                ·
                  rfl

theorem cell20_950137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_950137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950137 prefixEnd_950137 := by exact prefixLift 950137
  have htrace : WordTrace (prefixWord ++ tailWord_950137) baseStart_950137 baseEnd_950137 := by
    simpa [prefixWord, tailWord_950137, baseEnd_950137] using wordTrace_append hprefix tailTrace_950137
  have hstable : (prefixWord ++ tailWord_950137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950137).length < 2 ^ (prefixWord ++ tailWord_950137).sum := by decide
  have hdescent : baseEnd_950137 < baseStart_950137 := by decide
  rcases family_descends (prefixWord ++ tailWord_950137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950223 : List Nat := [1, 1, 2, 1, 1, 5, 2, 5, 2]
def baseStart_950223 : Nat := 118140960795 + 950223 * 2 ^ 59
def prefixEnd_950223 : Nat := 4983230072969 + 3 ^ 40 * 950223 * 2
def baseEnd_950223 : Nat := 433707669295414206082231

theorem tailTrace_950223 : CollatzResearch.WordTrace tailWord_950223 prefixEnd_950223 433707669295414206082231 := by
  unfold tailWord_950223
  simp only [CollatzResearch.WordTrace]
  refine ⟨34657480036511831013327323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23104986691007887342218215 34657480036511831013327323)
  ·
    refine ⟨51986220054767746519990985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34657480036511831013327323 51986220054767746519990985)
    ·
      refine ⟨38989665041075809889993239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51986220054767746519990985 38989665041075809889993239)
      ·
        refine ⟨58484497561613714834989859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38989665041075809889993239 58484497561613714834989859)
        ·
          refine ⟨87726746342420572252484789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58484497561613714834989859 87726746342420572252484789)
          ·
            refine ⟨8224382469601928648670449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87726746342420572252484789 8224382469601928648670449)
            ·
              refine ⟨6168286852201446486502837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8224382469601928648670449 6168286852201446486502837)
              ·
                refine ⟨578276892393885608109641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6168286852201446486502837 578276892393885608109641)
                ·
                  refine ⟨433707669295414206082231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578276892393885608109641 433707669295414206082231)
                  ·
                    rfl

theorem cell20_950223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 2].length) (baseStart_950223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950223 prefixEnd_950223 := by exact prefixLift 950223
  have htrace : WordTrace (prefixWord ++ tailWord_950223) baseStart_950223 baseEnd_950223 := by
    simpa [prefixWord, tailWord_950223, baseEnd_950223] using wordTrace_append hprefix tailTrace_950223
  have hstable : (prefixWord ++ tailWord_950223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950223).length < 2 ^ (prefixWord ++ tailWord_950223).sum := by decide
  have hdescent : baseEnd_950223 < baseStart_950223 := by decide
  rcases family_descends (prefixWord ++ tailWord_950223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950230 : List Nat := [5, 2, 1, 1, 11]
def baseStart_950230 : Nat := 118140960795 + 950230 * 2 ^ 59
def prefixEnd_950230 : Nat := 4983230072969 + 3 ^ 40 * 950230 * 2
def baseEnd_950230 : Nat := 5354455114643867812949

theorem tailTrace_950230 : CollatzResearch.WordTrace tailWord_950230 prefixEnd_950230 5354455114643867812949 := by
  unfold tailWord_950230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166108459217904450552009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23105156898324314139221429 2166108459217904450552009)
  ·
    refine ⟨1624581344413428337914007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2166108459217904450552009 1624581344413428337914007)
    ·
      refine ⟨2436872016620142506871011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624581344413428337914007 2436872016620142506871011)
      ·
        refine ⟨3655308024930213760306517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436872016620142506871011 3655308024930213760306517)
        ·
          refine ⟨5354455114643867812949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3655308024930213760306517 5354455114643867812949)
          ·
            rfl

theorem cell20_950230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 11].length) (baseStart_950230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950230 prefixEnd_950230 := by exact prefixLift 950230
  have htrace : WordTrace (prefixWord ++ tailWord_950230) baseStart_950230 baseEnd_950230 := by
    simpa [prefixWord, tailWord_950230, baseEnd_950230] using wordTrace_append hprefix tailTrace_950230
  have hstable : (prefixWord ++ tailWord_950230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950230).length < 2 ^ (prefixWord ++ tailWord_950230).sum := by decide
  have hdescent : baseEnd_950230 < baseStart_950230 := by decide
  rcases family_descends (prefixWord ++ tailWord_950230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950244 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_950244 : Nat := 118140960795 + 950244 * 2 ^ 59
def prefixEnd_950244 : Nat := 4983230072969 + 3 ^ 40 * 950244 * 2
def baseEnd_950244 : Nat := 433717254267631466382145

theorem tailTrace_950244 : CollatzResearch.WordTrace tailWord_950244 prefixEnd_950244 433717254267631466382145 := by
  unfold tailWord_950244
  simp only [CollatzResearch.WordTrace]
  refine ⟨17329122984717875799920893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23105497312957167733227857 17329122984717875799920893)
  ·
    refine ⟨6498421119269203424970335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17329122984717875799920893 6498421119269203424970335)
    ·
      refine ⟨9747631678903805137455503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498421119269203424970335 9747631678903805137455503)
      ·
        refine ⟨14621447518355707706183255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9747631678903805137455503 14621447518355707706183255)
        ·
          refine ⟨21932171277533561559274883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14621447518355707706183255 21932171277533561559274883)
          ·
            refine ⟨32898256916300342338912325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21932171277533561559274883 32898256916300342338912325)
            ·
              refine ⟨6168423171806314188546061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32898256916300342338912325 6168423171806314188546061)
              ·
                refine ⟨2313158689427367820704773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6168423171806314188546061 2313158689427367820704773)
                ·
                  refine ⟨433717254267631466382145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313158689427367820704773 433717254267631466382145)
                  ·
                    rfl

theorem cell20_950244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_950244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950244 prefixEnd_950244 := by exact prefixLift 950244
  have htrace : WordTrace (prefixWord ++ tailWord_950244) baseStart_950244 baseEnd_950244 := by
    simpa [prefixWord, tailWord_950244, baseEnd_950244] using wordTrace_append hprefix tailTrace_950244
  have hstable : (prefixWord ++ tailWord_950244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950244).length < 2 ^ (prefixWord ++ tailWord_950244).sum := by decide
  have hdescent : baseEnd_950244 < baseStart_950244 := by decide
  rcases family_descends (prefixWord ++ tailWord_950244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950247 : List Nat := [1, 1, 5, 2, 3, 2, 1, 5]
def baseStart_950247 : Nat := 118140960795 + 950247 * 2 ^ 59
def prefixEnd_950247 : Nat := 4983230072969 + 3 ^ 40 * 950247 * 2
def baseEnd_950247 : Nat := 144572874516458929760711

theorem tailTrace_950247 : CollatzResearch.WordTrace tailWord_950247 prefixEnd_950247 144572874516458929760711 := by
  unfold tailWord_950247
  simp only [CollatzResearch.WordTrace]
  refine ⟨34658355388424883112200995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23105570258949922074800663 34658355388424883112200995)
  ·
    refine ⟨51987533082637324668301493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34658355388424883112200995 51987533082637324668301493)
    ·
      refine ⟨4873831226497249187653265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51987533082637324668301493 4873831226497249187653265)
      ·
        refine ⟨3655373419872936890739949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4873831226497249187653265 3655373419872936890739949)
        ·
          refine ⟨1370765032452351334027481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3655373419872936890739949 1370765032452351334027481)
          ·
            refine ⟨1028073774339263500520611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370765032452351334027481 1028073774339263500520611)
            ·
              refine ⟨1542110661508895250780917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028073774339263500520611 1542110661508895250780917)
              ·
                refine ⟨144572874516458929760711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1542110661508895250780917 144572874516458929760711)
                ·
                  rfl

theorem cell20_950247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_950247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950247 prefixEnd_950247 := by exact prefixLift 950247
  have htrace : WordTrace (prefixWord ++ tailWord_950247) baseStart_950247 baseEnd_950247 := by
    simpa [prefixWord, tailWord_950247, baseEnd_950247] using wordTrace_append hprefix tailTrace_950247
  have hstable : (prefixWord ++ tailWord_950247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950247).length < 2 ^ (prefixWord ++ tailWord_950247).sum := by decide
  have hdescent : baseEnd_950247 < baseStart_950247 := by decide
  rcases family_descends (prefixWord ++ tailWord_950247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950254 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_950254 : Nat := 118140960795 + 950254 * 2 ^ 59
def prefixEnd_950254 : Nat := 4983230072969 + 3 ^ 40 * 950254 * 2
def baseEnd_950254 : Nat := 433721818540115876048771

theorem tailTrace_950254 : CollatzResearch.WordTrace tailWord_950254 prefixEnd_950254 433721818540115876048771 := by
  unfold tailWord_950254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332326337424940413463227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23105740466266348871803877 4332326337424940413463227)
  ·
    refine ⟨6498489506137410620194841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4332326337424940413463227 6498489506137410620194841)
    ·
      refine ⟨4873867129603057965146131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6498489506137410620194841 4873867129603057965146131)
      ·
        refine ⟨7310800694404586947719197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873867129603057965146131 7310800694404586947719197)
        ·
          refine ⟨2741550260401720105394699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7310800694404586947719197 2741550260401720105394699)
          ·
            refine ⟨4112325390602580158092049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741550260401720105394699 4112325390602580158092049)
            ·
              refine ⟨3084244042951935118569037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112325390602580158092049 3084244042951935118569037)
              ·
                refine ⟨1156591516106975669463389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084244042951935118569037 1156591516106975669463389)
                ·
                  refine ⟨433721818540115876048771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156591516106975669463389 433721818540115876048771)
                  ·
                    rfl

theorem cell20_950254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_950254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950254 prefixEnd_950254 := by exact prefixLift 950254
  have htrace : WordTrace (prefixWord ++ tailWord_950254) baseStart_950254 baseEnd_950254 := by
    simpa [prefixWord, tailWord_950254, baseEnd_950254] using wordTrace_append hprefix tailTrace_950254
  have hstable : (prefixWord ++ tailWord_950254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950254).length < 2 ^ (prefixWord ++ tailWord_950254).sum := by decide
  have hdescent : baseEnd_950254 < baseStart_950254 := by decide
  rcases family_descends (prefixWord ++ tailWord_950254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950268 : List Nat := [2, 2, 2, 1, 2, 2, 5, 4]
def baseStart_950268 : Nat := 118140960795 + 950268 * 2 ^ 59
def prefixEnd_950268 : Nat := 4983230072969 + 3 ^ 40 * 950268 * 2
def baseEnd_950268 : Nat := 144576069507198016527349

theorem tailTrace_950268 : CollatzResearch.WordTrace tailWord_950268 prefixEnd_950268 144576069507198016527349 := by
  unfold tailWord_950268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17329560660674401849357729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23106080880899202465810305 17329560660674401849357729)
  ·
    refine ⟨12997170495505801387018297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17329560660674401849357729 12997170495505801387018297)
    ·
      refine ⟨9747877871629351040263723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12997170495505801387018297 9747877871629351040263723)
      ·
        refine ⟨14621816807444026560395585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9747877871629351040263723 14621816807444026560395585)
        ·
          refine ⟨10966362605583019920296689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14621816807444026560395585 10966362605583019920296689)
          ·
            refine ⟨8224771954187264940222517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10966362605583019920296689 8224771954187264940222517)
            ·
              refine ⟨771072370705056088145861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8224771954187264940222517 771072370705056088145861)
              ·
                refine ⟨144576069507198016527349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 771072370705056088145861 144576069507198016527349)
                ·
                  rfl

theorem cell20_950268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_950268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950268 prefixEnd_950268 := by exact prefixLift 950268
  have htrace : WordTrace (prefixWord ++ tailWord_950268) baseStart_950268 baseEnd_950268 := by
    simpa [prefixWord, tailWord_950268, baseEnd_950268] using wordTrace_append hprefix tailTrace_950268
  have hstable : (prefixWord ++ tailWord_950268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950268).length < 2 ^ (prefixWord ++ tailWord_950268).sum := by decide
  have hdescent : baseEnd_950268 < baseStart_950268 := by decide
  rcases family_descends (prefixWord ++ tailWord_950268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950320 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_950320 : Nat := 118140960795 + 950320 * 2 ^ 59
def prefixEnd_950320 : Nat := 4983230072969 + 3 ^ 40 * 950320 * 2
def baseEnd_950320 : Nat := 433751942738512979848501

theorem tailTrace_950320 : CollatzResearch.WordTrace tailWord_950320 prefixEnd_950320 433751942738512979848501 := by
  unfold tailWord_950320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330508958580208289804207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23107345278106944386405609 17330508958580208289804207)
  ·
    refine ⟨25995763437870312434706311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17330508958580208289804207 25995763437870312434706311)
    ·
      refine ⟨38993645156805468652059467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25995763437870312434706311 38993645156805468652059467)
      ·
        refine ⟨58490467735208202978089201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38993645156805468652059467 58490467735208202978089201)
        ·
          refine ⟨43867850801406152233566901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58490467735208202978089201 43867850801406152233566901)
          ·
            refine ⟨4112611012631826771896897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43867850801406152233566901 4112611012631826771896897)
            ·
              refine ⟨3084458259473870078922673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112611012631826771896897 3084458259473870078922673)
              ·
                refine ⟨2313343694605402559192005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084458259473870078922673 2313343694605402559192005)
                ·
                  refine ⟨433751942738512979848501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313343694605402559192005 433751942738512979848501)
                  ·
                    rfl

theorem cell20_950320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_950320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950320 prefixEnd_950320 := by exact prefixLift 950320
  have htrace : WordTrace (prefixWord ++ tailWord_950320) baseStart_950320 baseEnd_950320 := by
    simpa [prefixWord, tailWord_950320, baseEnd_950320] using wordTrace_append hprefix tailTrace_950320
  have hstable : (prefixWord ++ tailWord_950320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950320).length < 2 ^ (prefixWord ++ tailWord_950320).sum := by decide
  have hdescent : baseEnd_950320 < baseStart_950320 := by decide
  rcases family_descends (prefixWord ++ tailWord_950320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950354 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_950354 : Nat := 118140960795 + 950354 * 2 ^ 59
def prefixEnd_950354 : Nat := 4983230072969 + 3 ^ 40 * 950354 * 2
def baseEnd_950354 : Nat := 433767461264959972715029

theorem tailTrace_950354 : CollatzResearch.WordTrace tailWord_950354 prefixEnd_950354 433767461264959972715029 := by
  unfold tailWord_950354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8665564499759310096586529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23108171999358160257564077 8665564499759310096586529)
  ·
    refine ⟨6499173374819482572439897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8665564499759310096586529 6499173374819482572439897)
    ·
      refine ⟨4874380031114611929329923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6499173374819482572439897 4874380031114611929329923)
      ·
        refine ⟨7311570046671917893994885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874380031114611929329923 7311570046671917893994885)
        ·
          refine ⟨1370919383750984605124041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7311570046671917893994885 1370919383750984605124041)
          ·
            refine ⟨1028189537813238453843031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370919383750984605124041 1028189537813238453843031)
            ·
              refine ⟨1542284306719857680764547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028189537813238453843031 1542284306719857680764547)
              ·
                refine ⟨2313426460079786521146821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542284306719857680764547 2313426460079786521146821)
                ·
                  refine ⟨433767461264959972715029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313426460079786521146821 433767461264959972715029)
                  ·
                    rfl

theorem cell20_950354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_950354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950354 prefixEnd_950354 := by exact prefixLift 950354
  have htrace : WordTrace (prefixWord ++ tailWord_950354) baseStart_950354 baseEnd_950354 := by
    simpa [prefixWord, tailWord_950354, baseEnd_950354] using wordTrace_append hprefix tailTrace_950354
  have hstable : (prefixWord ++ tailWord_950354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950354).length < 2 ^ (prefixWord ++ tailWord_950354).sum := by decide
  have hdescent : baseEnd_950354 < baseStart_950354 := by decide
  rcases family_descends (prefixWord ++ tailWord_950354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950368 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_950368 : Nat := 118140960795 + 950368 * 2 ^ 59
def prefixEnd_950368 : Nat := 4983230072969 + 3 ^ 40 * 950368 * 2
def baseEnd_950368 : Nat := 433773851246438146248305

theorem tailTrace_950368 : CollatzResearch.WordTrace tailWord_950368 prefixEnd_950368 433773851246438146248305 := by
  unfold tailWord_950368
  simp only [CollatzResearch.WordTrace]
  refine ⟨17331384310493260388677879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23108512413991013851570505 17331384310493260388677879)
  ·
    refine ⟨25997076465739890583016819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17331384310493260388677879 25997076465739890583016819)
    ·
      refine ⟨38995614698609835874525229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25997076465739890583016819 38995614698609835874525229)
      ·
        refine ⟨14623355511978688452946961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38995614698609835874525229 14623355511978688452946961)
        ·
          refine ⟨10967516633984016339710221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14623355511978688452946961 10967516633984016339710221)
          ·
            refine ⟨4112818737744006127391333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10967516633984016339710221 4112818737744006127391333)
            ·
              refine ⟨771153513327001148885875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4112818737744006127391333 771153513327001148885875)
              ·
                refine ⟨1156730269990501723328813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771153513327001148885875 1156730269990501723328813)
                ·
                  refine ⟨433773851246438146248305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156730269990501723328813 433773851246438146248305)
                  ·
                    rfl

theorem cell20_950368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_950368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950368 prefixEnd_950368 := by exact prefixLift 950368
  have htrace : WordTrace (prefixWord ++ tailWord_950368) baseStart_950368 baseEnd_950368 := by
    simpa [prefixWord, tailWord_950368, baseEnd_950368] using wordTrace_append hprefix tailTrace_950368
  have hstable : (prefixWord ++ tailWord_950368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950368).length < 2 ^ (prefixWord ++ tailWord_950368).sum := by decide
  have hdescent : baseEnd_950368 < baseStart_950368 := by decide
  rcases family_descends (prefixWord ++ tailWord_950368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950417 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_950417 : Nat := 118140960795 + 950417 * 2 ^ 59
def prefixEnd_950417 : Nat := 4983230072969 + 3 ^ 40 * 950417 * 2
def baseEnd_950417 : Nat := 433796216181611753614771

theorem tailTrace_950417 : CollatzResearch.WordTrace tailWord_950417 prefixEnd_950417 433796216181611753614771 := by
  unfold tailWord_950417
  simp only [CollatzResearch.WordTrace]
  refine ⟨34664555797809002145889505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23109703865206001430593003 34664555797809002145889505)
  ·
    refine ⟨25998416848356751609417129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34664555797809002145889505 25998416848356751609417129)
    ·
      refine ⟨19498812636267563707062847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25998416848356751609417129 19498812636267563707062847)
      ·
        refine ⟨29248218954401345560594271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19498812636267563707062847 29248218954401345560594271)
        ·
          refine ⟨43872328431602018340891407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29248218954401345560594271 43872328431602018340891407)
          ·
            refine ⟨65808492647403027511337111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43872328431602018340891407 65808492647403027511337111)
            ·
              refine ⟨98712738971104541267005667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65808492647403027511337111 98712738971104541267005667)
              ·
                refine ⟨148069108456656811900508501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98712738971104541267005667 148069108456656811900508501)
                ·
                  refine ⟨433796216181611753614771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 148069108456656811900508501 433796216181611753614771)
                  ·
                    rfl

theorem cell20_950417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_950417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950417 prefixEnd_950417 := by exact prefixLift 950417
  have htrace : WordTrace (prefixWord ++ tailWord_950417) baseStart_950417 baseEnd_950417 := by
    simpa [prefixWord, tailWord_950417, baseEnd_950417] using wordTrace_append hprefix tailTrace_950417
  have hstable : (prefixWord ++ tailWord_950417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950417).length < 2 ^ (prefixWord ++ tailWord_950417).sum := by decide
  have hdescent : baseEnd_950417 < baseStart_950417 := by decide
  rcases family_descends (prefixWord ++ tailWord_950417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950430 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_950430 : Nat := 118140960795 + 950430 * 2 ^ 59
def prefixEnd_950430 : Nat := 4983230072969 + 3 ^ 40 * 950430 * 2
def baseEnd_950430 : Nat := 433802149735841486181385

theorem tailTrace_950430 : CollatzResearch.WordTrace tailWord_950430 prefixEnd_950430 433802149735841486181385 := by
  unfold tailWord_950430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333128743345238170764093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23110019964507936910741829 4333128743345238170764093)
  ·
    refine ⟨1624923278754464314036535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4333128743345238170764093 1624923278754464314036535)
    ·
      refine ⟨2437384918131696471054803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624923278754464314036535 2437384918131696471054803)
      ·
        refine ⟨3656077377197544706582205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437384918131696471054803 3656077377197544706582205)
        ·
          refine ⟨1371029016449079264968327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3656077377197544706582205 1371029016449079264968327)
          ·
            refine ⟨2056543524673618897452491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371029016449079264968327 2056543524673618897452491)
            ·
              refine ⟨3084815287010428346178737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056543524673618897452491 3084815287010428346178737)
              ·
                refine ⟨2313611465257821259634053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084815287010428346178737 2313611465257821259634053)
                ·
                  refine ⟨433802149735841486181385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313611465257821259634053 433802149735841486181385)
                  ·
                    rfl

theorem cell20_950430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_950430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950430 prefixEnd_950430 := by exact prefixLift 950430
  have htrace : WordTrace (prefixWord ++ tailWord_950430) baseStart_950430 baseEnd_950430 := by
    simpa [prefixWord, tailWord_950430, baseEnd_950430] using wordTrace_append hprefix tailTrace_950430
  have hstable : (prefixWord ++ tailWord_950430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950430).length < 2 ^ (prefixWord ++ tailWord_950430).sum := by decide
  have hdescent : baseEnd_950430 < baseStart_950430 := by decide
  rcases family_descends (prefixWord ++ tailWord_950430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950468 : List Nat := [2, 3, 3, 1, 2, 1, 2, 4, 2]
def baseStart_950468 : Nat := 118140960795 + 950468 * 2 ^ 59
def prefixEnd_950468 : Nat := 4983230072969 + 3 ^ 40 * 950468 * 2
def baseEnd_950468 : Nat := 433819493971282242914563

theorem tailTrace_950468 : CollatzResearch.WordTrace tailWord_950468 prefixEnd_950468 433819493971282242914563 := by
  unfold tailWord_950468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17333207960312118927998029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23110943947082825237330705 17333207960312118927998029)
  ·
    refine ⟨6499952985117044597999261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17333207960312118927998029 6499952985117044597999261)
    ·
      refine ⟨2437482369418891724249723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6499952985117044597999261 2437482369418891724249723)
      ·
        refine ⟨3656223554128337586374585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437482369418891724249723 3656223554128337586374585)
        ·
          refine ⟨2742167665596253189780939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656223554128337586374585 2742167665596253189780939)
          ·
            refine ⟨4113251498394379784671409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742167665596253189780939 4113251498394379784671409)
            ·
              refine ⟨3084938623795784838503557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113251498394379784671409 3084938623795784838503557)
              ·
                refine ⟨578425991961709657219417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3084938623795784838503557 578425991961709657219417)
                ·
                  refine ⟨433819493971282242914563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578425991961709657219417 433819493971282242914563)
                  ·
                    rfl

theorem cell20_950468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_950468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950468 prefixEnd_950468 := by exact prefixLift 950468
  have htrace : WordTrace (prefixWord ++ tailWord_950468) baseStart_950468 baseEnd_950468 := by
    simpa [prefixWord, tailWord_950468, baseEnd_950468] using wordTrace_append hprefix tailTrace_950468
  have hstable : (prefixWord ++ tailWord_950468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950468).length < 2 ^ (prefixWord ++ tailWord_950468).sum := by decide
  have hdescent : baseEnd_950468 < baseStart_950468 := by decide
  rcases family_descends (prefixWord ++ tailWord_950468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950498 : List Nat := [3, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_950498 : Nat := 118140960795 + 950498 * 2 ^ 59
def prefixEnd_950498 : Nat := 4983230072969 + 3 ^ 40 * 950498 * 2
def baseEnd_950498 : Nat := 433833186788735471914441

theorem tailTrace_950498 : CollatzResearch.WordTrace tailWord_950498 prefixEnd_950498 433833186788735471914441 := by
  unfold tailWord_950498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8666877527628888244897037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23111673407010368653058765 8666877527628888244897037)
  ·
    refine ⟨3250079072860833091836389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8666877527628888244897037 3250079072860833091836389)
    ·
      refine ⟨609389826161406204719323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3250079072860833091836389 609389826161406204719323)
      ·
        refine ⟨914084739242109307078985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609389826161406204719323 914084739242109307078985)
        ·
          refine ⟨685563554431581980309239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914084739242109307078985 685563554431581980309239)
          ·
            refine ⟨1028345331647372970463859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685563554431581980309239 1028345331647372970463859)
            ·
              refine ⟨1542517997471059455695789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028345331647372970463859 1542517997471059455695789)
              ·
                refine ⟨578444249051647295885921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1542517997471059455695789 578444249051647295885921)
                ·
                  refine ⟨433833186788735471914441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578444249051647295885921 433833186788735471914441)
                  ·
                    rfl

theorem cell20_950498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_950498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950498 prefixEnd_950498 := by exact prefixLift 950498
  have htrace : WordTrace (prefixWord ++ tailWord_950498) baseStart_950498 baseEnd_950498 := by
    simpa [prefixWord, tailWord_950498, baseEnd_950498] using wordTrace_append hprefix tailTrace_950498
  have hstable : (prefixWord ++ tailWord_950498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950498).length < 2 ^ (prefixWord ++ tailWord_950498).sum := by decide
  have hdescent : baseEnd_950498 < baseStart_950498 := by decide
  rcases family_descends (prefixWord ++ tailWord_950498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950503 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_950503 : Nat := 118140960795 + 950503 * 2 ^ 59
def prefixEnd_950503 : Nat := 4983230072969 + 3 ^ 40 * 950503 * 2
def baseEnd_950503 : Nat := 433835468924977676747753

theorem tailTrace_950503 : CollatzResearch.WordTrace tailWord_950503 prefixEnd_950503 433835468924977676747753 := by
  unfold tailWord_950503
  simp only [CollatzResearch.WordTrace]
  refine ⟨34667692475497438833520163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23111794983664959222346775 34667692475497438833520163)
  ·
    refine ⟨52001538713246158250280245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34667692475497438833520163 52001538713246158250280245)
    ·
      refine ⟨4875144254366827335963773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52001538713246158250280245 4875144254366827335963773)
      ·
        refine ⟨1828179095387560250986415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4875144254366827335963773 1828179095387560250986415)
        ·
          refine ⟨2742268643081340376479623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828179095387560250986415 2742268643081340376479623)
          ·
            refine ⟨4113402964622010564719435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742268643081340376479623 4113402964622010564719435)
            ·
              refine ⟨6170104446933015847079153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113402964622010564719435 6170104446933015847079153)
              ·
                refine ⟨4627578335199761885309365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170104446933015847079153 4627578335199761885309365)
                ·
                  refine ⟨433835468924977676747753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4627578335199761885309365 433835468924977676747753)
                  ·
                    rfl

theorem cell20_950503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_950503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950503 prefixEnd_950503 := by exact prefixLift 950503
  have htrace : WordTrace (prefixWord ++ tailWord_950503) baseStart_950503 baseEnd_950503 := by
    simpa [prefixWord, tailWord_950503, baseEnd_950503] using wordTrace_append hprefix tailTrace_950503
  have hstable : (prefixWord ++ tailWord_950503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950503).length < 2 ^ (prefixWord ++ tailWord_950503).sum := by decide
  have hdescent : baseEnd_950503 < baseStart_950503 := by decide
  rcases family_descends (prefixWord ++ tailWord_950503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950578 : List Nat := [3, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_950578 : Nat := 118140960795 + 950578 * 2 ^ 59
def prefixEnd_950578 : Nat := 4983230072969 + 3 ^ 40 * 950578 * 2
def baseEnd_950578 : Nat := 433869700968610749247447

theorem tailTrace_950578 : CollatzResearch.WordTrace tailWord_950578 prefixEnd_950578 433869700968610749247447 := by
  unfold tailWord_950578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8667606987556431660625097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23113618633483817761666925 8667606987556431660625097)
  ·
    refine ⟨6500705240667323745468823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8667606987556431660625097 6500705240667323745468823)
    ·
      refine ⟨9751057861000985618203235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6500705240667323745468823 9751057861000985618203235)
      ·
        refine ⟨14626586791501478427304853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751057861000985618203235 14626586791501478427304853)
        ·
          refine ⟨685621255851631801279915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14626586791501478427304853 685621255851631801279915)
          ·
            refine ⟨1028431883777447701919873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685621255851631801279915 1028431883777447701919873)
            ·
              refine ⟨771323912833085776439905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028431883777447701919873 771323912833085776439905)
              ·
                refine ⟨578492934624814332329929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771323912833085776439905 578492934624814332329929)
                ·
                  refine ⟨433869700968610749247447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578492934624814332329929 433869700968610749247447)
                  ·
                    rfl

theorem cell20_950578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_950578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950578 prefixEnd_950578 := by exact prefixLift 950578
  have htrace : WordTrace (prefixWord ++ tailWord_950578) baseStart_950578 baseEnd_950578 := by
    simpa [prefixWord, tailWord_950578, baseEnd_950578] using wordTrace_append hprefix tailTrace_950578
  have hstable : (prefixWord ++ tailWord_950578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950578).length < 2 ^ (prefixWord ++ tailWord_950578).sum := by decide
  have hdescent : baseEnd_950578 < baseStart_950578 := by decide
  rcases family_descends (prefixWord ++ tailWord_950578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950579 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 3]
def baseStart_950579 : Nat := 118140960795 + 950579 * 2 ^ 59
def prefixEnd_950579 : Nat := 4983230072969 + 3 ^ 40 * 950579 * 2
def baseEnd_950579 : Nat := 433870157395859190214109

theorem tailTrace_950579 : CollatzResearch.WordTrace tailWord_950579 prefixEnd_950579 433870157395859190214109 := by
  unfold tailWord_950579
  simp only [CollatzResearch.WordTrace]
  refine ⟨34670464423222103813286791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23113642948814735875524527 34670464423222103813286791)
  ·
    refine ⟨52005696634833155719930187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34670464423222103813286791 52005696634833155719930187)
    ·
      refine ⟨78008544952249733579895281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52005696634833155719930187 78008544952249733579895281)
      ·
        refine ⟨58506408714187300184921461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78008544952249733579895281 58506408714187300184921461)
        ·
          refine ⟨5484975816955059392336387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58506408714187300184921461 5484975816955059392336387)
          ·
            refine ⟨8227463725432589088504581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484975816955059392336387 8227463725432589088504581)
            ·
              refine ⟨1542649448518610454094609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8227463725432589088504581 1542649448518610454094609)
              ·
                refine ⟨1156987086388957840570957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542649448518610454094609 1156987086388957840570957)
                ·
                  refine ⟨433870157395859190214109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156987086388957840570957 433870157395859190214109)
                  ·
                    rfl

theorem cell20_950579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_950579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950579 prefixEnd_950579 := by exact prefixLift 950579
  have htrace : WordTrace (prefixWord ++ tailWord_950579) baseStart_950579 baseEnd_950579 := by
    simpa [prefixWord, tailWord_950579, baseEnd_950579] using wordTrace_append hprefix tailTrace_950579
  have hstable : (prefixWord ++ tailWord_950579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950579).length < 2 ^ (prefixWord ++ tailWord_950579).sum := by decide
  have hdescent : baseEnd_950579 < baseStart_950579 := by decide
  rcases family_descends (prefixWord ++ tailWord_950579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950631 : List Nat := [1, 1, 5, 1, 3, 2, 7]
def baseStart_950631 : Nat := 118140960795 + 950631 * 2 ^ 59
def prefixEnd_950631 : Nat := 4983230072969 + 3 ^ 40 * 950631 * 2
def baseEnd_950631 : Nat := 48210432401419791164507

theorem tailTrace_950631 : CollatzResearch.WordTrace tailWord_950631 prefixEnd_950631 48210432401419791164507 := by
  unfold tailWord_950631
  simp only [CollatzResearch.WordTrace]
  refine ⟨34672361019033716694179747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23114907346022477796119831 34672361019033716694179747)
  ·
    refine ⟨52008541528550575041269621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34672361019033716694179747 52008541528550575041269621)
    ·
      refine ⟨4875800768301616410119027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52008541528550575041269621 4875800768301616410119027)
      ·
        refine ⟨7313701152452424615178541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875800768301616410119027 7313701152452424615178541)
        ·
          refine ⟨2742637932169659230691953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7313701152452424615178541 2742637932169659230691953)
          ·
            refine ⟨2056978449127244423018965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742637932169659230691953 2056978449127244423018965)
            ·
              refine ⟨48210432401419791164507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2056978449127244423018965 48210432401419791164507)
              ·
                rfl

theorem cell20_950631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_950631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950631 prefixEnd_950631 := by exact prefixLift 950631
  have htrace : WordTrace (prefixWord ++ tailWord_950631) baseStart_950631 baseEnd_950631 := by
    simpa [prefixWord, tailWord_950631, baseEnd_950631] using wordTrace_append hprefix tailTrace_950631
  have hstable : (prefixWord ++ tailWord_950631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950631).length < 2 ^ (prefixWord ++ tailWord_950631).sum := by decide
  have hdescent : baseEnd_950631 < baseStart_950631 := by decide
  rcases family_descends (prefixWord ++ tailWord_950631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950634 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_950634 : Nat := 118140960795 + 950634 * 2 ^ 59
def prefixEnd_950634 : Nat := 4983230072969 + 3 ^ 40 * 950634 * 2
def baseEnd_950634 : Nat := 433895260894523443380551

theorem tailTrace_950634 : CollatzResearch.WordTrace tailWord_950634 prefixEnd_950634 433895260894523443380551 := by
  unfold tailWord_950634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668117609505712051634739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23114980292015232137692637 8668117609505712051634739)
  ·
    refine ⟨13002176414258568077452109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8668117609505712051634739 13002176414258568077452109)
    ·
      refine ⟨4875816155346963029044541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13002176414258568077452109 4875816155346963029044541)
      ·
        refine ⟨1828431058255111135891703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4875816155346963029044541 1828431058255111135891703)
        ·
          refine ⟨2742646587382666703837555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828431058255111135891703 2742646587382666703837555)
          ·
            refine ⟨4113969881074000055756333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742646587382666703837555 4113969881074000055756333)
            ·
              refine ⟨1542738705402750020908625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4113969881074000055756333 1542738705402750020908625)
              ·
                refine ⟨1157054029052062515681469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542738705402750020908625 1157054029052062515681469)
                ·
                  refine ⟨433895260894523443380551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157054029052062515681469 433895260894523443380551)
                  ·
                    rfl

theorem cell20_950634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_950634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950634 prefixEnd_950634 := by exact prefixLift 950634
  have htrace : WordTrace (prefixWord ++ tailWord_950634) baseStart_950634 baseEnd_950634 := by
    simpa [prefixWord, tailWord_950634, baseEnd_950634] using wordTrace_append hprefix tailTrace_950634
  have hstable : (prefixWord ++ tailWord_950634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950634).length < 2 ^ (prefixWord ++ tailWord_950634).sum := by decide
  have hdescent : baseEnd_950634 < baseStart_950634 := by decide
  rcases family_descends (prefixWord ++ tailWord_950634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950679 : List Nat := [1, 1, 3, 3, 1, 1, 5, 3, 2]
def baseStart_950679 : Nat := 118140960795 + 950679 * 2 ^ 59
def prefixEnd_950679 : Nat := 4983230072969 + 3 ^ 40 * 950679 * 2
def baseEnd_950679 : Nat := 433915800120703286880367

theorem tailTrace_950679 : CollatzResearch.WordTrace tailWord_950679 prefixEnd_950679 433915800120703286880367 := by
  unfold tailWord_950679
  simp only [CollatzResearch.WordTrace]
  refine ⟨34674111722859820891927091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23116074481906547261284727 34674111722859820891927091)
  ·
    refine ⟨52011167584289731337890637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34674111722859820891927091 52011167584289731337890637)
    ·
      refine ⟨19504187844108649251708989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52011167584289731337890637 19504187844108649251708989)
      ·
        refine ⟨7314070441540743469390871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19504187844108649251708989 7314070441540743469390871)
        ·
          refine ⟨10971105662311115204086307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7314070441540743469390871 10971105662311115204086307)
          ·
            refine ⟨16456658493466672806129461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10971105662311115204086307 16456658493466672806129461)
            ·
              refine ⟨1542811733762500575574637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16456658493466672806129461 1542811733762500575574637)
              ·
                refine ⟨578554400160937715840489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1542811733762500575574637 578554400160937715840489)
                ·
                  refine ⟨433915800120703286880367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578554400160937715840489 433915800120703286880367)
                  ·
                    rfl

theorem cell20_950679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 2].length) (baseStart_950679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950679 prefixEnd_950679 := by exact prefixLift 950679
  have htrace : WordTrace (prefixWord ++ tailWord_950679) baseStart_950679 baseEnd_950679 := by
    simpa [prefixWord, tailWord_950679, baseEnd_950679] using wordTrace_append hprefix tailTrace_950679
  have hstable : (prefixWord ++ tailWord_950679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950679).length < 2 ^ (prefixWord ++ tailWord_950679).sum := by decide
  have hdescent : baseEnd_950679 < baseStart_950679 := by decide
  rcases family_descends (prefixWord ++ tailWord_950679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950686 : List Nat := [4, 3, 1, 2, 1, 1, 8]
def baseStart_950686 : Nat := 118140960795 + 950686 * 2 ^ 59
def prefixEnd_950686 : Nat := 4983230072969 + 3 ^ 40 * 950686 * 2
def baseEnd_950686 : Nat := 48213221679049152627445

theorem tailTrace_950686 : CollatzResearch.WordTrace tailWord_950686 prefixEnd_950686 48213221679049152627445 := by
  unfold tailWord_950686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334295879229307635928989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23116244689222974058287941 4334295879229307635928989)
  ·
    refine ⟨1625360954710990363473371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4334295879229307635928989 1625360954710990363473371)
    ·
      refine ⟨2438041432066485545210057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625360954710990363473371 2438041432066485545210057)
      ·
        refine ⟨1828531074049864158907543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2438041432066485545210057 1828531074049864158907543)
        ·
          refine ⟨2742796611074796238361315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828531074049864158907543 2742796611074796238361315)
          ·
            refine ⟨4114194916612194357541973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742796611074796238361315 4114194916612194357541973)
            ·
              refine ⟨48213221679049152627445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4114194916612194357541973 48213221679049152627445)
              ·
                rfl

theorem cell20_950686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 8].length) (baseStart_950686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950686 prefixEnd_950686 := by exact prefixLift 950686
  have htrace : WordTrace (prefixWord ++ tailWord_950686) baseStart_950686 baseEnd_950686 := by
    simpa [prefixWord, tailWord_950686, baseEnd_950686] using wordTrace_append hprefix tailTrace_950686
  have hstable : (prefixWord ++ tailWord_950686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950686).length < 2 ^ (prefixWord ++ tailWord_950686).sum := by decide
  have hdescent : baseEnd_950686 < baseStart_950686 := by decide
  rcases family_descends (prefixWord ++ tailWord_950686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950696 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_950696 : Nat := 118140960795 + 950696 * 2 ^ 59
def prefixEnd_950696 : Nat := 4983230072969 + 3 ^ 40 * 950696 * 2
def baseEnd_950696 : Nat := 433923559383926783313631

theorem tailTrace_950696 : CollatzResearch.WordTrace tailWord_950696 prefixEnd_950696 433923559383926783313631 := by
  unfold tailWord_950696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17337365881899116397647971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23116487842532155196863961 17337365881899116397647971)
  ·
    refine ⟨26006048822848674596471957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17337365881899116397647971 26006048822848674596471957)
    ·
      refine ⟨1219033538571031621709623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26006048822848674596471957 1219033538571031621709623)
      ·
        refine ⟨1828550307856547432564435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219033538571031621709623 1828550307856547432564435)
        ·
          refine ⟨2742825461784821148846653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828550307856547432564435 2742825461784821148846653)
          ·
            refine ⟨1028559548169307930817495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2742825461784821148846653 1028559548169307930817495)
            ·
              refine ⟨1542839322253961896226243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028559548169307930817495 1542839322253961896226243)
              ·
                refine ⟨2314258983380942844339365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542839322253961896226243 2314258983380942844339365)
                ·
                  refine ⟨433923559383926783313631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314258983380942844339365 433923559383926783313631)
                  ·
                    rfl

theorem cell20_950696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_950696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950696 prefixEnd_950696 := by exact prefixLift 950696
  have htrace : WordTrace (prefixWord ++ tailWord_950696) baseStart_950696 baseEnd_950696 := by
    simpa [prefixWord, tailWord_950696, baseEnd_950696] using wordTrace_append hprefix tailTrace_950696
  have hstable : (prefixWord ++ tailWord_950696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950696).length < 2 ^ (prefixWord ++ tailWord_950696).sum := by decide
  have hdescent : baseEnd_950696 < baseStart_950696 := by decide
  rcases family_descends (prefixWord ++ tailWord_950696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950762 : List Nat := [3, 1, 3, 1, 3, 3, 1, 5]
def baseStart_950762 : Nat := 118140960795 + 950762 * 2 ^ 59
def prefixEnd_950762 : Nat := 4983230072969 + 3 ^ 40 * 950762 * 2
def baseEnd_950762 : Nat := 144651227860774629037787

theorem tailTrace_950762 : CollatzResearch.WordTrace tailWord_950762 prefixEnd_950762 144651227860774629037787 := by
  unfold tailWord_950762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669284745389781516799635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23118092654372750711465693 8669284745389781516799635)
  ·
    refine ⟨13003927118084672275199453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8669284745389781516799635 13003927118084672275199453)
    ·
      refine ⟨4876472669281752103199795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13003927118084672275199453 4876472669281752103199795)
      ·
        refine ⟨7314709003922628154799693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4876472669281752103199795 7314709003922628154799693)
        ·
          refine ⟨2743015876470985558049885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7314709003922628154799693 2743015876470985558049885)
          ·
            refine ⟨1028630953676619584268707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2743015876470985558049885 1028630953676619584268707)
            ·
              refine ⟨1542946430514929376403061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028630953676619584268707 1542946430514929376403061)
              ·
                refine ⟨144651227860774629037787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1542946430514929376403061 144651227860774629037787)
                ·
                  rfl

theorem cell20_950762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_950762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950762 prefixEnd_950762 := by exact prefixLift 950762
  have htrace : WordTrace (prefixWord ++ tailWord_950762) baseStart_950762 baseEnd_950762 := by
    simpa [prefixWord, tailWord_950762, baseEnd_950762] using wordTrace_append hprefix tailTrace_950762
  have hstable : (prefixWord ++ tailWord_950762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950762).length < 2 ^ (prefixWord ++ tailWord_950762).sum := by decide
  have hdescent : baseEnd_950762 < baseStart_950762 := by decide
  rcases family_descends (prefixWord ++ tailWord_950762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950783 : List Nat := [1, 1, 2, 2, 1, 2, 7, 4]
def baseStart_950783 : Nat := 118140960795 + 950783 * 2 ^ 59
def prefixEnd_950783 : Nat := 4983230072969 + 3 ^ 40 * 950783 * 2
def baseEnd_950783 : Nat := 144654422851513715804425

theorem tailTrace_950783 : CollatzResearch.WordTrace tailWord_950783 prefixEnd_950783 144654422851513715804425 := by
  unfold tailWord_950783
  simp only [CollatzResearch.WordTrace]
  refine ⟨34677904914483046653713003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23118603276322031102475335 34677904914483046653713003)
  ·
    refine ⟨52016857371724569980569505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34677904914483046653713003 52016857371724569980569505)
    ·
      refine ⟨39012643028793427485427129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52016857371724569980569505 39012643028793427485427129)
      ·
        refine ⟨29259482271595070614070347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39012643028793427485427129 29259482271595070614070347)
        ·
          refine ⟨43889223407392605921105521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29259482271595070614070347 43889223407392605921105521)
          ·
            refine ⟨32916917555544454440829141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43889223407392605921105521 32916917555544454440829141)
            ·
              refine ⟨771490255208073150956933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32916917555544454440829141 771490255208073150956933)
              ·
                refine ⟨144654422851513715804425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 771490255208073150956933 144654422851513715804425)
                ·
                  rfl

theorem cell20_950783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_950783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950783 prefixEnd_950783 := by exact prefixLift 950783
  have htrace : WordTrace (prefixWord ++ tailWord_950783) baseStart_950783 baseEnd_950783 := by
    simpa [prefixWord, tailWord_950783, baseEnd_950783] using wordTrace_append hprefix tailTrace_950783
  have hstable : (prefixWord ++ tailWord_950783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950783).length < 2 ^ (prefixWord ++ tailWord_950783).sum := by decide
  have hdescent : baseEnd_950783 < baseStart_950783 := by decide
  rcases family_descends (prefixWord ++ tailWord_950783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950828 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_950828 : Nat := 118140960795 + 950828 * 2 ^ 59
def prefixEnd_950828 : Nat := 4983230072969 + 3 ^ 40 * 950828 * 2
def baseEnd_950828 : Nat := 433983807780720990913091

theorem tailTrace_950828 : CollatzResearch.WordTrace tailWord_950828 prefixEnd_950828 433983807780720990913091 := by
  unfold tailWord_950828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17339773099660009669550569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23119697466213346226067425 17339773099660009669550569)
  ·
    refine ⟨13004829824745007252162927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17339773099660009669550569 13004829824745007252162927)
    ·
      refine ⟨19507244737117510878244391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13004829824745007252162927 19507244737117510878244391)
      ·
        refine ⟨29260867105676266317366587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19507244737117510878244391 29260867105676266317366587)
        ·
          refine ⟨43891300658514399476049881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29260867105676266317366587 43891300658514399476049881)
          ·
            refine ⟨32918475493885799607037411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43891300658514399476049881 32918475493885799607037411)
            ·
              refine ⟨49377713240828699410556117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32918475493885799607037411 49377713240828699410556117)
              ·
                refine ⟨1157290154081922642434909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49377713240828699410556117 1157290154081922642434909)
                ·
                  refine ⟨433983807780720990913091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157290154081922642434909 433983807780720990913091)
                  ·
                    rfl

theorem cell20_950828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_950828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950828 prefixEnd_950828 := by exact prefixLift 950828
  have htrace : WordTrace (prefixWord ++ tailWord_950828) baseStart_950828 baseEnd_950828 := by
    simpa [prefixWord, tailWord_950828, baseEnd_950828] using wordTrace_append hprefix tailTrace_950828
  have hstable : (prefixWord ++ tailWord_950828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950828).length < 2 ^ (prefixWord ++ tailWord_950828).sum := by decide
  have hdescent : baseEnd_950828 < baseStart_950828 := by decide
  rcases family_descends (prefixWord ++ tailWord_950828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950835 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_950835 : Nat := 118140960795 + 950835 * 2 ^ 59
def prefixEnd_950835 : Nat := 4983230072969 + 3 ^ 40 * 950835 * 2
def baseEnd_950835 : Nat := 433987002771460077679729

theorem tailTrace_950835 : CollatzResearch.WordTrace tailWord_950835 prefixEnd_950835 433987002771460077679729 := by
  unfold tailWord_950835
  simp only [CollatzResearch.WordTrace]
  refine ⟨34679801510294659534605959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23119867673529773023070639 34679801510294659534605959)
  ·
    refine ⟨52019702265441989301908939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34679801510294659534605959 52019702265441989301908939)
    ·
      refine ⟨78029553398162983952863409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52019702265441989301908939 78029553398162983952863409)
      ·
        refine ⟨58522165048622237964647557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78029553398162983952863409 58522165048622237964647557)
        ·
          refine ⟨10972905946616669618371417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58522165048622237964647557 10972905946616669618371417)
          ·
            refine ⟨8229679459962502213778563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10972905946616669618371417 8229679459962502213778563)
            ·
              refine ⟨12344519189943753320667845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229679459962502213778563 12344519189943753320667845)
              ·
                refine ⟨2314597348114453747625221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12344519189943753320667845 2314597348114453747625221)
                ·
                  refine ⟨433987002771460077679729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314597348114453747625221 433987002771460077679729)
                  ·
                    rfl

theorem cell20_950835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_950835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950835 prefixEnd_950835 := by exact prefixLift 950835
  have htrace : WordTrace (prefixWord ++ tailWord_950835) baseStart_950835 baseEnd_950835 := by
    simpa [prefixWord, tailWord_950835, baseEnd_950835] using wordTrace_append hprefix tailTrace_950835
  have hstable : (prefixWord ++ tailWord_950835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950835).length < 2 ^ (prefixWord ++ tailWord_950835).sum := by decide
  have hdescent : baseEnd_950835 < baseStart_950835 := by decide
  rcases family_descends (prefixWord ++ tailWord_950835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950838 : List Nat := [5, 1, 2, 1, 2, 2, 1, 6]
def baseStart_950838 : Nat := 118140960795 + 950838 * 2 ^ 59
def prefixEnd_950838 : Nat := 4983230072969 + 3 ^ 40 * 950838 * 2
def baseEnd_950838 : Nat := 144662790684401800193239

theorem tailTrace_950838 : CollatzResearch.WordTrace tailWord_950838 prefixEnd_950838 144662790684401800193239 := by
  unfold tailWord_950838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2167494433080236940435323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23119940619522527364643445 2167494433080236940435323)
  ·
    refine ⟨3251241649620355410652985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2167494433080236940435323 3251241649620355410652985)
    ·
      refine ⟨2438431237215266557989739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3251241649620355410652985 2438431237215266557989739)
      ·
        refine ⟨3657646855822899836984609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438431237215266557989739 3657646855822899836984609)
        ·
          refine ⟨2743235141867174877738457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3657646855822899836984609 2743235141867174877738457)
          ·
            refine ⟨2057426356400381158303843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2743235141867174877738457 2057426356400381158303843)
            ·
              refine ⟨3086139534600571737455765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057426356400381158303843 3086139534600571737455765)
              ·
                refine ⟨144662790684401800193239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3086139534600571737455765 144662790684401800193239)
                ·
                  rfl

theorem cell20_950838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_950838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950838 prefixEnd_950838 := by exact prefixLift 950838
  have htrace : WordTrace (prefixWord ++ tailWord_950838) baseStart_950838 baseEnd_950838 := by
    simpa [prefixWord, tailWord_950838, baseEnd_950838] using wordTrace_append hprefix tailTrace_950838
  have hstable : (prefixWord ++ tailWord_950838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950838).length < 2 ^ (prefixWord ++ tailWord_950838).sum := by decide
  have hdescent : baseEnd_950838 < baseStart_950838 := by decide
  rcases family_descends (prefixWord ++ tailWord_950838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950866 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_950866 : Nat := 118140960795 + 950866 * 2 ^ 59
def prefixEnd_950866 : Nat := 4983230072969 + 3 ^ 40 * 950866 * 2
def baseEnd_950866 : Nat := 434001152016161747646269

theorem tailTrace_950866 : CollatzResearch.WordTrace tailWord_950866 prefixEnd_950866 434001152016161747646269 := by
  unfold tailWord_950866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670233043295587957246113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23120621448788234552656301 8670233043295587957246113)
  ·
    refine ⟨6502674782471690967934585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8670233043295587957246113 6502674782471690967934585)
    ·
      refine ⟨4877006086853768225950939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6502674782471690967934585 4877006086853768225950939)
      ·
        refine ⟨7315509130280652338926409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4877006086853768225950939 7315509130280652338926409)
        ·
          refine ⟨5486631847710489254194807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7315509130280652338926409 5486631847710489254194807)
          ·
            refine ⟨8229947771565733881292211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486631847710489254194807 8229947771565733881292211)
            ·
              refine ⟨12344921657348600821938317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229947771565733881292211 12344921657348600821938317)
              ·
                refine ⟨4629345621505725308226869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12344921657348600821938317 4629345621505725308226869)
                ·
                  refine ⟨434001152016161747646269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4629345621505725308226869 434001152016161747646269)
                  ·
                    rfl

theorem cell20_950866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_950866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950866 prefixEnd_950866 := by exact prefixLift 950866
  have htrace : WordTrace (prefixWord ++ tailWord_950866) baseStart_950866 baseEnd_950866 := by
    simpa [prefixWord, tailWord_950866, baseEnd_950866] using wordTrace_append hprefix tailTrace_950866
  have hstable : (prefixWord ++ tailWord_950866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950866).length < 2 ^ (prefixWord ++ tailWord_950866).sum := by decide
  have hdescent : baseEnd_950866 < baseStart_950866 := by decide
  rcases family_descends (prefixWord ++ tailWord_950866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950876 : List Nat := [2, 2, 4, 1, 3, 1, 2, 5]
def baseStart_950876 : Nat := 118140960795 + 950876 * 2 ^ 59
def prefixEnd_950876 : Nat := 4983230072969 + 3 ^ 40 * 950876 * 2
def baseEnd_950876 : Nat := 144668572096215385770965

theorem tailTrace_950876 : CollatzResearch.WordTrace tailWord_950876 prefixEnd_950876 144668572096215385770965 := by
  unfold tailWord_950876
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340648451573061768424241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23120864602097415691232321 17340648451573061768424241)
  ·
    refine ⟨13005486338679796326318181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17340648451573061768424241 13005486338679796326318181)
    ·
      refine ⟨2438528688502461811184659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13005486338679796326318181 2438528688502461811184659)
      ·
        refine ⟨3657793032753692716776989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438528688502461811184659 3657793032753692716776989)
        ·
          refine ⟨1371672387282634768791371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3657793032753692716776989 1371672387282634768791371)
          ·
            refine ⟨2057508580923952153187057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371672387282634768791371 2057508580923952153187057)
            ·
              refine ⟨1543131435692964114890293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057508580923952153187057 1543131435692964114890293)
              ·
                refine ⟨144668572096215385770965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1543131435692964114890293 144668572096215385770965)
                ·
                  rfl

theorem cell20_950876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_950876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950876 prefixEnd_950876 := by exact prefixLift 950876
  have htrace : WordTrace (prefixWord ++ tailWord_950876) baseStart_950876 baseEnd_950876 := by
    simpa [prefixWord, tailWord_950876, baseEnd_950876] using wordTrace_append hprefix tailTrace_950876
  have hstable : (prefixWord ++ tailWord_950876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950876).length < 2 ^ (prefixWord ++ tailWord_950876).sum := by decide
  have hdescent : baseEnd_950876 < baseStart_950876 := by decide
  rcases family_descends (prefixWord ++ tailWord_950876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950880 : List Nat := [2, 1, 1, 3, 2, 1, 3, 7]
def baseStart_950880 : Nat := 118140960795 + 950880 * 2 ^ 59
def prefixEnd_950880 : Nat := 4983230072969 + 3 ^ 40 * 950880 * 2
def baseEnd_950880 : Nat := 144669180665879973726515

theorem tailTrace_950880 : CollatzResearch.WordTrace tailWord_950880 prefixEnd_950880 144669180665879973726515 := by
  unfold tailWord_950880
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340721397565816109997047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23120961863421088146662729 17340721397565816109997047)
  ·
    refine ⟨26011082096348724164995571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17340721397565816109997047 26011082096348724164995571)
    ·
      refine ⟨39016623144523086247493357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26011082096348724164995571 39016623144523086247493357)
      ·
        refine ⟨14631233679196157342810009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39016623144523086247493357 14631233679196157342810009)
        ·
          refine ⟨10973425259397118007107507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14631233679196157342810009 10973425259397118007107507)
          ·
            refine ⟨16460137889095677010661261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10973425259397118007107507 16460137889095677010661261)
            ·
              refine ⟨6172551708410878878997973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16460137889095677010661261 6172551708410878878997973)
              ·
                refine ⟨144669180665879973726515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6172551708410878878997973 144669180665879973726515)
                ·
                  rfl

theorem cell20_950880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_950880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_950880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_950880 prefixEnd_950880 := by exact prefixLift 950880
  have htrace : WordTrace (prefixWord ++ tailWord_950880) baseStart_950880 baseEnd_950880 := by
    simpa [prefixWord, tailWord_950880, baseEnd_950880] using wordTrace_append hprefix tailTrace_950880
  have hstable : (prefixWord ++ tailWord_950880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950880).length < 2 ^ (prefixWord ++ tailWord_950880).sum := by decide
  have hdescent : baseEnd_950880 < baseStart_950880 := by decide
  rcases family_descends (prefixWord ++ tailWord_950880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951011 : List Nat := [1, 1, 1, 7, 1, 2, 1, 6]
def baseStart_951011 : Nat := 118140960795 + 951011 * 2 ^ 59
def prefixEnd_951011 : Nat := 4983230072969 + 3 ^ 40 * 951011 * 2
def baseEnd_951011 : Nat := 144689111322395229270781

theorem tailTrace_951011 : CollatzResearch.WordTrace tailWord_951011 prefixEnd_951011 144689111322395229270781 := by
  unfold tailWord_951011
  simp only [CollatzResearch.WordTrace]
  refine ⟨34686220757657041593012887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23124147171771361062008591 34686220757657041593012887)
  ·
    refine ⟨52029331136485562389519331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34686220757657041593012887 52029331136485562389519331)
    ·
      refine ⟨78043996704728343584278997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52029331136485562389519331 78043996704728343584278997)
      ·
        refine ⟨1829156172767070552756539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78043996704728343584278997 1829156172767070552756539)
        ·
          refine ⟨2743734259150605829134809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829156172767070552756539 2743734259150605829134809)
          ·
            refine ⟨2057800694362954371851107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2743734259150605829134809 2057800694362954371851107)
            ·
              refine ⟨3086701041544431557776661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057800694362954371851107 3086701041544431557776661)
              ·
                refine ⟨144689111322395229270781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3086701041544431557776661 144689111322395229270781)
                ·
                  rfl

theorem cell20_951011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_951011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951011 prefixEnd_951011 := by exact prefixLift 951011
  have htrace : WordTrace (prefixWord ++ tailWord_951011) baseStart_951011 baseEnd_951011 := by
    simpa [prefixWord, tailWord_951011, baseEnd_951011] using wordTrace_append hprefix tailTrace_951011
  have hstable : (prefixWord ++ tailWord_951011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951011).length < 2 ^ (prefixWord ++ tailWord_951011).sum := by decide
  have hdescent : baseEnd_951011 < baseStart_951011 := by decide
  rcases family_descends (prefixWord ++ tailWord_951011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951125 : List Nat := [1, 3, 2, 2, 2, 1, 5, 4]
def baseStart_951125 : Nat := 118140960795 + 951125 * 2 ^ 59
def prefixEnd_951125 : Nat := 4983230072969 + 3 ^ 40 * 951125 * 2
def baseEnd_951125 : Nat := 144706455557835986003959

theorem tailTrace_951125 : CollatzResearch.WordTrace tailWord_951125 prefixEnd_951125 144706455557835986003959 := by
  unfold tailWord_951125
  simp only [CollatzResearch.WordTrace]
  refine ⟨34690378679244039062662829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23126919119496026041775219 34690378679244039062662829)
  ·
    refine ⟨13008892004716514648498561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34690378679244039062662829 13008892004716514648498561)
    ·
      refine ⟨9756669003537385986373921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13008892004716514648498561 9756669003537385986373921)
      ·
        refine ⟨7317501752653039489780441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9756669003537385986373921 7317501752653039489780441)
        ·
          refine ⟨5488126314489779617335331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7317501752653039489780441 5488126314489779617335331)
          ·
            refine ⟨8232189471734669426002997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488126314489779617335331 8232189471734669426002997)
            ·
              refine ⟨771767762975125258687781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8232189471734669426002997 771767762975125258687781)
              ·
                refine ⟨144706455557835986003959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 771767762975125258687781 144706455557835986003959)
                ·
                  rfl

theorem cell20_951125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_951125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951125 prefixEnd_951125 := by exact prefixLift 951125
  have htrace : WordTrace (prefixWord ++ tailWord_951125) baseStart_951125 baseEnd_951125 := by
    simpa [prefixWord, tailWord_951125, baseEnd_951125] using wordTrace_append hprefix tailTrace_951125
  have hstable : (prefixWord ++ tailWord_951125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951125).length < 2 ^ (prefixWord ++ tailWord_951125).sum := by decide
  have hdescent : baseEnd_951125 < baseStart_951125 := by decide
  rcases family_descends (prefixWord ++ tailWord_951125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951177 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_951177 : Nat := 118140960795 + 951177 * 2 ^ 59
def prefixEnd_951177 : Nat := 4983230072969 + 3 ^ 40 * 951177 * 2
def baseEnd_951177 : Nat := 434143100890426888278331

theorem tailTrace_951177 : CollatzResearch.WordTrace tailWord_951177 prefixEnd_951177 434143100890426888278331 := by
  unfold tailWord_951177
  simp only [CollatzResearch.WordTrace]
  refine ⟨34692275275055651943555785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23128183516703767962370523 34692275275055651943555785)
  ·
    refine ⟨26019206456291738957666839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34692275275055651943555785 26019206456291738957666839)
    ·
      refine ⟨39028809684437608436500259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26019206456291738957666839 39028809684437608436500259)
      ·
        refine ⟨58543214526656412654750389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39028809684437608436500259 58543214526656412654750389)
        ·
          refine ⟨5488426361874038686382849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58543214526656412654750389 5488426361874038686382849)
          ·
            refine ⟨4116319771405529014787137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488426361874038686382849 4116319771405529014787137)
            ·
              refine ⟨3087239828554146761090353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116319771405529014787137 3087239828554146761090353)
              ·
                refine ⟨2315429871415610070817765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087239828554146761090353 2315429871415610070817765)
                ·
                  refine ⟨434143100890426888278331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315429871415610070817765 434143100890426888278331)
                  ·
                    rfl

theorem cell20_951177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_951177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951177 prefixEnd_951177 := by exact prefixLift 951177
  have htrace : WordTrace (prefixWord ++ tailWord_951177) baseStart_951177 baseEnd_951177 := by
    simpa [prefixWord, tailWord_951177, baseEnd_951177] using wordTrace_append hprefix tailTrace_951177
  have hstable : (prefixWord ++ tailWord_951177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951177).length < 2 ^ (prefixWord ++ tailWord_951177).sum := by decide
  have hdescent : baseEnd_951177 < baseStart_951177 := by decide
  rcases family_descends (prefixWord ++ tailWord_951177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951191 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_951191 : Nat := 118140960795 + 951191 * 2 ^ 59
def prefixEnd_951191 : Nat := 4983230072969 + 3 ^ 40 * 951191 * 2
def baseEnd_951191 : Nat := 434149490871905061811607

theorem tailTrace_951191 : CollatzResearch.WordTrace tailWord_951191 prefixEnd_951191 434149490871905061811607 := by
  unfold tailWord_951191
  simp only [CollatzResearch.WordTrace]
  refine ⟨34692785897004932334565427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23128523931336621556376951 34692785897004932334565427)
  ·
    refine ⟨52039178845507398501848141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34692785897004932334565427 52039178845507398501848141)
    ·
      refine ⟨19514692067065274438193053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52039178845507398501848141 19514692067065274438193053)
      ·
        refine ⟨7318009525149477914322395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19514692067065274438193053 7318009525149477914322395)
        ·
          refine ⟨10977014287724216871483593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318009525149477914322395 10977014287724216871483593)
          ·
            refine ⟨8232760715793162653612695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10977014287724216871483593 8232760715793162653612695)
            ·
              refine ⟨12349141073689743980419043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232760715793162653612695 12349141073689743980419043)
              ·
                refine ⟨18523711610534615970628565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12349141073689743980419043 18523711610534615970628565)
                ·
                  refine ⟨434149490871905061811607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18523711610534615970628565 434149490871905061811607)
                  ·
                    rfl

theorem cell20_951191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_951191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951191 prefixEnd_951191 := by exact prefixLift 951191
  have htrace : WordTrace (prefixWord ++ tailWord_951191) baseStart_951191 baseEnd_951191 := by
    simpa [prefixWord, tailWord_951191, baseEnd_951191] using wordTrace_append hprefix tailTrace_951191
  have hstable : (prefixWord ++ tailWord_951191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951191).length < 2 ^ (prefixWord ++ tailWord_951191).sum := by decide
  have hdescent : baseEnd_951191 < baseStart_951191 := by decide
  rcases family_descends (prefixWord ++ tailWord_951191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951201 : List Nat := [1, 2, 3, 4, 1, 3, 6]
def baseStart_951201 : Nat := 118140960795 + 951201 * 2 ^ 59
def prefixEnd_951201 : Nat := 4983230072969 + 3 ^ 40 * 951201 * 2
def baseEnd_951201 : Nat := 48239339460487719053137

theorem tailTrace_951201 : CollatzResearch.WordTrace tailWord_951201 prefixEnd_951201 48239339460487719053137 := by
  unfold tailWord_951201
  simp only [CollatzResearch.WordTrace]
  refine ⟨34693150626968704042429457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23128767084645802694952971 34693150626968704042429457)
  ·
    refine ⟨26019862970226528031822093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34693150626968704042429457 26019862970226528031822093)
    ·
      refine ⟨9757448613834948011933285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26019862970226528031822093 9757448613834948011933285)
      ·
        refine ⟨1829521615094052752237491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9757448613834948011933285 1829521615094052752237491)
        ·
          refine ⟨2744282422641079128356237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829521615094052752237491 2744282422641079128356237)
          ·
            refine ⟨1029105908490404673133589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2744282422641079128356237 1029105908490404673133589)
            ·
              refine ⟨48239339460487719053137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1029105908490404673133589 48239339460487719053137)
              ·
                rfl

theorem cell20_951201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 6].length) (baseStart_951201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951201 prefixEnd_951201 := by exact prefixLift 951201
  have htrace : WordTrace (prefixWord ++ tailWord_951201) baseStart_951201 baseEnd_951201 := by
    simpa [prefixWord, tailWord_951201, baseEnd_951201] using wordTrace_append hprefix tailTrace_951201
  have hstable : (prefixWord ++ tailWord_951201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951201).length < 2 ^ (prefixWord ++ tailWord_951201).sum := by decide
  have hdescent : baseEnd_951201 < baseStart_951201 := by decide
  rcases family_descends (prefixWord ++ tailWord_951201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951225 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 3]
def baseStart_951225 : Nat := 118140960795 + 951225 * 2 ^ 59
def prefixEnd_951225 : Nat := 4983230072969 + 3 ^ 40 * 951225 * 2
def baseEnd_951225 : Nat := 434165009398352054678135

theorem tailTrace_951225 : CollatzResearch.WordTrace tailWord_951225 prefixEnd_951225 434165009398352054678135 := by
  unfold tailWord_951225
  simp only [CollatzResearch.WordTrace]
  refine ⟨34694025978881756141303129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23129350652587837427535419 34694025978881756141303129)
  ·
    refine ⟨26020519484161317105977347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34694025978881756141303129 26020519484161317105977347)
    ·
      refine ⟨39030779226241975658966021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26020519484161317105977347 39030779226241975658966021)
      ·
        refine ⟨7318271104920370436056129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39030779226241975658966021 7318271104920370436056129)
        ·
          refine ⟨5488703328690277827042097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7318271104920370436056129 5488703328690277827042097)
          ·
            refine ⟨4116527496517708370281573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488703328690277827042097 4116527496517708370281573)
            ·
              refine ⟨771848905597070319427795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4116527496517708370281573 771848905597070319427795)
              ·
                refine ⟨1157773358395605479141693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771848905597070319427795 1157773358395605479141693)
                ·
                  refine ⟨434165009398352054678135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157773358395605479141693 434165009398352054678135)
                  ·
                    rfl

theorem cell20_951225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_951225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951225 prefixEnd_951225 := by exact prefixLift 951225
  have htrace : WordTrace (prefixWord ++ tailWord_951225) baseStart_951225 baseEnd_951225 := by
    simpa [prefixWord, tailWord_951225, baseEnd_951225] using wordTrace_append hprefix tailTrace_951225
  have hstable : (prefixWord ++ tailWord_951225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951225).length < 2 ^ (prefixWord ++ tailWord_951225).sum := by decide
  have hdescent : baseEnd_951225 < baseStart_951225 := by decide
  rcases family_descends (prefixWord ++ tailWord_951225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951263 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 3]
def baseStart_951263 : Nat := 118140960795 + 951263 * 2 ^ 59
def prefixEnd_951263 : Nat := 4983230072969 + 3 ^ 40 * 951263 * 2
def baseEnd_951263 : Nat := 434182353633792811411313

theorem tailTrace_951263 : CollatzResearch.WordTrace tailWord_951263 prefixEnd_951263 434182353633792811411313 := by
  unfold tailWord_951263
  simp only [CollatzResearch.WordTrace]
  refine ⟨34695411952744088631186443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23130274635162725754124295 34695411952744088631186443)
  ·
    refine ⟨52043117929116132946779665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34695411952744088631186443 52043117929116132946779665)
    ·
      refine ⟨39032338446837099710084749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52043117929116132946779665 39032338446837099710084749)
      ·
        refine ⟨14637126917563912391281781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39032338446837099710084749 14637126917563912391281781)
        ·
          refine ⟨1372230648521616786682667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14637126917563912391281781 1372230648521616786682667)
          ·
            refine ⟨2058345972782425180024001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372230648521616786682667 2058345972782425180024001)
            ·
              refine ⟨1543759479586818885018001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058345972782425180024001 1543759479586818885018001)
              ·
                refine ⟨1157819609690114163763501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543759479586818885018001 1157819609690114163763501)
                ·
                  refine ⟨434182353633792811411313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157819609690114163763501 434182353633792811411313)
                  ·
                    rfl

theorem cell20_951263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_951263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951263 prefixEnd_951263 := by exact prefixLift 951263
  have htrace : WordTrace (prefixWord ++ tailWord_951263) baseStart_951263 baseEnd_951263 := by
    simpa [prefixWord, tailWord_951263, baseEnd_951263] using wordTrace_append hprefix tailTrace_951263
  have hstable : (prefixWord ++ tailWord_951263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951263).length < 2 ^ (prefixWord ++ tailWord_951263).sum := by decide
  have hdescent : baseEnd_951263 < baseStart_951263 := by decide
  rcases family_descends (prefixWord ++ tailWord_951263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951266 : List Nat := [3, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_951266 : Nat := 118140960795 + 951266 * 2 ^ 59
def prefixEnd_951266 : Nat := 4983230072969 + 3 ^ 40 * 951266 * 2
def baseEnd_951266 : Nat := 434183722915538134311301

theorem tailTrace_951266 : CollatzResearch.WordTrace tailWord_951266 prefixEnd_951266 434183722915538134311301 := by
  unfold tailWord_951266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673880342933305035886413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23130347581155480095697101 8673880342933305035886413)
  ·
    refine ⟨3252705128599989388457405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8673880342933305035886413 3252705128599989388457405)
    ·
      refine ⟨1219764423224996020671527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3252705128599989388457405 1219764423224996020671527)
      ·
        refine ⟨1829646634837494031007291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219764423224996020671527 1829646634837494031007291)
        ·
          refine ⟨2744469952256241046510937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829646634837494031007291 2744469952256241046510937)
          ·
            refine ⟨2058352464192180784883203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744469952256241046510937 2058352464192180784883203)
            ·
              refine ⟨3087528696288271177324805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058352464192180784883203 3087528696288271177324805)
              ·
                refine ⟨578911630554050845748401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3087528696288271177324805 578911630554050845748401)
                ·
                  refine ⟨434183722915538134311301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578911630554050845748401 434183722915538134311301)
                  ·
                    rfl

theorem cell20_951266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_951266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951266 prefixEnd_951266 := by exact prefixLift 951266
  have htrace : WordTrace (prefixWord ++ tailWord_951266) baseStart_951266 baseEnd_951266 := by
    simpa [prefixWord, tailWord_951266, baseEnd_951266] using wordTrace_append hprefix tailTrace_951266
  have hstable : (prefixWord ++ tailWord_951266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951266).length < 2 ^ (prefixWord ++ tailWord_951266).sum := by decide
  have hdescent : baseEnd_951266 < baseStart_951266 := by decide
  rcases family_descends (prefixWord ++ tailWord_951266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951308 : List Nat := [2, 2, 1, 2, 3, 2, 1, 5, 2]
def baseStart_951308 : Nat := 118140960795 + 951308 * 2 ^ 59
def prefixEnd_951308 : Nat := 4983230072969 + 3 ^ 40 * 951308 * 2
def baseEnd_951308 : Nat := 434202892859972654911129

theorem tailTrace_951308 : CollatzResearch.WordTrace tailWord_951308 prefixEnd_951308 434202892859972654911129 := by
  unfold tailWord_951308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17348526618790530658287289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23131368825054040877716385 17348526618790530658287289)
  ·
    refine ⟨13011394964092897993715467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17348526618790530658287289 13011394964092897993715467)
    ·
      refine ⟨19517092446139346990573201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13011394964092897993715467 19517092446139346990573201)
      ·
        refine ⟨14637819334604510242929901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19517092446139346990573201 14637819334604510242929901)
        ·
          refine ⟨5489182250476691341098713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14637819334604510242929901 5489182250476691341098713)
          ·
            refine ⟨4116886687857518505824035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5489182250476691341098713 4116886687857518505824035)
            ·
              refine ⟨6175330031786277758736053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116886687857518505824035 6175330031786277758736053)
              ·
                refine ⟨578937190479963539881505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6175330031786277758736053 578937190479963539881505)
                ·
                  refine ⟨434202892859972654911129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578937190479963539881505 434202892859972654911129)
                  ·
                    rfl

theorem cell20_951308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_951308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951308 prefixEnd_951308 := by exact prefixLift 951308
  have htrace : WordTrace (prefixWord ++ tailWord_951308) baseStart_951308 baseEnd_951308 := by
    simpa [prefixWord, tailWord_951308, baseEnd_951308] using wordTrace_append hprefix tailTrace_951308
  have hstable : (prefixWord ++ tailWord_951308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951308).length < 2 ^ (prefixWord ++ tailWord_951308).sum := by decide
  have hdescent : baseEnd_951308 < baseStart_951308 := by decide
  rcases family_descends (prefixWord ++ tailWord_951308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951314 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_951314 : Nat := 118140960795 + 951314 * 2 ^ 59
def prefixEnd_951314 : Nat := 4983230072969 + 3 ^ 40 * 951314 * 2
def baseEnd_951314 : Nat := 434205631423463300711105

theorem tailTrace_951314 : CollatzResearch.WordTrace tailWord_951314 prefixEnd_951314 434205631423463300711105 := by
  unfold tailWord_951314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674318018889831085323249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23131514717039549560861997 8674318018889831085323249)
  ·
    refine ⟨6505738514167373313992437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8674318018889831085323249 6505738514167373313992437)
    ·
      refine ⟨609912985703191248186791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6505738514167373313992437 609912985703191248186791)
      ·
        refine ⟨914869478554786872280187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609912985703191248186791 914869478554786872280187)
        ·
          refine ⟨1372304217832180308420281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914869478554786872280187 1372304217832180308420281)
          ·
            refine ⟨1029228163374135231315211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372304217832180308420281 1029228163374135231315211)
            ·
              refine ⟨1543842245061202846972817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029228163374135231315211 1543842245061202846972817)
              ·
                refine ⟨1157881683795902135229613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543842245061202846972817 1157881683795902135229613)
                ·
                  refine ⟨434205631423463300711105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157881683795902135229613 434205631423463300711105)
                  ·
                    rfl

theorem cell20_951314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_951314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951314 prefixEnd_951314 := by exact prefixLift 951314
  have htrace : WordTrace (prefixWord ++ tailWord_951314) baseStart_951314 baseEnd_951314 := by
    simpa [prefixWord, tailWord_951314, baseEnd_951314] using wordTrace_append hprefix tailTrace_951314
  have hstable : (prefixWord ++ tailWord_951314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951314).length < 2 ^ (prefixWord ++ tailWord_951314).sum := by decide
  have hdescent : baseEnd_951314 < baseStart_951314 := by decide
  rcases family_descends (prefixWord ++ tailWord_951314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951329 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_951329 : Nat := 118140960795 + 951329 * 2 ^ 59
def prefixEnd_951329 : Nat := 4983230072969 + 3 ^ 40 * 951329 * 2
def baseEnd_951329 : Nat := 434212477832189915211043

theorem tailTrace_951329 : CollatzResearch.WordTrace tailWord_951329 prefixEnd_951329 434212477832189915211043 := by
  unfold tailWord_951329
  simp only [CollatzResearch.WordTrace]
  refine ⟨34697819170504981903089041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23131879447003321268726027 34697819170504981903089041)
  ·
    refine ⟨26023364377878736427316781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34697819170504981903089041 26023364377878736427316781)
    ·
      refine ⟨9758761641704526160243793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26023364377878736427316781 9758761641704526160243793)
      ·
        refine ⟨7319071231278394620182845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9758761641704526160243793 7319071231278394620182845)
        ·
          refine ⟨2744651711729397982568567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7319071231278394620182845 2744651711729397982568567)
          ·
            refine ⟨4116977567594096973852851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744651711729397982568567 4116977567594096973852851)
            ·
              refine ⟨6175466351391145460779277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116977567594096973852851 6175466351391145460779277)
              ·
                refine ⟨2315799881771679547792229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6175466351391145460779277 2315799881771679547792229)
                ·
                  refine ⟨434212477832189915211043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315799881771679547792229 434212477832189915211043)
                  ·
                    rfl

theorem cell20_951329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_951329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951329 prefixEnd_951329 := by exact prefixLift 951329
  have htrace : WordTrace (prefixWord ++ tailWord_951329) baseStart_951329 baseEnd_951329 := by
    simpa [prefixWord, tailWord_951329, baseEnd_951329] using wordTrace_append hprefix tailTrace_951329
  have hstable : (prefixWord ++ tailWord_951329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951329).length < 2 ^ (prefixWord ++ tailWord_951329).sum := by decide
  have hdescent : baseEnd_951329 < baseStart_951329 := by decide
  rcases family_descends (prefixWord ++ tailWord_951329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951353 : List Nat := [1, 2, 1, 5, 2, 1, 4, 4]
def baseStart_951353 : Nat := 118140960795 + 951353 * 2 ^ 59
def prefixEnd_951353 : Nat := 4983230072969 + 3 ^ 40 * 951353 * 2
def baseEnd_951353 : Nat := 144741144028717499470315

theorem tailTrace_951353 : CollatzResearch.WordTrace tailWord_951353 prefixEnd_951353 144741144028717499470315 := by
  unfold tailWord_951353
  simp only [CollatzResearch.WordTrace]
  refine ⟨34698694522418034001962713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23132463014945356001308475 34698694522418034001962713)
  ·
    refine ⟨26024020891813525501472035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34698694522418034001962713 26024020891813525501472035)
    ·
      refine ⟨39036031337720288252208053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26024020891813525501472035 39036031337720288252208053)
      ·
        refine ⟨3659627937911277023644505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39036031337720288252208053 3659627937911277023644505)
        ·
          refine ⟨2744720953433457767733379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3659627937911277023644505 2744720953433457767733379)
          ·
            refine ⟨4117081430150186651600069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744720953433457767733379 4117081430150186651600069)
            ·
              refine ⟨771952768153159997175013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4117081430150186651600069 771952768153159997175013)
              ·
                refine ⟨144741144028717499470315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 771952768153159997175013 144741144028717499470315)
                ·
                  rfl

theorem cell20_951353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_951353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951353 prefixEnd_951353 := by exact prefixLift 951353
  have htrace : WordTrace (prefixWord ++ tailWord_951353) baseStart_951353 baseEnd_951353 := by
    simpa [prefixWord, tailWord_951353, baseEnd_951353] using wordTrace_append hprefix tailTrace_951353
  have hstable : (prefixWord ++ tailWord_951353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951353).length < 2 ^ (prefixWord ++ tailWord_951353).sum := by decide
  have hdescent : baseEnd_951353 < baseStart_951353 := by decide
  rcases family_descends (prefixWord ++ tailWord_951353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951381 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_951381 : Nat := 118140960795 + 951381 * 2 ^ 59
def prefixEnd_951381 : Nat := 4983230072969 + 3 ^ 40 * 951381 * 2
def baseEnd_951381 : Nat := 434236212049108845477497

theorem tailTrace_951381 : CollatzResearch.WordTrace tailWord_951381 prefixEnd_951381 434236212049108845477497 := by
  unfold tailWord_951381
  simp only [CollatzResearch.WordTrace]
  refine ⟨34699715766316594783981997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23133143844211063189321331 34699715766316594783981997)
  ·
    refine ⟨13012393412368723043993249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34699715766316594783981997 13012393412368723043993249)
    ·
      refine ⟨9759295059276542282994937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13012393412368723043993249 9759295059276542282994937)
      ·
        refine ⟨7319471294457406712246203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9759295059276542282994937 7319471294457406712246203)
        ·
          refine ⟨10979206941686110068369305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319471294457406712246203 10979206941686110068369305)
          ·
            refine ⟨8234405206264582551276979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10979206941686110068369305 8234405206264582551276979)
            ·
              refine ⟨12351607809396873826915469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234405206264582551276979 12351607809396873826915469)
              ·
                refine ⟨4631852928523827685093301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12351607809396873826915469 4631852928523827685093301)
                ·
                  refine ⟨434236212049108845477497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4631852928523827685093301 434236212049108845477497)
                  ·
                    rfl

theorem cell20_951381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_951381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951381 prefixEnd_951381 := by exact prefixLift 951381
  have htrace : WordTrace (prefixWord ++ tailWord_951381) baseStart_951381 baseEnd_951381 := by
    simpa [prefixWord, tailWord_951381, baseEnd_951381] using wordTrace_append hprefix tailTrace_951381
  have hstable : (prefixWord ++ tailWord_951381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951381).length < 2 ^ (prefixWord ++ tailWord_951381).sum := by decide
  have hdescent : baseEnd_951381 < baseStart_951381 := by decide
  rcases family_descends (prefixWord ++ tailWord_951381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951390 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_951390 : Nat := 118140960795 + 951390 * 2 ^ 59
def prefixEnd_951390 : Nat := 4983230072969 + 3 ^ 40 * 951390 * 2
def baseEnd_951390 : Nat := 434240319894344814177461

theorem tailTrace_951390 : CollatzResearch.WordTrace tailWord_951390 prefixEnd_951390 434240319894344814177461 := by
  unfold tailWord_951390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337505502910498665132453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23133362682189326214039749 4337505502910498665132453)
  ·
    refine ⟨813282281795718499712335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4337505502910498665132453 813282281795718499712335)
    ·
      refine ⟨1219923422693577749568503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813282281795718499712335 1219923422693577749568503)
      ·
        refine ⟨1829885134040366624352755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219923422693577749568503 1829885134040366624352755)
        ·
          refine ⟨2744827701060549936529133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829885134040366624352755 2744827701060549936529133)
          ·
            refine ⟨1029310387897706226198425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2744827701060549936529133 1029310387897706226198425)
            ·
              refine ⟨771982790923279669648819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029310387897706226198425 771982790923279669648819)
              ·
                refine ⟨1157974186384919504473229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771982790923279669648819 1157974186384919504473229)
                ·
                  refine ⟨434240319894344814177461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157974186384919504473229 434240319894344814177461)
                  ·
                    rfl

theorem cell20_951390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_951390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951390 prefixEnd_951390 := by exact prefixLift 951390
  have htrace : WordTrace (prefixWord ++ tailWord_951390) baseStart_951390 baseEnd_951390 := by
    simpa [prefixWord, tailWord_951390, baseEnd_951390] using wordTrace_append hprefix tailTrace_951390
  have hstable : (prefixWord ++ tailWord_951390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951390).length < 2 ^ (prefixWord ++ tailWord_951390).sum := by decide
  have hdescent : baseEnd_951390 < baseStart_951390 := by decide
  rcases family_descends (prefixWord ++ tailWord_951390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951394 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_951394 : Nat := 118140960795 + 951394 * 2 ^ 59
def prefixEnd_951394 : Nat := 4983230072969 + 3 ^ 40 * 951394 * 2
def baseEnd_951394 : Nat := 434242145603338578044111

theorem tailTrace_951394 : CollatzResearch.WordTrace tailWord_951394 prefixEnd_951394 434242145603338578044111 := by
  unfold tailWord_951394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675047478817374501051309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23133459943512998669470157 8675047478817374501051309)
  ·
    refine ⟨3253142804556515437894241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8675047478817374501051309 3253142804556515437894241)
    ·
      refine ⟨2439857103417386578420681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3253142804556515437894241 2439857103417386578420681)
      ·
        refine ⟨1829892827563039933815511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2439857103417386578420681 1829892827563039933815511)
        ·
          refine ⟨2744839241344559900723267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829892827563039933815511 2744839241344559900723267)
          ·
            refine ⟨4117258862016839851084901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744839241344559900723267 4117258862016839851084901)
            ·
              refine ⟨771986036628157472078419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4117258862016839851084901 771986036628157472078419)
              ·
                refine ⟨1157979054942236208117629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771986036628157472078419 1157979054942236208117629)
                ·
                  refine ⟨434242145603338578044111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157979054942236208117629 434242145603338578044111)
                  ·
                    rfl

theorem cell20_951394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_951394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951394 prefixEnd_951394 := by exact prefixLift 951394
  have htrace : WordTrace (prefixWord ++ tailWord_951394) baseStart_951394 baseEnd_951394 := by
    simpa [prefixWord, tailWord_951394, baseEnd_951394] using wordTrace_append hprefix tailTrace_951394
  have hstable : (prefixWord ++ tailWord_951394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951394).length < 2 ^ (prefixWord ++ tailWord_951394).sum := by decide
  have hdescent : baseEnd_951394 < baseStart_951394 := by decide
  rcases family_descends (prefixWord ++ tailWord_951394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951433 : List Nat := [1, 2, 1, 1, 4, 11]
def baseStart_951433 : Nat := 118140960795 + 951433 * 2 ^ 59
def prefixEnd_951433 : Nat := 4983230072969 + 3 ^ 40 * 951433 * 2
def baseEnd_951433 : Nat := 16083701713556584286813

theorem tailTrace_951433 : CollatzResearch.WordTrace tailWord_951433 prefixEnd_951433 16083701713556584286813 := by
  unfold tailWord_951433
  simp only [CollatzResearch.WordTrace]
  refine ⟨34701612362128207664874953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23134408241418805109916635 34701612362128207664874953)
  ·
    refine ⟨26026209271596155748656215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34701612362128207664874953 26026209271596155748656215)
    ·
      refine ⟨39039313907394233622984323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26026209271596155748656215 39039313907394233622984323)
      ·
        refine ⟨58558970861091350434476485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39039313907394233622984323 58558970861091350434476485)
        ·
          refine ⟨10979807036454628206464341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58558970861091350434476485 10979807036454628206464341)
          ·
            refine ⟨16083701713556584286813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10979807036454628206464341 16083701713556584286813)
            ·
              rfl

theorem cell20_951433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 11].length) (baseStart_951433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951433 prefixEnd_951433 := by exact prefixLift 951433
  have htrace : WordTrace (prefixWord ++ tailWord_951433) baseStart_951433 baseEnd_951433 := by
    simpa [prefixWord, tailWord_951433, baseEnd_951433] using wordTrace_append hprefix tailTrace_951433
  have hstable : (prefixWord ++ tailWord_951433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951433).length < 2 ^ (prefixWord ++ tailWord_951433).sum := by decide
  have hdescent : baseEnd_951433 < baseStart_951433 := by decide
  rcases family_descends (prefixWord ++ tailWord_951433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951471 : List Nat := [1, 1, 2, 1, 2, 3, 2, 8]
def baseStart_951471 : Nat := 118140960795 + 951471 * 2 ^ 59
def prefixEnd_951471 : Nat := 4983230072969 + 3 ^ 40 * 951471 * 2
def baseEnd_951471 : Nat := 144759096833822844159043

theorem tailTrace_951471 : CollatzResearch.WordTrace tailWord_951471 prefixEnd_951471 144759096833822844159043 := by
  unfold tailWord_951471
  simp only [CollatzResearch.WordTrace]
  refine ⟨34702998335990540154758267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23135332223993693436505511 34702998335990540154758267)
  ·
    refine ⟨52054497503985810232137401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34702998335990540154758267 52054497503985810232137401)
    ·
      refine ⟨39040873127989357674103051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52054497503985810232137401 39040873127989357674103051)
      ·
        refine ⟨58561309691984036511154577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39040873127989357674103051 58561309691984036511154577)
        ·
          refine ⟨43920982268988027383365933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58561309691984036511154577 43920982268988027383365933)
          ·
            refine ⟨16470368350870510268762225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43920982268988027383365933 16470368350870510268762225)
            ·
              refine ⟨12352776263152882701571669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16470368350870510268762225 12352776263152882701571669)
              ·
                refine ⟨144759096833822844159043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12352776263152882701571669 144759096833822844159043)
                ·
                  rfl

theorem cell20_951471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_951471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951471 prefixEnd_951471 := by exact prefixLift 951471
  have htrace : WordTrace (prefixWord ++ tailWord_951471) baseStart_951471 baseEnd_951471 := by
    simpa [prefixWord, tailWord_951471, baseEnd_951471] using wordTrace_append hprefix tailTrace_951471
  have hstable : (prefixWord ++ tailWord_951471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951471).length < 2 ^ (prefixWord ++ tailWord_951471).sum := by decide
  have hdescent : baseEnd_951471 < baseStart_951471 := by decide
  rcases family_descends (prefixWord ++ tailWord_951471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951488 : List Nat := [2, 1, 1, 2, 6, 1, 7]
def baseStart_951488 : Nat := 118140960795 + 951488 * 2 ^ 59
def prefixEnd_951488 : Nat := 4983230072969 + 3 ^ 40 * 951488 * 2
def baseEnd_951488 : Nat := 48253894418299114323377

theorem tailTrace_951488 : CollatzResearch.WordTrace tailWord_951488 prefixEnd_951488 48253894418299114323377 := by
  unfold tailWord_951488
  simp only [CollatzResearch.WordTrace]
  refine ⟨17351809188464476029063559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23135745584619301372084745 17351809188464476029063559)
  ·
    refine ⟨26027713782696714043595339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17351809188464476029063559 26027713782696714043595339)
    ·
      refine ⟨39041570674045071065393009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26027713782696714043595339 39041570674045071065393009)
      ·
        refine ⟨29281178005533803299044757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39041570674045071065393009 29281178005533803299044757)
        ·
          refine ⟨1372555219009397029642723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29281178005533803299044757 1372555219009397029642723)
          ·
            refine ⟨2058832828514095544464085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372555219009397029642723 2058832828514095544464085)
            ·
              refine ⟨48253894418299114323377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2058832828514095544464085 48253894418299114323377)
              ·
                rfl

theorem cell20_951488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 7].length) (baseStart_951488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951488 prefixEnd_951488 := by exact prefixLift 951488
  have htrace : WordTrace (prefixWord ++ tailWord_951488) baseStart_951488 baseEnd_951488 := by
    simpa [prefixWord, tailWord_951488, baseEnd_951488] using wordTrace_append hprefix tailTrace_951488
  have hstable : (prefixWord ++ tailWord_951488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951488).length < 2 ^ (prefixWord ++ tailWord_951488).sum := by decide
  have hdescent : baseEnd_951488 < baseStart_951488 := by decide
  rcases family_descends (prefixWord ++ tailWord_951488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951498 : List Nat := [3, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_951498 : Nat := 118140960795 + 951498 * 2 ^ 59
def prefixEnd_951498 : Nat := 4983230072969 + 3 ^ 40 * 951498 * 2
def baseEnd_951498 : Nat := 434289614037176438577019

theorem tailTrace_951498 : CollatzResearch.WordTrace tailWord_951498 prefixEnd_951498 434289614037176438577019 := by
  unfold tailWord_951498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675995776723180941497787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23135988737928482510660765 8675995776723180941497787)
  ·
    refine ⟨13013993665084771412246681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8675995776723180941497787 13013993665084771412246681)
    ·
      refine ⟨9760495248813578559185011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13013993665084771412246681 9760495248813578559185011)
      ·
        refine ⟨14640742873220367838777517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9760495248813578559185011 14640742873220367838777517)
        ·
          refine ⟨5490278577457637939541569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14640742873220367838777517 5490278577457637939541569)
          ·
            refine ⟨4117708933093228454656177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5490278577457637939541569 4117708933093228454656177)
            ·
              refine ⟨3088281699819921340992133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117708933093228454656177 3088281699819921340992133)
              ·
                refine ⟨579052818716235251436025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3088281699819921340992133 579052818716235251436025)
                ·
                  refine ⟨434289614037176438577019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579052818716235251436025 434289614037176438577019)
                  ·
                    rfl

theorem cell20_951498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_951498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951498 prefixEnd_951498 := by exact prefixLift 951498
  have htrace : WordTrace (prefixWord ++ tailWord_951498) baseStart_951498 baseEnd_951498 := by
    simpa [prefixWord, tailWord_951498, baseEnd_951498] using wordTrace_append hprefix tailTrace_951498
  have hstable : (prefixWord ++ tailWord_951498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951498).length < 2 ^ (prefixWord ++ tailWord_951498).sum := by decide
  have hdescent : baseEnd_951498 < baseStart_951498 := by decide
  rcases family_descends (prefixWord ++ tailWord_951498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951550 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_951550 : Nat := 118140960795 + 951550 * 2 ^ 59
def prefixEnd_951550 : Nat := 4983230072969 + 3 ^ 40 * 951550 * 2
def baseEnd_951550 : Nat := 434313348254095368843473

theorem tailTrace_951550 : CollatzResearch.WordTrace tailWord_951550 prefixEnd_951550 434313348254095368843473 := by
  unfold tailWord_951550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338234962838042080860513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23137253135136224431256069 4338234962838042080860513)
  ·
    refine ⟨3253676222128531560645385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4338234962838042080860513 3253676222128531560645385)
    ·
      refine ⟨2440257166596398670484039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3253676222128531560645385 2440257166596398670484039)
      ·
        refine ⟨3660385749894598005726059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440257166596398670484039 3660385749894598005726059)
        ·
          refine ⟨5490578624841897008589089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660385749894598005726059 5490578624841897008589089)
          ·
            refine ⟨4117933968631422756441817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5490578624841897008589089 4117933968631422756441817)
            ·
              refine ⟨3088450476473567067331363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117933968631422756441817 3088450476473567067331363)
              ·
                refine ⟨4632675714710350600997045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088450476473567067331363 4632675714710350600997045)
                ·
                  refine ⟨434313348254095368843473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4632675714710350600997045 434313348254095368843473)
                  ·
                    rfl

theorem cell20_951550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_951550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951550 prefixEnd_951550 := by exact prefixLift 951550
  have htrace : WordTrace (prefixWord ++ tailWord_951550) baseStart_951550 baseEnd_951550 := by
    simpa [prefixWord, tailWord_951550, baseEnd_951550] using wordTrace_append hprefix tailTrace_951550
  have hstable : (prefixWord ++ tailWord_951550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951550).length < 2 ^ (prefixWord ++ tailWord_951550).sum := by decide
  have hdescent : baseEnd_951550 < baseStart_951550 := by decide
  rcases family_descends (prefixWord ++ tailWord_951550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951553 : List Nat := [1, 2, 4, 1, 1, 4, 3, 2, 2]
def baseStart_951553 : Nat := 118140960795 + 951553 * 2 ^ 59
def prefixEnd_951553 : Nat := 4983230072969 + 3 ^ 40 * 951553 * 2
def baseEnd_951553 : Nat := 434314717535840691743461

theorem tailTrace_951553 : CollatzResearch.WordTrace tailWord_951553 prefixEnd_951553 434314717535840691743461 := by
  unfold tailWord_951553
  simp only [CollatzResearch.WordTrace]
  refine ⟨34705989121693468159243313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23137326081128978772828875 34705989121693468159243313)
  ·
    refine ⟨26029491841270101119432485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34705989121693468159243313 26029491841270101119432485)
    ·
      refine ⟨4880529720238143959893591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26029491841270101119432485 4880529720238143959893591)
      ·
        refine ⟨7320794580357215939840387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880529720238143959893591 7320794580357215939840387)
        ·
          refine ⟨10981191870535823909760581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320794580357215939840387 10981191870535823909760581)
          ·
            refine ⟨2058973475725466983080109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10981191870535823909760581 2058973475725466983080109)
            ·
              refine ⟨772115053397050118655041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2058973475725466983080109 772115053397050118655041)
              ·
                refine ⟨579086290047787588991281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772115053397050118655041 579086290047787588991281)
                ·
                  refine ⟨434314717535840691743461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579086290047787588991281 434314717535840691743461)
                  ·
                    rfl

theorem cell20_951553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_951553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951553 prefixEnd_951553 := by exact prefixLift 951553
  have htrace : WordTrace (prefixWord ++ tailWord_951553) baseStart_951553 baseEnd_951553 := by
    simpa [prefixWord, tailWord_951553, baseEnd_951553] using wordTrace_append hprefix tailTrace_951553
  have hstable : (prefixWord ++ tailWord_951553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951553).length < 2 ^ (prefixWord ++ tailWord_951553).sum := by decide
  have hdescent : baseEnd_951553 < baseStart_951553 := by decide
  rcases family_descends (prefixWord ++ tailWord_951553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951564 : List Nat := [2, 2, 1, 2, 2, 4, 2, 5]
def baseStart_951564 : Nat := 118140960795 + 951564 * 2 ^ 59
def prefixEnd_951564 : Nat := 4983230072969 + 3 ^ 40 * 951564 * 2
def baseEnd_951564 : Nat := 144773246078524514125583

theorem tailTrace_951564 : CollatzResearch.WordTrace tailWord_951564 prefixEnd_951564 144773246078524514125583 := by
  unfold tailWord_951564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353195162326808518946873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23137593549769078025262497 17353195162326808518946873)
  ·
    refine ⟨13014896371745106389210155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17353195162326808518946873 13014896371745106389210155)
    ·
      refine ⟨19522344557617659583815233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13014896371745106389210155 19522344557617659583815233)
      ·
        refine ⟨14641758418213244687861425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19522344557617659583815233 14641758418213244687861425)
        ·
          refine ⟨10981318813659933515896069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14641758418213244687861425 10981318813659933515896069)
          ·
            refine ⟨2058997277561237534230513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10981318813659933515896069 2058997277561237534230513)
            ·
              refine ⟨1544247958170928150672885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058997277561237534230513 1544247958170928150672885)
              ·
                refine ⟨144773246078524514125583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1544247958170928150672885 144773246078524514125583)
                ·
                  rfl

theorem cell20_951564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_951564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951564 prefixEnd_951564 := by exact prefixLift 951564
  have htrace : WordTrace (prefixWord ++ tailWord_951564) baseStart_951564 baseEnd_951564 := by
    simpa [prefixWord, tailWord_951564, baseEnd_951564] using wordTrace_append hprefix tailTrace_951564
  have hstable : (prefixWord ++ tailWord_951564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951564).length < 2 ^ (prefixWord ++ tailWord_951564).sum := by decide
  have hdescent : baseEnd_951564 < baseStart_951564 := by decide
  rcases family_descends (prefixWord ++ tailWord_951564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951612 : List Nat := [2, 2, 2, 2, 1, 4, 1, 4, 2]
def baseStart_951612 : Nat := 118140960795 + 951612 * 2 ^ 59
def prefixEnd_951612 : Nat := 4983230072969 + 3 ^ 40 * 951612 * 2
def baseEnd_951612 : Nat := 434341646743498708776553

theorem tailTrace_951612 : CollatzResearch.WordTrace tailWord_951612 prefixEnd_951612 434341646743498708776553 := by
  unfold tailWord_951612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17354070514239860617820545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23138760685653147490427393 17354070514239860617820545)
  ·
    refine ⟨13015552885679895463365409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17354070514239860617820545 13015552885679895463365409)
    ·
      refine ⟨9761664664259921597524057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13015552885679895463365409 9761664664259921597524057)
      ·
        refine ⟨7321248498194941198143043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9761664664259921597524057 7321248498194941198143043)
        ·
          refine ⟨10981872747292411797214565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321248498194941198143043 10981872747292411797214565)
          ·
            refine ⟨2059101140117327211977731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10981872747292411797214565 2059101140117327211977731)
            ·
              refine ⟨3088651710175990817966597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059101140117327211977731 3088651710175990817966597)
              ·
                refine ⟨579122195657998278368737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3088651710175990817966597 579122195657998278368737)
                ·
                  refine ⟨434341646743498708776553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579122195657998278368737 434341646743498708776553)
                  ·
                    rfl

theorem cell20_951612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_951612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951612 prefixEnd_951612 := by exact prefixLift 951612
  have htrace : WordTrace (prefixWord ++ tailWord_951612) baseStart_951612 baseEnd_951612 := by
    simpa [prefixWord, tailWord_951612, baseEnd_951612] using wordTrace_append hprefix tailTrace_951612
  have hstable : (prefixWord ++ tailWord_951612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951612).length < 2 ^ (prefixWord ++ tailWord_951612).sum := by decide
  have hdescent : baseEnd_951612 < baseStart_951612 := by decide
  rcases family_descends (prefixWord ++ tailWord_951612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951616 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_951616 : Nat := 118140960795 + 951616 * 2 ^ 59
def prefixEnd_951616 : Nat := 4983230072969 + 3 ^ 40 * 951616 * 2
def baseEnd_951616 : Nat := 434343472452492472643203

theorem tailTrace_951616 : CollatzResearch.WordTrace tailWord_951616 prefixEnd_951616 434343472452492472643203 := by
  unfold tailWord_951616
  simp only [CollatzResearch.WordTrace]
  refine ⟨17354143460232614959393351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23138857946976819945857801 17354143460232614959393351)
  ·
    refine ⟨26031215190348922439090027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17354143460232614959393351 26031215190348922439090027)
    ·
      refine ⟨39046822785523383658635041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26031215190348922439090027 39046822785523383658635041)
      ·
        refine ⟨29285117089142537743976281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39046822785523383658635041 29285117089142537743976281)
        ·
          refine ⟨21963837816856903307982211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29285117089142537743976281 21963837816856903307982211)
          ·
            refine ⟨32945756725285354961973317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21963837816856903307982211 32945756725285354961973317)
            ·
              refine ⟨6177329385991004055369997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32945756725285354961973317 6177329385991004055369997)
              ·
                refine ⟨2316498519746626520763749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6177329385991004055369997 2316498519746626520763749)
                ·
                  refine ⟨434343472452492472643203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316498519746626520763749 434343472452492472643203)
                  ·
                    rfl

theorem cell20_951616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_951616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951616 prefixEnd_951616 := by exact prefixLift 951616
  have htrace : WordTrace (prefixWord ++ tailWord_951616) baseStart_951616 baseEnd_951616 := by
    simpa [prefixWord, tailWord_951616, baseEnd_951616] using wordTrace_append hprefix tailTrace_951616
  have hstable : (prefixWord ++ tailWord_951616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951616).length < 2 ^ (prefixWord ++ tailWord_951616).sum := by decide
  have hdescent : baseEnd_951616 < baseStart_951616 := by decide
  rcases family_descends (prefixWord ++ tailWord_951616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951629 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 4]
def baseStart_951629 : Nat := 118140960795 + 951629 * 2 ^ 59
def prefixEnd_951629 : Nat := 4983230072969 + 3 ^ 40 * 951629 * 2
def baseEnd_951629 : Nat := 434349406006722205209817

theorem tailTrace_951629 : CollatzResearch.WordTrace tailWord_951629 prefixEnd_951629 434349406006722205209817 := by
  unfold tailWord_951629
  simp only [CollatzResearch.WordTrace]
  refine ⟨34708761069418133139009941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23139174046278755426006627 34708761069418133139009941)
  ·
    refine ⟨1626973175128974990891091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34708761069418133139009941 1626973175128974990891091)
    ·
      refine ⟨2440459762693462486336637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626973175128974990891091 2440459762693462486336637)
      ·
        refine ⟨915172411010048432376239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2440459762693462486336637 915172411010048432376239)
        ·
          refine ⟨1372758616515072648564359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915172411010048432376239 1372758616515072648564359)
          ·
            refine ⟨2059137924772608972846539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372758616515072648564359 2059137924772608972846539)
            ·
              refine ⟨3088706887158913459269809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059137924772608972846539 3088706887158913459269809)
              ·
                refine ⟨2316530165369185094452357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088706887158913459269809 2316530165369185094452357)
                ·
                  refine ⟨434349406006722205209817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316530165369185094452357 434349406006722205209817)
                  ·
                    rfl

theorem cell20_951629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_951629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951629 prefixEnd_951629 := by exact prefixLift 951629
  have htrace : WordTrace (prefixWord ++ tailWord_951629) baseStart_951629 baseEnd_951629 := by
    simpa [prefixWord, tailWord_951629, baseEnd_951629] using wordTrace_append hprefix tailTrace_951629
  have hstable : (prefixWord ++ tailWord_951629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951629).length < 2 ^ (prefixWord ++ tailWord_951629).sum := by decide
  have hdescent : baseEnd_951629 < baseStart_951629 := by decide
  rcases family_descends (prefixWord ++ tailWord_951629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951640 : List Nat := [2, 1, 2, 2, 1, 1, 7, 4]
def baseStart_951640 : Nat := 118140960795 + 951640 * 2 ^ 59
def prefixEnd_951640 : Nat := 4983230072969 + 3 ^ 40 * 951640 * 2
def baseEnd_951640 : Nat := 144784808902151685281035

theorem tailTrace_951640 : CollatzResearch.WordTrace tailWord_951640 prefixEnd_951640 144784808902151685281035 := by
  unfold tailWord_951640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17354581136189141008830187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23139441514918854678440249 17354581136189141008830187)
  ·
    refine ⟨26031871704283711513245281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17354581136189141008830187 26031871704283711513245281)
    ·
      refine ⟨19523903778212783634933961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26031871704283711513245281 19523903778212783634933961)
      ·
        refine ⟨14642927833659587726200471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19523903778212783634933961 14642927833659587726200471)
        ·
          refine ⟨21964391750489381589300707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14642927833659587726200471 21964391750489381589300707)
          ·
            refine ⟨32946587625734072383951061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21964391750489381589300707 32946587625734072383951061)
            ·
              refine ⟨772185647478142321498853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32946587625734072383951061 772185647478142321498853)
              ·
                refine ⟨144784808902151685281035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772185647478142321498853 144784808902151685281035)
                ·
                  rfl

theorem cell20_951640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_951640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951640 prefixEnd_951640 := by exact prefixLift 951640
  have htrace : WordTrace (prefixWord ++ tailWord_951640) baseStart_951640 baseEnd_951640 := by
    simpa [prefixWord, tailWord_951640, baseEnd_951640] using wordTrace_append hprefix tailTrace_951640
  have hstable : (prefixWord ++ tailWord_951640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951640).length < 2 ^ (prefixWord ++ tailWord_951640).sum := by decide
  have hdescent : baseEnd_951640 < baseStart_951640 := by decide
  rcases family_descends (prefixWord ++ tailWord_951640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951671 : List Nat := [1, 1, 3, 1, 1, 2, 3, 6, 2]
def baseStart_951671 : Nat := 118140960795 + 951671 * 2 ^ 59
def prefixEnd_951671 : Nat := 4983230072969 + 3 ^ 40 * 951671 * 2
def baseEnd_951671 : Nat := 434368575951156725809645

theorem tailTrace_951671 : CollatzResearch.WordTrace tailWord_951671 prefixEnd_951671 434368575951156725809645 := by
  unfold tailWord_951671
  simp only [CollatzResearch.WordTrace]
  refine ⟨34710292935265974312038867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23140195290177316208025911 34710292935265974312038867)
  ·
    refine ⟨52065439402898961468058301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34710292935265974312038867 52065439402898961468058301)
    ·
      refine ⟨19524539776087110550521863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52065439402898961468058301 19524539776087110550521863)
      ·
        refine ⟨29286809664130665825782795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19524539776087110550521863 29286809664130665825782795)
        ·
          refine ⟨43930214496195998738674193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29286809664130665825782795 43930214496195998738674193)
          ·
            refine ⟨32947660872146999054005645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43930214496195998738674193 32947660872146999054005645)
            ·
              refine ⟨12355372827055124645252117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32947660872146999054005645 12355372827055124645252117)
              ·
                refine ⟨579158101268208967746193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12355372827055124645252117 579158101268208967746193)
                ·
                  refine ⟨434368575951156725809645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579158101268208967746193 434368575951156725809645)
                  ·
                    rfl

theorem cell20_951671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 2].length) (baseStart_951671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951671 prefixEnd_951671 := by exact prefixLift 951671
  have htrace : WordTrace (prefixWord ++ tailWord_951671) baseStart_951671 baseEnd_951671 := by
    simpa [prefixWord, tailWord_951671, baseEnd_951671] using wordTrace_append hprefix tailTrace_951671
  have hstable : (prefixWord ++ tailWord_951671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951671).length < 2 ^ (prefixWord ++ tailWord_951671).sum := by decide
  have hdescent : baseEnd_951671 < baseStart_951671 := by decide
  rcases family_descends (prefixWord ++ tailWord_951671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951685 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 3]
def baseStart_951685 : Nat := 118140960795 + 951685 * 2 ^ 59
def prefixEnd_951685 : Nat := 4983230072969 + 3 ^ 40 * 951685 * 2
def baseEnd_951685 : Nat := 434374965932634899342921

theorem tailTrace_951685 : CollatzResearch.WordTrace tailWord_951685 prefixEnd_951685 434374965932634899342921 := by
  unfold tailWord_951685
  simp only [CollatzResearch.WordTrace]
  refine ⟨34710803557215254703048509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23140535704810169802032339 34710803557215254703048509)
  ·
    refine ⟨13016551333955720513643191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34710803557215254703048509 13016551333955720513643191)
    ·
      refine ⟨19524827000933580770464787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016551333955720513643191 19524827000933580770464787)
      ·
        refine ⟨29287240501400371155697181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19524827000933580770464787 29287240501400371155697181)
        ·
          refine ⟨10982715188025139183386443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29287240501400371155697181 10982715188025139183386443)
          ·
            refine ⟨16474072782037708775079665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10982715188025139183386443 16474072782037708775079665)
            ·
              refine ⟨12355554586528281581309749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16474072782037708775079665 12355554586528281581309749)
              ·
                refine ⟨1158333242487026398247789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12355554586528281581309749 1158333242487026398247789)
                ·
                  refine ⟨434374965932634899342921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1158333242487026398247789 434374965932634899342921)
                  ·
                    rfl

theorem cell20_951685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_951685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951685 prefixEnd_951685 := by exact prefixLift 951685
  have htrace : WordTrace (prefixWord ++ tailWord_951685) baseStart_951685 baseEnd_951685 := by
    simpa [prefixWord, tailWord_951685, baseEnd_951685] using wordTrace_append hprefix tailTrace_951685
  have hstable : (prefixWord ++ tailWord_951685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951685).length < 2 ^ (prefixWord ++ tailWord_951685).sum := by decide
  have hdescent : baseEnd_951685 < baseStart_951685 := by decide
  rcases family_descends (prefixWord ++ tailWord_951685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951692 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_951692 : Nat := 118140960795 + 951692 * 2 ^ 59
def prefixEnd_951692 : Nat := 4983230072969 + 3 ^ 40 * 951692 * 2
def baseEnd_951692 : Nat := 434378160923373986109559

theorem tailTrace_951692 : CollatzResearch.WordTrace tailWord_951692 prefixEnd_951692 434378160923373986109559 := by
  unfold tailWord_951692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355529434094947449276665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23140705912126596599035553 17355529434094947449276665)
  ·
    refine ⟨13016647075571210586957499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17355529434094947449276665 13016647075571210586957499)
    ·
      refine ⟨19524970613356815880436249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016647075571210586957499 19524970613356815880436249)
      ·
        refine ⟨14643727960017611910327187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19524970613356815880436249 14643727960017611910327187)
        ·
          refine ⟨21965591940026417865490781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14643727960017611910327187 21965591940026417865490781)
          ·
            refine ⟨8237096977509906699559043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21965591940026417865490781 8237096977509906699559043)
            ·
              refine ⟨12355645466264860049338565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237096977509906699559043 12355645466264860049338565)
              ·
                refine ⟨2316683524924661259250981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12355645466264860049338565 2316683524924661259250981)
                ·
                  refine ⟨434378160923373986109559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316683524924661259250981 434378160923373986109559)
                  ·
                    rfl

theorem cell20_951692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_951692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951692 prefixEnd_951692 := by exact prefixLift 951692
  have htrace : WordTrace (prefixWord ++ tailWord_951692) baseStart_951692 baseEnd_951692 := by
    simpa [prefixWord, tailWord_951692, baseEnd_951692] using wordTrace_append hprefix tailTrace_951692
  have hstable : (prefixWord ++ tailWord_951692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951692).length < 2 ^ (prefixWord ++ tailWord_951692).sum := by decide
  have hdescent : baseEnd_951692 < baseStart_951692 := by decide
  rcases family_descends (prefixWord ++ tailWord_951692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951730 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_951730 : Nat := 118140960795 + 951730 * 2 ^ 59
def prefixEnd_951730 : Nat := 4983230072969 + 3 ^ 40 * 951730 * 2
def baseEnd_951730 : Nat := 434395505158814742842737

theorem tailTrace_951730 : CollatzResearch.WordTrace tailWord_951730 prefixEnd_951730 434395505158814742842737 := by
  unfold tailWord_951730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678111210513056847109161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23141629894701484925624429 8678111210513056847109161)
  ·
    refine ⟨6508583407884792635331871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8678111210513056847109161 6508583407884792635331871)
    ·
      refine ⟨9762875111827188952997807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508583407884792635331871 9762875111827188952997807)
      ·
        refine ⟨14644312667740783429496711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762875111827188952997807 14644312667740783429496711)
        ·
          refine ⟨21966469001611175144245067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14644312667740783429496711 21966469001611175144245067)
          ·
            refine ⟨32949703502416762716367601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21966469001611175144245067 32949703502416762716367601)
            ·
              refine ⟨24712277626812572037275701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32949703502416762716367601 24712277626812572037275701)
              ·
                refine ⟨2316776027513678628494597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24712277626812572037275701 2316776027513678628494597)
                ·
                  refine ⟨434395505158814742842737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316776027513678628494597 434395505158814742842737)
                  ·
                    rfl

theorem cell20_951730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_951730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951730 prefixEnd_951730 := by exact prefixLift 951730
  have htrace : WordTrace (prefixWord ++ tailWord_951730) baseStart_951730 baseEnd_951730 := by
    simpa [prefixWord, tailWord_951730, baseEnd_951730] using wordTrace_append hprefix tailTrace_951730
  have hstable : (prefixWord ++ tailWord_951730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951730).length < 2 ^ (prefixWord ++ tailWord_951730).sum := by decide
  have hdescent : baseEnd_951730 < baseStart_951730 := by decide
  rcases family_descends (prefixWord ++ tailWord_951730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951781 : List Nat := [1, 3, 1, 5, 1, 1, 4, 2, 2]
def baseStart_951781 : Nat := 118140960795 + 951781 * 2 ^ 59
def prefixEnd_951781 : Nat := 4983230072969 + 3 ^ 40 * 951781 * 2
def baseEnd_951781 : Nat := 434418782948485232142529

theorem tailTrace_951781 : CollatzResearch.WordTrace tailWord_951781 prefixEnd_951781 434418782948485232142529 := by
  unfold tailWord_951781
  simp only [CollatzResearch.WordTrace]
  refine ⟨34714304964867463098543197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23142869976578308732362131 34714304964867463098543197)
  ·
    refine ⟨13017864361825298661953699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34714304964867463098543197 13017864361825298661953699)
    ·
      refine ⟨19526796542737947992930549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13017864361825298661953699 19526796542737947992930549)
      ·
        refine ⟨1830637175881682624337239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19526796542737947992930549 1830637175881682624337239)
        ·
          refine ⟨2745955763822523936505859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830637175881682624337239 2745955763822523936505859)
          ·
            refine ⟨4118933645733785904758789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745955763822523936505859 4118933645733785904758789)
            ·
              refine ⟨772300058575084857142273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4118933645733785904758789 772300058575084857142273)
              ·
                refine ⟨579225043931313642856705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772300058575084857142273 579225043931313642856705)
                ·
                  refine ⟨434418782948485232142529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579225043931313642856705 434418782948485232142529)
                  ·
                    rfl

theorem cell20_951781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_951781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951781 prefixEnd_951781 := by exact prefixLift 951781
  have htrace : WordTrace (prefixWord ++ tailWord_951781) baseStart_951781 baseEnd_951781 := by
    simpa [prefixWord, tailWord_951781, baseEnd_951781] using wordTrace_append hprefix tailTrace_951781
  have hstable : (prefixWord ++ tailWord_951781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951781).length < 2 ^ (prefixWord ++ tailWord_951781).sum := by decide
  have hdescent : baseEnd_951781 < baseStart_951781 := by decide
  rcases family_descends (prefixWord ++ tailWord_951781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951792 : List Nat := [2, 1, 1, 1, 3, 6, 1, 5]
def baseStart_951792 : Nat := 118140960795 + 951792 * 2 ^ 59
def prefixEnd_951792 : Nat := 4983230072969 + 3 ^ 40 * 951792 * 2
def baseEnd_951792 : Nat := 144807934549406027591939

theorem tailTrace_951792 : CollatzResearch.WordTrace tailWord_951792 prefixEnd_951792 144807934549406027591939 := by
  unfold tailWord_951792
  simp only [CollatzResearch.WordTrace]
  refine ⟨17357353083913805988596815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23143137445218407984795753 17357353083913805988596815)
  ·
    refine ⟨26036029625870708982895223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17357353083913805988596815 26036029625870708982895223)
    ·
      refine ⟨39054044438806063474342835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26036029625870708982895223 39054044438806063474342835)
      ·
        refine ⟨58581066658209095211514253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39054044438806063474342835 58581066658209095211514253)
        ·
          refine ⟨21967899996828410704317845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58581066658209095211514253 21967899996828410704317845)
          ·
            refine ⟨1029745312351331751764899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21967899996828410704317845 1029745312351331751764899)
            ·
              refine ⟨1544617968526997627647349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029745312351331751764899 1544617968526997627647349)
              ·
                refine ⟨144807934549406027591939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1544617968526997627647349 144807934549406027591939)
                ·
                  rfl

theorem cell20_951792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_951792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951792 prefixEnd_951792 := by exact prefixLift 951792
  have htrace : WordTrace (prefixWord ++ tailWord_951792) baseStart_951792 baseEnd_951792 := by
    simpa [prefixWord, tailWord_951792, baseEnd_951792] using wordTrace_append hprefix tailTrace_951792
  have hstable : (prefixWord ++ tailWord_951792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951792).length < 2 ^ (prefixWord ++ tailWord_951792).sum := by decide
  have hdescent : baseEnd_951792 < baseStart_951792 := by decide
  rcases family_descends (prefixWord ++ tailWord_951792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951809 : List Nat := [1, 2, 4, 1, 4, 1, 3, 4]
def baseStart_951809 : Nat := 118140960795 + 951809 * 2 ^ 59
def prefixEnd_951809 : Nat := 4983230072969 + 3 ^ 40 * 951809 * 2
def baseEnd_951809 : Nat := 144810520970480526403027

theorem tailTrace_951809 : CollatzResearch.WordTrace tailWord_951809 prefixEnd_951809 144810520970480526403027 := by
  unfold tailWord_951809
  simp only [CollatzResearch.WordTrace]
  refine ⟨34715326208766023880562481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23143550805844015920374987 34715326208766023880562481)
  ·
    refine ⟨26036494656574517910421861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34715326208766023880562481 26036494656574517910421861)
    ·
      refine ⟨4881842748107722108204099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26036494656574517910421861 4881842748107722108204099)
      ·
        refine ⟨7322764122161583162306149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881842748107722108204099 7322764122161583162306149)
        ·
          refine ⟨1373018272905296842932403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7322764122161583162306149 1373018272905296842932403)
          ·
            refine ⟨2059527409357945264398605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373018272905296842932403 2059527409357945264398605)
            ·
              refine ⟨772322778509229474149477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2059527409357945264398605 772322778509229474149477)
              ·
                refine ⟨144810520970480526403027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772322778509229474149477 144810520970480526403027)
                ·
                  rfl

theorem cell20_951809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_951809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951809 prefixEnd_951809 := by exact prefixLift 951809
  have htrace : WordTrace (prefixWord ++ tailWord_951809) baseStart_951809 baseEnd_951809 := by
    simpa [prefixWord, tailWord_951809, baseEnd_951809] using wordTrace_append hprefix tailTrace_951809
  have hstable : (prefixWord ++ tailWord_951809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951809).length < 2 ^ (prefixWord ++ tailWord_951809).sum := by decide
  have hdescent : baseEnd_951809 < baseStart_951809 := by decide
  rcases family_descends (prefixWord ++ tailWord_951809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951837 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_951837 : Nat := 118140960795 + 951837 * 2 ^ 59
def prefixEnd_951837 : Nat := 4983230072969 + 3 ^ 40 * 951837 * 2
def baseEnd_951837 : Nat := 434444342874397926275633

theorem tailTrace_951837 : CollatzResearch.WordTrace tailWord_951837 prefixEnd_951837 434444342874397926275633 := by
  unfold tailWord_951837
  simp only [CollatzResearch.WordTrace]
  refine ⟨34716347452664584662581765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23144231635109723108387843 34716347452664584662581765)
  ·
    refine ⟨6509315147374609624234081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34716347452664584662581765 6509315147374609624234081)
    ·
      refine ⟨4881986360530957218175561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6509315147374609624234081 4881986360530957218175561)
      ·
        refine ⟨3661489770398217913631671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4881986360530957218175561 3661489770398217913631671)
        ·
          refine ⟨5492234655597326870447507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661489770398217913631671 5492234655597326870447507)
          ·
            refine ⟨8238351983395990305671261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492234655597326870447507 8238351983395990305671261)
            ·
              refine ⟨3089381993773496364626723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8238351983395990305671261 3089381993773496364626723)
              ·
                refine ⟨4634072990660244546940085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089381993773496364626723 4634072990660244546940085)
                ·
                  refine ⟨434444342874397926275633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634072990660244546940085 434444342874397926275633)
                  ·
                    rfl

theorem cell20_951837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_951837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951837 prefixEnd_951837 := by exact prefixLift 951837
  have htrace : WordTrace (prefixWord ++ tailWord_951837) baseStart_951837 baseEnd_951837 := by
    simpa [prefixWord, tailWord_951837, baseEnd_951837] using wordTrace_append hprefix tailTrace_951837
  have hstable : (prefixWord ++ tailWord_951837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951837).length < 2 ^ (prefixWord ++ tailWord_951837).sum := by decide
  have hdescent : baseEnd_951837 < baseStart_951837 := by decide
  rcases family_descends (prefixWord ++ tailWord_951837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951840 : List Nat := [2, 1, 1, 6, 1, 1, 2, 4, 2]
def baseStart_951840 : Nat := 118140960795 + 951840 * 2 ^ 59
def prefixEnd_951840 : Nat := 4983230072969 + 3 ^ 40 * 951840 * 2
def baseEnd_951840 : Nat := 434445712156143249175621

theorem tailTrace_951840 : CollatzResearch.WordTrace tailWord_951840 prefixEnd_951840 434445712156143249175621 := by
  unfold tailWord_951840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358228435826858087470487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23144304581102477449960649 17358228435826858087470487)
  ·
    refine ⟨26037342653740287131205731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17358228435826858087470487 26037342653740287131205731)
    ·
      refine ⟨39056013980610430696808597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26037342653740287131205731 39056013980610430696808597)
      ·
        refine ⟨1830750655341113938912903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39056013980610430696808597 1830750655341113938912903)
        ·
          refine ⟨2746125983011670908369355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830750655341113938912903 2746125983011670908369355)
          ·
            refine ⟨4119188974517506362554033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746125983011670908369355 4119188974517506362554033)
            ·
              refine ⟨3089391730888129771915525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119188974517506362554033 3089391730888129771915525)
              ·
                refine ⟨579260949541524332234161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3089391730888129771915525 579260949541524332234161)
                ·
                  refine ⟨434445712156143249175621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579260949541524332234161 434445712156143249175621)
                  ·
                    rfl

theorem cell20_951840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_951840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951840 prefixEnd_951840 := by exact prefixLift 951840
  have htrace : WordTrace (prefixWord ++ tailWord_951840) baseStart_951840 baseEnd_951840 := by
    simpa [prefixWord, tailWord_951840, baseEnd_951840] using wordTrace_append hprefix tailTrace_951840
  have hstable : (prefixWord ++ tailWord_951840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951840).length < 2 ^ (prefixWord ++ tailWord_951840).sum := by decide
  have hdescent : baseEnd_951840 < baseStart_951840 := by decide
  rcases family_descends (prefixWord ++ tailWord_951840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951868 : List Nat := [2, 2, 2, 2, 4, 1, 1, 6]
def baseStart_951868 : Nat := 118140960795 + 951868 * 2 ^ 59
def prefixEnd_951868 : Nat := 4983230072969 + 3 ^ 40 * 951868 * 2
def baseEnd_951868 : Nat := 144819497373033198747391

theorem tailTrace_951868 : CollatzResearch.WordTrace tailWord_951868 prefixEnd_951868 144819497373033198747391 := by
  unfold tailWord_951868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358739057776138478480129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23144985410368184637973505 17358739057776138478480129)
  ·
    refine ⟨13019054293332103858860097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17358739057776138478480129 13019054293332103858860097)
    ·
      refine ⟨9764290719999077894145073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13019054293332103858860097 9764290719999077894145073)
      ·
        refine ⟨7323218039999308420608805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9764290719999077894145073 7323218039999308420608805)
        ·
          refine ⟨1373103382499870328864151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7323218039999308420608805 1373103382499870328864151)
          ·
            refine ⟨2059655073749805493296227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373103382499870328864151 2059655073749805493296227)
            ·
              refine ⟨3089482610624708239944341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059655073749805493296227 3089482610624708239944341)
              ·
                refine ⟨144819497373033198747391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3089482610624708239944341 144819497373033198747391)
                ·
                  rfl

theorem cell20_951868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_951868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951868 prefixEnd_951868 := by exact prefixLift 951868
  have htrace : WordTrace (prefixWord ++ tailWord_951868) baseStart_951868 baseEnd_951868 := by
    simpa [prefixWord, tailWord_951868, baseEnd_951868] using wordTrace_append hprefix tailTrace_951868
  have hstable : (prefixWord ++ tailWord_951868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951868).length < 2 ^ (prefixWord ++ tailWord_951868).sum := by decide
  have hdescent : baseEnd_951868 < baseStart_951868 := by decide
  rcases family_descends (prefixWord ++ tailWord_951868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951885 : List Nat := [1, 6, 1, 1, 3, 2, 6]
def baseStart_951885 : Nat := 118140960795 + 951885 * 2 ^ 59
def prefixEnd_951885 : Nat := 4983230072969 + 3 ^ 40 * 951885 * 2
def baseEnd_951885 : Nat := 48274027931369232519493

theorem tailTrace_951885 : CollatzResearch.WordTrace tailWord_951885 prefixEnd_951885 48274027931369232519493 := by
  unfold tailWord_951885
  simp only [CollatzResearch.WordTrace]
  refine ⟨34718098156490688860329109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23145398770993792573552739 34718098156490688860329109)
  ·
    refine ⟨1627410851085501040327927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34718098156490688860329109 1627410851085501040327927)
    ·
      refine ⟨2441116276628251560491891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627410851085501040327927 2441116276628251560491891)
      ·
        refine ⟨3661674414942377340737837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441116276628251560491891 3661674414942377340737837)
        ·
          refine ⟨1373127905603391502776689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3661674414942377340737837 1373127905603391502776689)
          ·
            refine ⟨1029845929202543627082517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373127905603391502776689 1029845929202543627082517)
            ·
              refine ⟨48274027931369232519493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1029845929202543627082517 48274027931369232519493)
              ·
                rfl

theorem cell20_951885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 6].length) (baseStart_951885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951885 prefixEnd_951885 := by exact prefixLift 951885
  have htrace : WordTrace (prefixWord ++ tailWord_951885) baseStart_951885 baseEnd_951885 := by
    simpa [prefixWord, tailWord_951885, baseEnd_951885] using wordTrace_append hprefix tailTrace_951885
  have hstable : (prefixWord ++ tailWord_951885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951885).length < 2 ^ (prefixWord ++ tailWord_951885).sum := by decide
  have hdescent : baseEnd_951885 < baseStart_951885 := by decide
  rcases family_descends (prefixWord ++ tailWord_951885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951909 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 3]
def baseStart_951909 : Nat := 118140960795 + 951909 * 2 ^ 59
def prefixEnd_951909 : Nat := 4983230072969 + 3 ^ 40 * 951909 * 2
def baseEnd_951909 : Nat := 434477205636285675875339

theorem tailTrace_951909 : CollatzResearch.WordTrace tailWord_951909 prefixEnd_951909 434477205636285675875339 := by
  unfold tailWord_951909
  simp only [CollatzResearch.WordTrace]
  refine ⟨34718973508403740959202781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23145982338935827306135187 34718973508403740959202781)
  ·
    refine ⟨13019615065651402859701043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34718973508403740959202781 13019615065651402859701043)
    ·
      refine ⟨19529422598477104289551565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13019615065651402859701043 19529422598477104289551565)
      ·
        refine ⟨7323533474428914108581837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19529422598477104289551565 7323533474428914108581837)
        ·
          refine ⟨2746325052910842790718189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7323533474428914108581837 2746325052910842790718189)
          ·
            refine ⟨1029871894841566046519321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2746325052910842790718189 1029871894841566046519321)
            ·
              refine ⟨772403921131174534889491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029871894841566046519321 772403921131174534889491)
              ·
                refine ⟨1158605881696761802334237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772403921131174534889491 1158605881696761802334237)
                ·
                  refine ⟨434477205636285675875339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1158605881696761802334237 434477205636285675875339)
                  ·
                    rfl

theorem cell20_951909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_951909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951909 prefixEnd_951909 := by exact prefixLift 951909
  have htrace : WordTrace (prefixWord ++ tailWord_951909) baseStart_951909 baseEnd_951909 := by
    simpa [prefixWord, tailWord_951909, baseEnd_951909] using wordTrace_append hprefix tailTrace_951909
  have hstable : (prefixWord ++ tailWord_951909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951909).length < 2 ^ (prefixWord ++ tailWord_951909).sum := by decide
  have hdescent : baseEnd_951909 < baseStart_951909 := by decide
  rcases family_descends (prefixWord ++ tailWord_951909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951944 : List Nat := [2, 1, 3, 5, 1, 8]
def baseStart_951944 : Nat := 118140960795 + 951944 * 2 ^ 59
def prefixEnd_951944 : Nat := 4983230072969 + 3 ^ 40 * 951944 * 2
def baseEnd_951944 : Nat := 16092340021851152211427

theorem tailTrace_951944 : CollatzResearch.WordTrace tailWord_951944 prefixEnd_951944 16092340021851152211427 := by
  unfold tailWord_951944
  simp only [CollatzResearch.WordTrace]
  refine ⟨17360125031638470968363443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23146833375517961291151257 17360125031638470968363443)
  ·
    refine ⟨26040187547457706452545165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17360125031638470968363443 26040187547457706452545165)
    ·
      refine ⟨9765070330296639919704437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26040187547457706452545165 9765070330296639919704437)
      ·
        refine ⟨915475343465309992472291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9765070330296639919704437 915475343465309992472291)
        ·
          refine ⟨1373213015197964988708437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915475343465309992472291 1373213015197964988708437)
          ·
            refine ⟨16092340021851152211427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1373213015197964988708437 16092340021851152211427)
            ·
              rfl

theorem cell20_951944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 8].length) (baseStart_951944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_951944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_951944 prefixEnd_951944 := by exact prefixLift 951944
  have htrace : WordTrace (prefixWord ++ tailWord_951944) baseStart_951944 baseEnd_951944 := by
    simpa [prefixWord, tailWord_951944, baseEnd_951944] using wordTrace_append hprefix tailTrace_951944
  have hstable : (prefixWord ++ tailWord_951944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951944).length < 2 ^ (prefixWord ++ tailWord_951944).sum := by decide
  have hdescent : baseEnd_951944 < baseStart_951944 := by decide
  rcases family_descends (prefixWord ++ tailWord_951944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952002 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_952002 : Nat := 118140960795 + 952002 * 2 ^ 59
def prefixEnd_952002 : Nat := 4983230072969 + 3 ^ 40 * 952002 * 2
def baseEnd_952002 : Nat := 434519653370390685774959

theorem tailTrace_952002 : CollatzResearch.WordTrace tailWord_952002 prefixEnd_952002 434519653370390685774959 := by
  unfold tailWord_952002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680591374266704460584565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23148243664711211894892173 8680591374266704460584565)
  ·
    refine ⟨813805441337503543179803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8680591374266704460584565 813805441337503543179803)
    ·
      refine ⟨1220708162006255314769705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813805441337503543179803 1220708162006255314769705)
      ·
        refine ⟨915531121504691486077279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1220708162006255314769705 915531121504691486077279)
        ·
          refine ⟨1373296682257037229115919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915531121504691486077279 1373296682257037229115919)
          ·
            refine ⟨2059945023385555843673879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373296682257037229115919 2059945023385555843673879)
            ·
              refine ⟨3089917535078333765510819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059945023385555843673879 3089917535078333765510819)
              ·
                refine ⟨4634876302617500648266229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089917535078333765510819 4634876302617500648266229)
                ·
                  refine ⟨434519653370390685774959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634876302617500648266229 434519653370390685774959)
                  ·
                    rfl

theorem cell20_952002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_952002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952002 prefixEnd_952002 := by exact prefixLift 952002
  have htrace : WordTrace (prefixWord ++ tailWord_952002) baseStart_952002 baseEnd_952002 := by
    simpa [prefixWord, tailWord_952002, baseEnd_952002] using wordTrace_append hprefix tailTrace_952002
  have hstable : (prefixWord ++ tailWord_952002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952002).length < 2 ^ (prefixWord ++ tailWord_952002).sum := by decide
  have hdescent : baseEnd_952002 < baseStart_952002 := by decide
  rcases family_descends (prefixWord ++ tailWord_952002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952051 : List Nat := [1, 1, 1, 2, 2, 3, 5, 3, 2]
def baseStart_952051 : Nat := 118140960795 + 952051 * 2 ^ 59
def prefixEnd_952051 : Nat := 4983230072969 + 3 ^ 40 * 952051 * 2
def baseEnd_952051 : Nat := 434542018305564293141425

theorem tailTrace_952051 : CollatzResearch.WordTrace tailWord_952051 prefixEnd_952051 434542018305564293141425 := by
  unfold tailWord_952051
  simp only [CollatzResearch.WordTrace]
  refine ⟨34724152673889299210872007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23149435115926199473914671 34724152673889299210872007)
  ·
    refine ⟨52086229010833948816308011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34724152673889299210872007 52086229010833948816308011)
    ·
      refine ⟨78129343516250923224462017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52086229010833948816308011 78129343516250923224462017)
      ·
        refine ⟨58597007637188192418346513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78129343516250923224462017 58597007637188192418346513)
        ·
          refine ⟨43947755727891144313759885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58597007637188192418346513 43947755727891144313759885)
          ·
            refine ⟨16480408397959179117659957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43947755727891144313759885 16480408397959179117659957)
            ·
              refine ⟨1545038287308673042280621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16480408397959179117659957 1545038287308673042280621)
              ·
                refine ⟨579389357740752390855233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545038287308673042280621 579389357740752390855233)
                ·
                  refine ⟨434542018305564293141425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579389357740752390855233 434542018305564293141425)
                  ·
                    rfl

theorem cell20_952051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 2].length) (baseStart_952051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952051 prefixEnd_952051 := by exact prefixLift 952051
  have htrace : WordTrace (prefixWord ++ tailWord_952051) baseStart_952051 baseEnd_952051 := by
    simpa [prefixWord, tailWord_952051, baseEnd_952051] using wordTrace_append hprefix tailTrace_952051
  have hstable : (prefixWord ++ tailWord_952051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952051).length < 2 ^ (prefixWord ++ tailWord_952051).sum := by decide
  have hdescent : baseEnd_952051 < baseStart_952051 := by decide
  rcases family_descends (prefixWord ++ tailWord_952051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952055 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_952055 : Nat := 118140960795 + 952055 * 2 ^ 59
def prefixEnd_952055 : Nat := 4983230072969 + 3 ^ 40 * 952055 * 2
def baseEnd_952055 : Nat := 434543844014558057008075

theorem tailTrace_952055 : CollatzResearch.WordTrace tailWord_952055 prefixEnd_952055 434543844014558057008075 := by
  unfold tailWord_952055
  simp only [CollatzResearch.WordTrace]
  refine ⟨34724298565874807894017619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23149532377249871929345079 34724298565874807894017619)
  ·
    refine ⟨52086447848812211841026429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34724298565874807894017619 52086447848812211841026429)
    ·
      refine ⟨19532417943304579440384911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52086447848812211841026429 19532417943304579440384911)
      ·
        refine ⟨29298626914956869160577367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532417943304579440384911 29298626914956869160577367)
        ·
          refine ⟨43947940372435303740866051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29298626914956869160577367 43947940372435303740866051)
          ·
            refine ⟨65921910558652955611299077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43947940372435303740866051 65921910558652955611299077)
            ·
              refine ⟨12360358229747429177118577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65921910558652955611299077 12360358229747429177118577)
              ·
                refine ⟨9270268672310571882838933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12360358229747429177118577 9270268672310571882838933)
                ·
                  refine ⟨434543844014558057008075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9270268672310571882838933 434543844014558057008075)
                  ·
                    rfl

theorem cell20_952055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_952055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952055 prefixEnd_952055 := by exact prefixLift 952055
  have htrace : WordTrace (prefixWord ++ tailWord_952055) baseStart_952055 baseEnd_952055 := by
    simpa [prefixWord, tailWord_952055, baseEnd_952055] using wordTrace_append hprefix tailTrace_952055
  have hstable : (prefixWord ++ tailWord_952055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952055).length < 2 ^ (prefixWord ++ tailWord_952055).sum := by decide
  have hdescent : baseEnd_952055 < baseStart_952055 := by decide
  rcases family_descends (prefixWord ++ tailWord_952055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952070 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_952070 : Nat := 118140960795 + 952070 * 2 ^ 59
def prefixEnd_952070 : Nat := 4983230072969 + 3 ^ 40 * 952070 * 2
def baseEnd_952070 : Nat := 434550690423284671508015

theorem tailTrace_952070 : CollatzResearch.WordTrace tailWord_952070 prefixEnd_952070 434550690423284671508015 := by
  unfold tailWord_952070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085151426900639545494177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23149897107213643637209109 1085151426900639545494177)
  ·
    refine ⟨813863570175479659120633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1085151426900639545494177 813863570175479659120633)
    ·
      refine ⟨610397677631609744340475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813863570175479659120633 610397677631609744340475)
      ·
        refine ⟨915596516447414616510713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610397677631609744340475 915596516447414616510713)
        ·
          refine ⟨686697387335560962383035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915596516447414616510713 686697387335560962383035)
          ·
            refine ⟨1030046081003341443574553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686697387335560962383035 1030046081003341443574553)
            ·
              refine ⟨772534560752506082680915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030046081003341443574553 772534560752506082680915)
              ·
                refine ⟨1158801841128759124021373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772534560752506082680915 1158801841128759124021373)
                ·
                  refine ⟨434550690423284671508015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1158801841128759124021373 434550690423284671508015)
                  ·
                    rfl

theorem cell20_952070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_952070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952070 prefixEnd_952070 := by exact prefixLift 952070
  have htrace : WordTrace (prefixWord ++ tailWord_952070) baseStart_952070 baseEnd_952070 := by
    simpa [prefixWord, tailWord_952070, baseEnd_952070] using wordTrace_append hprefix tailTrace_952070
  have hstable : (prefixWord ++ tailWord_952070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952070).length < 2 ^ (prefixWord ++ tailWord_952070).sum := by decide
  have hdescent : baseEnd_952070 < baseStart_952070 := by decide
  rcases family_descends (prefixWord ++ tailWord_952070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952117 : List Nat := [1, 3, 3, 1, 4, 8]
def baseStart_952117 : Nat := 118140960795 + 952117 * 2 ^ 59
def prefixEnd_952117 : Nat := 4983230072969 + 3 ^ 40 * 952117 * 2
def baseEnd_952117 : Nat := 16095264537183755442265

theorem tailTrace_952117 : CollatzResearch.WordTrace tailWord_952117 prefixEnd_952117 16095264537183755442265 := by
  unfold tailWord_952117
  simp only [CollatzResearch.WordTrace]
  refine ⟨34726559891650192482774605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23151039927766794988516403 34726559891650192482774605)
  ·
    refine ⟨13022459959368822181040477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34726559891650192482774605 13022459959368822181040477)
    ·
      refine ⟨4883422484763308317890179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13022459959368822181040477 4883422484763308317890179)
      ·
        refine ⟨7325133727144962476835269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883422484763308317890179 7325133727144962476835269)
        ·
          refine ⟨1373462573839680464406613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7325133727144962476835269 1373462573839680464406613)
          ·
            refine ⟨16095264537183755442265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1373462573839680464406613 16095264537183755442265)
            ·
              rfl

theorem cell20_952117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 8].length) (baseStart_952117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952117 prefixEnd_952117 := by exact prefixLift 952117
  have htrace : WordTrace (prefixWord ++ tailWord_952117) baseStart_952117 baseEnd_952117 := by
    simpa [prefixWord, tailWord_952117, baseEnd_952117] using wordTrace_append hprefix tailTrace_952117
  have hstable : (prefixWord ++ tailWord_952117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952117).length < 2 ^ (prefixWord ++ tailWord_952117).sum := by decide
  have hdescent : baseEnd_952117 < baseStart_952117 := by decide
  rcases family_descends (prefixWord ++ tailWord_952117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952124 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_952124 : Nat := 118140960795 + 952124 * 2 ^ 59
def prefixEnd_952124 : Nat := 4983230072969 + 3 ^ 40 * 952124 * 2
def baseEnd_952124 : Nat := 434575337494700483707793

theorem tailTrace_952124 : CollatzResearch.WordTrace tailWord_952124 prefixEnd_952124 434575337494700483707793 := by
  unfold tailWord_952124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17363407601312416339139713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23151210135083221785519617 17363407601312416339139713)
  ·
    refine ⟨13022555700984312254354785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17363407601312416339139713 13022555700984312254354785)
    ·
      refine ⟨9766916775738234190766089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13022555700984312254354785 9766916775738234190766089)
      ·
        refine ⟨7325187581803675643074567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9766916775738234190766089 7325187581803675643074567)
        ·
          refine ⟨10987781372705513464611851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7325187581803675643074567 10987781372705513464611851)
          ·
            refine ⟨16481672059058270196917777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987781372705513464611851 16481672059058270196917777)
            ·
              refine ⟨12361254044293702647688333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16481672059058270196917777 12361254044293702647688333)
              ·
                refine ⟨4635470266610138492883125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12361254044293702647688333 4635470266610138492883125)
                ·
                  refine ⟨434575337494700483707793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635470266610138492883125 434575337494700483707793)
                  ·
                    rfl

theorem cell20_952124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_952124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952124 prefixEnd_952124 := by exact prefixLift 952124
  have htrace : WordTrace (prefixWord ++ tailWord_952124) baseStart_952124 baseEnd_952124 := by
    simpa [prefixWord, tailWord_952124, baseEnd_952124] using wordTrace_append hprefix tailTrace_952124
  have hstable : (prefixWord ++ tailWord_952124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952124).length < 2 ^ (prefixWord ++ tailWord_952124).sum := by decide
  have hdescent : baseEnd_952124 < baseStart_952124 := by decide
  rcases family_descends (prefixWord ++ tailWord_952124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952148 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_952148 : Nat := 118140960795 + 952148 * 2 ^ 59
def prefixEnd_952148 : Nat := 4983230072969 + 3 ^ 40 * 952148 * 2
def baseEnd_952148 : Nat := 434586291748663066907695

theorem tailTrace_952148 : CollatzResearch.WordTrace tailWord_952148 prefixEnd_952148 434586291748663066907695 := by
  unfold tailWord_952148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17363845277268942388576549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23151793703025256518102065 17363845277268942388576549)
  ·
    refine ⟨3255720989487926697858103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17363845277268942388576549 3255720989487926697858103)
    ·
      refine ⟨4883581484231890046787155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3255720989487926697858103 4883581484231890046787155)
      ·
        refine ⟨7325372226347835070180733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883581484231890046787155 7325372226347835070180733)
        ·
          refine ⟨2747014584880438151317775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7325372226347835070180733 2747014584880438151317775)
          ·
            refine ⟨4120521877320657226976663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747014584880438151317775 4120521877320657226976663)
            ·
              refine ⟨6180782815980985840464995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120521877320657226976663 6180782815980985840464995)
              ·
                refine ⟨9271174223971478760697493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180782815980985840464995 9271174223971478760697493)
                ·
                  refine ⟨434586291748663066907695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9271174223971478760697493 434586291748663066907695)
                  ·
                    rfl

theorem cell20_952148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_952148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952148 prefixEnd_952148 := by exact prefixLift 952148
  have htrace : WordTrace (prefixWord ++ tailWord_952148) baseStart_952148 baseEnd_952148 := by
    simpa [prefixWord, tailWord_952148, baseEnd_952148] using wordTrace_append hprefix tailTrace_952148
  have hstable : (prefixWord ++ tailWord_952148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952148).length < 2 ^ (prefixWord ++ tailWord_952148).sum := by decide
  have hdescent : baseEnd_952148 < baseStart_952148 := by decide
  rcases family_descends (prefixWord ++ tailWord_952148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952182 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_952182 : Nat := 118140960795 + 952182 * 2 ^ 59
def prefixEnd_952182 : Nat := 4983230072969 + 3 ^ 40 * 952182 * 2
def baseEnd_952182 : Nat := 434601810275110059774223

theorem tailTrace_952182 : CollatzResearch.WordTrace tailWord_952182 prefixEnd_952182 434601810275110059774223 := by
  unfold tailWord_952182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170558164775919286493175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23152620424276472389260533 2170558164775919286493175)
  ·
    refine ⟨3255837247163878929739763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170558164775919286493175 3255837247163878929739763)
    ·
      refine ⟨4883755870745818394609645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3255837247163878929739763 4883755870745818394609645)
      ·
        refine ⟨1831408451529681897978617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4883755870745818394609645 1831408451529681897978617)
        ·
          refine ⟨1373556338647261423483963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831408451529681897978617 1373556338647261423483963)
          ·
            refine ⟨2060334507970892135225945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373556338647261423483963 2060334507970892135225945)
            ·
              refine ⟨1545250880978169101419459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060334507970892135225945 1545250880978169101419459)
              ·
                refine ⟨2317876321467253652129189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545250880978169101419459 2317876321467253652129189)
                ·
                  refine ⟨434601810275110059774223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317876321467253652129189 434601810275110059774223)
                  ·
                    rfl

theorem cell20_952182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_952182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952182 prefixEnd_952182 := by exact prefixLift 952182
  have htrace : WordTrace (prefixWord ++ tailWord_952182) baseStart_952182 baseEnd_952182 := by
    simpa [prefixWord, tailWord_952182, baseEnd_952182] using wordTrace_append hprefix tailTrace_952182
  have hstable : (prefixWord ++ tailWord_952182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952182).length < 2 ^ (prefixWord ++ tailWord_952182).sum := by decide
  have hdescent : baseEnd_952182 < baseStart_952182 := by decide
  rcases family_descends (prefixWord ++ tailWord_952182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952206 : List Nat := [4, 1, 1, 5, 1, 2, 2, 4]
def baseStart_952206 : Nat := 118140960795 + 952206 * 2 ^ 59
def prefixEnd_952206 : Nat := 4983230072969 + 3 ^ 40 * 952206 * 2
def baseEnd_952206 : Nat := 144870921509690880991375

theorem tailTrace_952206 : CollatzResearch.WordTrace tailWord_952206 prefixEnd_952206 144870921509690880991375 := by
  unfold tailWord_952206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341225748540970085345559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23153203992218507121842981 4341225748540970085345559)
  ·
    refine ⟨6511838622811455128018339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341225748540970085345559 6511838622811455128018339)
    ·
      refine ⟨9767757934217182692027509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511838622811455128018339 9767757934217182692027509)
      ·
        refine ⟨915727306332860877377579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9767757934217182692027509 915727306332860877377579)
        ·
          refine ⟨1373590959499291316066369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915727306332860877377579 1373590959499291316066369)
          ·
            refine ⟨1030193219624468487049777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373590959499291316066369 1030193219624468487049777)
            ·
              refine ⟨772644914718351365287333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030193219624468487049777 772644914718351365287333)
              ·
                refine ⟨144870921509690880991375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772644914718351365287333 144870921509690880991375)
                ·
                  rfl

theorem cell20_952206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_952206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952206 prefixEnd_952206 := by exact prefixLift 952206
  have htrace : WordTrace (prefixWord ++ tailWord_952206) baseStart_952206 baseEnd_952206 := by
    simpa [prefixWord, tailWord_952206, baseEnd_952206] using wordTrace_append hprefix tailTrace_952206
  have hstable : (prefixWord ++ tailWord_952206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952206).length < 2 ^ (prefixWord ++ tailWord_952206).sum := by decide
  have hdescent : baseEnd_952206 < baseStart_952206 := by decide
  rcases family_descends (prefixWord ++ tailWord_952206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952210 : List Nat := [3, 2, 3, 2, 1, 2, 1, 6]
def baseStart_952210 : Nat := 118140960795 + 952210 * 2 ^ 59
def prefixEnd_952210 : Nat := 4983230072969 + 3 ^ 40 * 952210 * 2
def baseEnd_952210 : Nat := 144871530079355468946925

theorem tailTrace_952210 : CollatzResearch.WordTrace tailWord_952210 prefixEnd_952210 144871530079355468946925 := by
  unfold tailWord_952210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682487970078317341477521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23153301253542179577273389 8682487970078317341477521)
  ·
    refine ⟨6511865977558738006108141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8682487970078317341477521 6511865977558738006108141)
    ·
      refine ⟨2441949741584526752290553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6511865977558738006108141 2441949741584526752290553)
      ·
        refine ⟨1831462306188395064217915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441949741584526752290553 1831462306188395064217915)
        ·
          refine ⟨2747193459282592596326873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831462306188395064217915 2747193459282592596326873)
          ·
            refine ⟨2060395094461944447245155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2747193459282592596326873 2060395094461944447245155)
            ·
              refine ⟨3090592641692916670867733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060395094461944447245155 3090592641692916670867733)
              ·
                refine ⟨144871530079355468946925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3090592641692916670867733 144871530079355468946925)
                ·
                  rfl

theorem cell20_952210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_952210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952210 prefixEnd_952210 := by exact prefixLift 952210
  have htrace : WordTrace (prefixWord ++ tailWord_952210) baseStart_952210 baseEnd_952210 := by
    simpa [prefixWord, tailWord_952210, baseEnd_952210] using wordTrace_append hprefix tailTrace_952210
  have hstable : (prefixWord ++ tailWord_952210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952210).length < 2 ^ (prefixWord ++ tailWord_952210).sum := by decide
  have hdescent : baseEnd_952210 < baseStart_952210 := by decide
  rcases family_descends (prefixWord ++ tailWord_952210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952216 : List Nat := [2, 1, 2, 6, 2, 1, 1, 3, 2]
def baseStart_952216 : Nat := 118140960795 + 952216 * 2 ^ 59
def prefixEnd_952216 : Nat := 4983230072969 + 3 ^ 40 * 952216 * 2
def baseEnd_952216 : Nat := 434617328801557052640751

theorem tailTrace_952216 : CollatzResearch.WordTrace tailWord_952216 prefixEnd_952216 434617328801557052640751 := by
  unfold tailWord_952216
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365085359145766195314251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23153447145527688260419001 17365085359145766195314251)
  ·
    refine ⟨26047628038718649292971377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17365085359145766195314251 26047628038718649292971377)
    ·
      refine ⟨19535721029038986969728533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26047628038718649292971377 19535721029038986969728533)
      ·
        refine ⟨915736923236202514206025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19535721029038986969728533 915736923236202514206025)
        ·
          refine ⟨686802692427151885654519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915736923236202514206025 686802692427151885654519)
          ·
            refine ⟨1030204038640727828481779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686802692427151885654519 1030204038640727828481779)
            ·
              refine ⟨1545306057961091742722669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030204038640727828481779 1545306057961091742722669)
              ·
                refine ⟨579489771735409403521001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545306057961091742722669 579489771735409403521001)
                ·
                  refine ⟨434617328801557052640751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579489771735409403521001 434617328801557052640751)
                  ·
                    rfl

theorem cell20_952216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_952216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952216 prefixEnd_952216 := by exact prefixLift 952216
  have htrace : WordTrace (prefixWord ++ tailWord_952216) baseStart_952216 baseEnd_952216 := by
    simpa [prefixWord, tailWord_952216, baseEnd_952216] using wordTrace_append hprefix tailTrace_952216
  have hstable : (prefixWord ++ tailWord_952216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952216).length < 2 ^ (prefixWord ++ tailWord_952216).sum := by decide
  have hdescent : baseEnd_952216 < baseStart_952216 := by decide
  rcases family_descends (prefixWord ++ tailWord_952216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952220 : List Nat := [2, 2, 3, 3, 1, 1, 3, 3, 2]
def baseStart_952220 : Nat := 118140960795 + 952220 * 2 ^ 59
def prefixEnd_952220 : Nat := 4983230072969 + 3 ^ 40 * 952220 * 2
def baseEnd_952220 : Nat := 434619154510550816507401

theorem tailTrace_952220 : CollatzResearch.WordTrace tailWord_952220 prefixEnd_952220 434619154510550816507401 := by
  unfold tailWord_952220
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365158305138520536887057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23153544406851360715849409 17365158305138520536887057)
  ·
    refine ⟨13023868728853890402665293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17365158305138520536887057 13023868728853890402665293)
    ·
      refine ⟨4883950773320208900999485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13023868728853890402665293 4883950773320208900999485)
      ·
        refine ⟨1831481539995078337874807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4883950773320208900999485 1831481539995078337874807)
        ·
          refine ⟨2747222309992617506812211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831481539995078337874807 2747222309992617506812211)
          ·
            refine ⟨4120833464988926260218317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747222309992617506812211 4120833464988926260218317)
            ·
              refine ⟨1545312549370847347581869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4120833464988926260218317 1545312549370847347581869)
              ·
                refine ⟨579492206014067755343201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545312549370847347581869 579492206014067755343201)
                ·
                  refine ⟨434619154510550816507401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579492206014067755343201 434619154510550816507401)
                  ·
                    rfl

theorem cell20_952220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_952220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952220 prefixEnd_952220 := by exact prefixLift 952220
  have htrace : WordTrace (prefixWord ++ tailWord_952220) baseStart_952220 baseEnd_952220 := by
    simpa [prefixWord, tailWord_952220, baseEnd_952220] using wordTrace_append hprefix tailTrace_952220
  have hstable : (prefixWord ++ tailWord_952220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952220).length < 2 ^ (prefixWord ++ tailWord_952220).sum := by decide
  have hdescent : baseEnd_952220 < baseStart_952220 := by decide
  rcases family_descends (prefixWord ++ tailWord_952220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952231 : List Nat := [1, 1, 6, 1, 2, 1, 8]
def baseStart_952231 : Nat := 118140960795 + 952231 * 2 ^ 59
def prefixEnd_952231 : Nat := 4983230072969 + 3 ^ 40 * 952231 * 2
def baseEnd_952231 : Nat := 48291575023364851904521

theorem tailTrace_952231 : CollatzResearch.WordTrace tailWord_952231 prefixEnd_952231 48291575023364851904521 := by
  unfold tailWord_952231
  simp only [CollatzResearch.WordTrace]
  refine ⟨34730717813237189952424547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23153811875491459968283031 34730717813237189952424547)
  ·
    refine ⟨52096076719855784928636821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34730717813237189952424547 52096076719855784928636821)
    ·
      refine ⟨2442003596243239918529851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52096076719855784928636821 2442003596243239918529851)
      ·
        refine ⟨3663005394364859877794777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442003596243239918529851 3663005394364859877794777)
        ·
          refine ⟨2747254045773644908346083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663005394364859877794777 2747254045773644908346083)
          ·
            refine ⟨4120881068660467362519125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747254045773644908346083 4120881068660467362519125)
            ·
              refine ⟨48291575023364851904521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4120881068660467362519125 48291575023364851904521)
              ·
                rfl

theorem cell20_952231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_952231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952231 prefixEnd_952231 := by exact prefixLift 952231
  have htrace : WordTrace (prefixWord ++ tailWord_952231) baseStart_952231 baseEnd_952231 := by
    simpa [prefixWord, tailWord_952231, baseEnd_952231] using wordTrace_append hprefix tailTrace_952231
  have hstable : (prefixWord ++ tailWord_952231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952231).length < 2 ^ (prefixWord ++ tailWord_952231).sum := by decide
  have hdescent : baseEnd_952231 < baseStart_952231 := by decide
  rcases family_descends (prefixWord ++ tailWord_952231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952241 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 4]
def baseStart_952241 : Nat := 118140960795 + 952241 * 2 ^ 59
def prefixEnd_952241 : Nat := 4983230072969 + 3 ^ 40 * 952241 * 2
def baseEnd_952241 : Nat := 434628739482768076807315

theorem tailTrace_952241 : CollatzResearch.WordTrace tailWord_952241 prefixEnd_952241 434628739482768076807315 := by
  unfold tailWord_952241
  simp only [CollatzResearch.WordTrace]
  refine ⟨34731082543200961660288577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23154055028800641106859051 34731082543200961660288577)
  ·
    refine ⟨26048311907400721245216433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34731082543200961660288577 26048311907400721245216433)
    ·
      refine ⟨19536233930550540933912325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26048311907400721245216433 19536233930550540933912325)
      ·
        refine ⟨3663043861978226425108561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19536233930550540933912325 3663043861978226425108561)
        ·
          refine ⟨2747282896483669818831421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663043861978226425108561 2747282896483669818831421)
          ·
            refine ⟨1030231086181376182061783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2747282896483669818831421 1030231086181376182061783)
            ·
              refine ⟨1545346629272064273092675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030231086181376182061783 1545346629272064273092675)
              ·
                refine ⟨2318019943908096409639013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545346629272064273092675 2318019943908096409639013)
                ·
                  refine ⟨434628739482768076807315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2318019943908096409639013 434628739482768076807315)
                  ·
                    rfl

theorem cell20_952241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_952241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952241 prefixEnd_952241 := by exact prefixLift 952241
  have htrace : WordTrace (prefixWord ++ tailWord_952241) baseStart_952241 baseEnd_952241 := by
    simpa [prefixWord, tailWord_952241, baseEnd_952241] using wordTrace_append hprefix tailTrace_952241
  have hstable : (prefixWord ++ tailWord_952241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952241).length < 2 ^ (prefixWord ++ tailWord_952241).sum := by decide
  have hdescent : baseEnd_952241 < baseStart_952241 := by decide
  rcases family_descends (prefixWord ++ tailWord_952241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952348 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_952348 : Nat := 118140960795 + 952348 * 2 ^ 59
def prefixEnd_952348 : Nat := 4983230072969 + 3 ^ 40 * 952348 * 2
def baseEnd_952348 : Nat := 434677577198351260240211

theorem tailTrace_952348 : CollatzResearch.WordTrace tailWord_952348 prefixEnd_952348 434677577198351260240211 := by
  unfold tailWord_952348
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367492576906659467216849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23156656769208879289622465 17367492576906659467216849)
  ·
    refine ⟨13025619432679994600412637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17367492576906659467216849 13025619432679994600412637)
    ·
      refine ⟨4884607287254997975154739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13025619432679994600412637 4884607287254997975154739)
      ·
        refine ⟨7326910930882496962732109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884607287254997975154739 7326910930882496962732109)
        ·
          refine ⟨2747591599080936361024541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7326910930882496962732109 2747591599080936361024541)
          ·
            refine ⟨1030346849655351135384203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2747591599080936361024541 1030346849655351135384203)
            ·
              refine ⟨1545520274483026703076305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030346849655351135384203 1545520274483026703076305)
              ·
                refine ⟨1159140205862270027307229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545520274483026703076305 1159140205862270027307229)
                ·
                  refine ⟨434677577198351260240211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159140205862270027307229 434677577198351260240211)
                  ·
                    rfl

theorem cell20_952348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_952348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952348 prefixEnd_952348 := by exact prefixLift 952348
  have htrace : WordTrace (prefixWord ++ tailWord_952348) baseStart_952348 baseEnd_952348 := by
    simpa [prefixWord, tailWord_952348, baseEnd_952348] using wordTrace_append hprefix tailTrace_952348
  have hstable : (prefixWord ++ tailWord_952348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952348).length < 2 ^ (prefixWord ++ tailWord_952348).sum := by decide
  have hdescent : baseEnd_952348 < baseStart_952348 := by decide
  rcases family_descends (prefixWord ++ tailWord_952348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952383 : List Nat := [1, 1, 2, 2, 3, 1, 6, 4]
def baseStart_952383 : Nat := 118140960795 + 952383 * 2 ^ 59
def prefixEnd_952383 : Nat := 4983230072969 + 3 ^ 40 * 952383 * 2
def baseEnd_952383 : Nat := 144897850717348898024467

theorem tailTrace_952383 : CollatzResearch.WordTrace tailWord_952383 prefixEnd_952383 144897850717348898024467 := by
  unfold tailWord_952383
  simp only [CollatzResearch.WordTrace]
  refine ⟨34736261708686519911957803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23157507805791013274638535 34736261708686519911957803)
  ·
    refine ⟨52104392563029779867936705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34736261708686519911957803 52104392563029779867936705)
    ·
      refine ⟨39078294422272334900952529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52104392563029779867936705 39078294422272334900952529)
      ·
        refine ⟨29308720816704251175714397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39078294422272334900952529 29308720816704251175714397)
        ·
          refine ⟨10990770306264094190892899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29308720816704251175714397 10990770306264094190892899)
          ·
            refine ⟨16486155459396141286339349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990770306264094190892899 16486155459396141286339349)
            ·
              refine ⟨772788537159194122797157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16486155459396141286339349 772788537159194122797157)
              ·
                refine ⟨144897850717348898024467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772788537159194122797157 144897850717348898024467)
                ·
                  rfl

theorem cell20_952383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_952383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952383 prefixEnd_952383 := by exact prefixLift 952383
  have htrace : WordTrace (prefixWord ++ tailWord_952383) baseStart_952383 baseEnd_952383 := by
    simpa [prefixWord, tailWord_952383, baseEnd_952383] using wordTrace_append hprefix tailTrace_952383
  have hstable : (prefixWord ++ tailWord_952383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952383).length < 2 ^ (prefixWord ++ tailWord_952383).sum := by decide
  have hdescent : baseEnd_952383 < baseStart_952383 := by decide
  rcases family_descends (prefixWord ++ tailWord_952383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952406 : List Nat := [5, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_952406 : Nat := 118140960795 + 952406 * 2 ^ 59
def prefixEnd_952406 : Nat := 4983230072969 + 3 ^ 40 * 952406 * 2
def baseEnd_952406 : Nat := 434704049978760836306641

theorem tailTrace_952406 : CollatzResearch.WordTrace tailWord_952406 prefixEnd_952406 434704049978760836306641 := by
  unfold tailWord_952406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171068786725199677502817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23158067058402129893363381 2171068786725199677502817)
  ·
    refine ⟨1628301590043899758127113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2171068786725199677502817 1628301590043899758127113)
    ·
      refine ⟨1221226192532924818595335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1628301590043899758127113 1221226192532924818595335)
      ·
        refine ⟨1831839288799387227893003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221226192532924818595335 1831839288799387227893003)
        ·
          refine ⟨2747758933199080841839505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831839288799387227893003 2747758933199080841839505)
          ·
            refine ⟨2060819199899310631379629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2747758933199080841839505 2060819199899310631379629)
            ·
              refine ⟨772807199962241486767361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2060819199899310631379629 772807199962241486767361)
              ·
                refine ⟨579605399971681115075521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772807199962241486767361 579605399971681115075521)
                ·
                  refine ⟨434704049978760836306641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579605399971681115075521 434704049978760836306641)
                  ·
                    rfl

theorem cell20_952406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_952406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952406 prefixEnd_952406 := by exact prefixLift 952406
  have htrace : WordTrace (prefixWord ++ tailWord_952406) baseStart_952406 baseEnd_952406 := by
    simpa [prefixWord, tailWord_952406, baseEnd_952406] using wordTrace_append hprefix tailTrace_952406
  have hstable : (prefixWord ++ tailWord_952406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952406).length < 2 ^ (prefixWord ++ tailWord_952406).sum := by decide
  have hdescent : baseEnd_952406 < baseStart_952406 := by decide
  rcases family_descends (prefixWord ++ tailWord_952406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952421 : List Nat := [1, 3, 1, 3, 2, 3, 2, 5]
def baseStart_952421 : Nat := 118140960795 + 952421 * 2 ^ 59
def prefixEnd_952421 : Nat := 4983230072969 + 3 ^ 40 * 952421 * 2
def baseEnd_952421 : Nat := 144903632129162483602193

theorem tailTrace_952421 : CollatzResearch.WordTrace tailWord_952421 prefixEnd_952421 144903632129162483602193 := by
  unfold tailWord_952421
  simp only [CollatzResearch.WordTrace]
  refine ⟨34737647682548852401841117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23158431788365901601227411 34737647682548852401841117)
  ·
    refine ⟨13026617880955819650690419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34737647682548852401841117 13026617880955819650690419)
    ·
      refine ⟨19539926821433729476035629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026617880955819650690419 19539926821433729476035629)
      ·
        refine ⟨7327472558037648553513361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19539926821433729476035629 7327472558037648553513361)
        ·
          refine ⟨5495604418528236415135021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7327472558037648553513361 5495604418528236415135021)
          ·
            refine ⟨2060851656948088655675633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5495604418528236415135021 2060851656948088655675633)
            ·
              refine ⟨1545638742711066491756725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060851656948088655675633 1545638742711066491756725)
              ·
                refine ⟨144903632129162483602193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1545638742711066491756725 144903632129162483602193)
                ·
                  rfl

theorem cell20_952421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_952421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952421 prefixEnd_952421 := by exact prefixLift 952421
  have htrace : WordTrace (prefixWord ++ tailWord_952421) baseStart_952421 baseEnd_952421 := by
    simpa [prefixWord, tailWord_952421, baseEnd_952421] using wordTrace_append hprefix tailTrace_952421
  have hstable : (prefixWord ++ tailWord_952421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952421).length < 2 ^ (prefixWord ++ tailWord_952421).sum := by decide
  have hdescent : baseEnd_952421 < baseStart_952421 := by decide
  rcases family_descends (prefixWord ++ tailWord_952421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952462 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_952462 : Nat := 118140960795 + 952462 * 2 ^ 59
def prefixEnd_952462 : Nat := 4983230072969 + 3 ^ 40 * 952462 * 2
def baseEnd_952462 : Nat := 434729609904673530439745

theorem tailTrace_952462 : CollatzResearch.WordTrace tailWord_952462 prefixEnd_952462 434729609904673530439745 := by
  unfold tailWord_952462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4342392884425039550510455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23159428716933544269389093 4342392884425039550510455)
  ·
    refine ⟨6513589326637559325765683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4342392884425039550510455 6513589326637559325765683)
    ·
      refine ⟨9770383989956338988648525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6513589326637559325765683 9770383989956338988648525)
      ·
        refine ⟨3663893996233627120743197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9770383989956338988648525 3663893996233627120743197)
        ·
          refine ⟨1373960248587610170278699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3663893996233627120743197 1373960248587610170278699)
          ·
            refine ⟨2060940372881415255418049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373960248587610170278699 2060940372881415255418049)
            ·
              refine ⟨1545705279661061441563537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060940372881415255418049 1545705279661061441563537)
              ·
                refine ⟨1159278959745796081172653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545705279661061441563537 1159278959745796081172653)
                ·
                  refine ⟨434729609904673530439745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159278959745796081172653 434729609904673530439745)
                  ·
                    rfl

theorem cell20_952462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_952462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952462 prefixEnd_952462 := by exact prefixLift 952462
  have htrace : WordTrace (prefixWord ++ tailWord_952462) baseStart_952462 baseEnd_952462 := by
    simpa [prefixWord, tailWord_952462, baseEnd_952462] using wordTrace_append hprefix tailTrace_952462
  have hstable : (prefixWord ++ tailWord_952462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952462).length < 2 ^ (prefixWord ++ tailWord_952462).sum := by decide
  have hdescent : baseEnd_952462 < baseStart_952462 := by decide
  rcases family_descends (prefixWord ++ tailWord_952462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952552 : List Nat := [2, 1, 4, 1, 2, 4, 2, 4]
def baseStart_952552 : Nat := 118140960795 + 952552 * 2 ^ 59
def prefixEnd_952552 : Nat := 4983230072969 + 3 ^ 40 * 952552 * 2
def baseEnd_952552 : Nat := 144923562785677739146459

theorem tailTrace_952552 : CollatzResearch.WordTrace tailWord_952552 prefixEnd_952552 144923562785677739146459 := by
  unfold tailWord_952552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17371212822537130887429955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23161617096716174516573273 17371212822537130887429955)
  ·
    refine ⟨26056819233805696331144933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17371212822537130887429955 26056819233805696331144933)
    ·
      refine ⟨4885653606338568062089675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26056819233805696331144933 4885653606338568062089675)
      ·
        refine ⟨7328480409507852093134513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885653606338568062089675 7328480409507852093134513)
        ·
          refine ⟨5496360307130889069850885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7328480409507852093134513 5496360307130889069850885)
          ·
            refine ⟨1030567557587041700597041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5496360307130889069850885 1030567557587041700597041)
            ·
              refine ⟨772925668190281275447781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030567557587041700597041 772925668190281275447781)
              ·
                refine ⟨144923562785677739146459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772925668190281275447781 144923562785677739146459)
                ·
                  rfl

theorem cell20_952552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_952552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952552 prefixEnd_952552 := by exact prefixLift 952552
  have htrace : WordTrace (prefixWord ++ tailWord_952552) baseStart_952552 baseEnd_952552 := by
    simpa [prefixWord, tailWord_952552, baseEnd_952552] using wordTrace_append hprefix tailTrace_952552
  have hstable : (prefixWord ++ tailWord_952552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952552).length < 2 ^ (prefixWord ++ tailWord_952552).sum := by decide
  have hdescent : baseEnd_952552 < baseStart_952552 := by decide
  rcases family_descends (prefixWord ++ tailWord_952552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952556 : List Nat := [2, 2, 1, 1, 2, 3, 3, 6]
def baseStart_952556 : Nat := 118140960795 + 952556 * 2 ^ 59
def prefixEnd_952556 : Nat := 4983230072969 + 3 ^ 40 * 952556 * 2
def baseEnd_952556 : Nat := 144924171355342327102009

theorem tailTrace_952556 : CollatzResearch.WordTrace tailWord_952556 prefixEnd_952556 144924171355342327102009 := by
  unfold tailWord_952556
  simp only [CollatzResearch.WordTrace]
  refine ⟨17371285768529885229002761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23161714358039846972003681 17371285768529885229002761)
  ·
    refine ⟨13028464326397413921752071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17371285768529885229002761 13028464326397413921752071)
    ·
      refine ⟨19542696489596120882628107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13028464326397413921752071 19542696489596120882628107)
      ·
        refine ⟨29314044734394181323942161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19542696489596120882628107 29314044734394181323942161)
        ·
          refine ⟨21985533550795635992956621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29314044734394181323942161 21985533550795635992956621)
          ·
            refine ⟨8244575081548363497358733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21985533550795635992956621 8244575081548363497358733)
            ·
              refine ⟨3091715655580636311509525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8244575081548363497358733 3091715655580636311509525)
              ·
                refine ⟨144924171355342327102009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3091715655580636311509525 144924171355342327102009)
                ·
                  rfl

theorem cell20_952556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_952556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952556 prefixEnd_952556 := by exact prefixLift 952556
  have htrace : WordTrace (prefixWord ++ tailWord_952556) baseStart_952556 baseEnd_952556 := by
    simpa [prefixWord, tailWord_952556, baseEnd_952556] using wordTrace_append hprefix tailTrace_952556
  have hstable : (prefixWord ++ tailWord_952556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952556).length < 2 ^ (prefixWord ++ tailWord_952556).sum := by decide
  have hdescent : baseEnd_952556 < baseStart_952556 := by decide
  rcases family_descends (prefixWord ++ tailWord_952556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952562 : List Nat := [3, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_952562 : Nat := 118140960795 + 952562 * 2 ^ 59
def prefixEnd_952562 : Nat := 4983230072969 + 3 ^ 40 * 952562 * 2
def baseEnd_952562 : Nat := 434775252629517627106003

theorem tailTrace_952562 : CollatzResearch.WordTrace tailWord_952562 prefixEnd_952562 434775252629517627106003 := by
  unfold tailWord_952562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685697593759508370680985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23161860250025355655149293 8685697593759508370680985)
  ·
    refine ⟨6514273195319631278010739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8685697593759508370680985 6514273195319631278010739)
    ·
      refine ⟨9771409792979446917016109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6514273195319631278010739 9771409792979446917016109)
      ·
        refine ⟨3664278672367292593881041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9771409792979446917016109 3664278672367292593881041)
        ·
          refine ⟨2748209004275469445410781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664278672367292593881041 2748209004275469445410781)
          ·
            refine ⟨1030578376603301042029043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2748209004275469445410781 1030578376603301042029043)
            ·
              refine ⟨1545867564904951563043565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030578376603301042029043 1545867564904951563043565)
              ·
                refine ⟨579700336839356836141337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545867564904951563043565 579700336839356836141337)
                ·
                  refine ⟨434775252629517627106003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579700336839356836141337 434775252629517627106003)
                  ·
                    rfl

theorem cell20_952562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_952562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952562 prefixEnd_952562 := by exact prefixLift 952562
  have htrace : WordTrace (prefixWord ++ tailWord_952562) baseStart_952562 baseEnd_952562 := by
    simpa [prefixWord, tailWord_952562, baseEnd_952562] using wordTrace_append hprefix tailTrace_952562
  have hstable : (prefixWord ++ tailWord_952562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952562).length < 2 ^ (prefixWord ++ tailWord_952562).sum := by decide
  have hdescent : baseEnd_952562 < baseStart_952562 := by decide
  rcases family_descends (prefixWord ++ tailWord_952562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952563 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_952563 : Nat := 118140960795 + 952563 * 2 ^ 59
def prefixEnd_952563 : Nat := 4983230072969 + 3 ^ 40 * 952563 * 2
def baseEnd_952563 : Nat := 434775709056766068072665

theorem tailTrace_952563 : CollatzResearch.WordTrace tailWord_952563 prefixEnd_952563 434775709056766068072665 := by
  unfold tailWord_952563
  simp only [CollatzResearch.WordTrace]
  refine ⟨34742826848034410653510343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23161884565356273769006895 34742826848034410653510343)
  ·
    refine ⟨52114240272051615980265515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34742826848034410653510343 52114240272051615980265515)
    ·
      refine ⟨78171360408077423970398273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52114240272051615980265515 78171360408077423970398273)
      ·
        refine ⟨58628520306058067977798705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78171360408077423970398273 58628520306058067977798705)
        ·
          refine ⟨43971390229543550983349029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58628520306058067977798705 43971390229543550983349029)
          ·
            refine ⟨8244635668039415809377943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43971390229543550983349029 8244635668039415809377943)
            ·
              refine ⟨12366953502059123714066915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244635668039415809377943 12366953502059123714066915)
              ·
                refine ⟨18550430253088685571100373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12366953502059123714066915 18550430253088685571100373)
                ·
                  refine ⟨434775709056766068072665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18550430253088685571100373 434775709056766068072665)
                  ·
                    rfl

theorem cell20_952563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_952563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952563 prefixEnd_952563 := by exact prefixLift 952563
  have htrace : WordTrace (prefixWord ++ tailWord_952563) baseStart_952563 baseEnd_952563 := by
    simpa [prefixWord, tailWord_952563, baseEnd_952563] using wordTrace_append hprefix tailTrace_952563
  have hstable : (prefixWord ++ tailWord_952563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952563).length < 2 ^ (prefixWord ++ tailWord_952563).sum := by decide
  have hdescent : baseEnd_952563 < baseStart_952563 := by decide
  rcases family_descends (prefixWord ++ tailWord_952563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952597 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 3]
def baseStart_952597 : Nat := 118140960795 + 952597 * 2 ^ 59
def prefixEnd_952597 : Nat := 4983230072969 + 3 ^ 40 * 952597 * 2
def baseEnd_952597 : Nat := 434791227583213060939193

theorem tailTrace_952597 : CollatzResearch.WordTrace tailWord_952597 prefixEnd_952597 434791227583213060939193 := by
  unfold tailWord_952597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34744066929911234460248045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23162711286607489640165363 34744066929911234460248045)
  ·
    refine ⟨13029025098716712922593017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34744066929911234460248045 13029025098716712922593017)
    ·
      refine ⟨9771768824037534691944763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13029025098716712922593017 9771768824037534691944763)
      ·
        refine ⟨14657653236056302037917145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9771768824037534691944763 14657653236056302037917145)
        ·
          refine ⟨10993239927042226528437859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14657653236056302037917145 10993239927042226528437859)
          ·
            refine ⟨16489859890563339792656789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993239927042226528437859 16489859890563339792656789)
            ·
              refine ⟨772962182370156552780787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16489859890563339792656789 772962182370156552780787)
              ·
                refine ⟨1159443273555234829171181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772962182370156552780787 1159443273555234829171181)
                ·
                  refine ⟨434791227583213060939193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159443273555234829171181 434791227583213060939193)
                  ·
                    rfl

theorem cell20_952597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_952597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952597 prefixEnd_952597 := by exact prefixLift 952597
  have htrace : WordTrace (prefixWord ++ tailWord_952597) baseStart_952597 baseEnd_952597 := by
    simpa [prefixWord, tailWord_952597, baseEnd_952597] using wordTrace_append hprefix tailTrace_952597
  have hstable : (prefixWord ++ tailWord_952597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952597).length < 2 ^ (prefixWord ++ tailWord_952597).sum := by decide
  have hdescent : baseEnd_952597 < baseStart_952597 := by decide
  rcases family_descends (prefixWord ++ tailWord_952597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952638 : List Nat := [4, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_952638 : Nat := 118140960795 + 952638 * 2 ^ 59
def prefixEnd_952638 : Nat := 4983230072969 + 3 ^ 40 * 952638 * 2
def baseEnd_952638 : Nat := 434809941100399140572359

theorem tailTrace_952638 : CollatzResearch.WordTrace tailWord_952638 prefixEnd_952638 434809941100399140572359 := by
  unfold tailWord_952638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4343195290345337307811321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23163708215175132308327045 4343195290345337307811321)
  ·
    refine ⟨3257396467759002980858491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4343195290345337307811321 3257396467759002980858491)
    ·
      refine ⟨4886094701638504471287737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257396467759002980858491 4886094701638504471287737)
      ·
        refine ⟨3664571026228878353465803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4886094701638504471287737 3664571026228878353465803)
        ·
          refine ⟨5496856539343317530198705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664571026228878353465803 5496856539343317530198705)
          ·
            refine ⟨4122642404507488147649029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5496856539343317530198705 4122642404507488147649029)
            ·
              refine ⟨772995450845154027684193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4122642404507488147649029 772995450845154027684193)
              ·
                refine ⟨579746588133865520763145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772995450845154027684193 579746588133865520763145)
                ·
                  refine ⟨434809941100399140572359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579746588133865520763145 434809941100399140572359)
                  ·
                    rfl

theorem cell20_952638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_952638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952638 prefixEnd_952638 := by exact prefixLift 952638
  have htrace : WordTrace (prefixWord ++ tailWord_952638) baseStart_952638 baseEnd_952638 := by
    simpa [prefixWord, tailWord_952638, baseEnd_952638] using wordTrace_append hprefix tailTrace_952638
  have hstable : (prefixWord ++ tailWord_952638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952638).length < 2 ^ (prefixWord ++ tailWord_952638).sum := by decide
  have hdescent : baseEnd_952638 < baseStart_952638 := by decide
  rcases family_descends (prefixWord ++ tailWord_952638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952656 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_952656 : Nat := 118140960795 + 952656 * 2 ^ 59
def prefixEnd_952656 : Nat := 4983230072969 + 3 ^ 40 * 952656 * 2
def baseEnd_952656 : Nat := 434818156790871077972285

theorem tailTrace_952656 : CollatzResearch.WordTrace tailWord_952656 prefixEnd_952656 434818156790871077972285 := by
  unfold tailWord_952656
  simp only [CollatzResearch.WordTrace]
  refine ⟨17373109418348743768322911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23164145891131658357763881 17373109418348743768322911)
  ·
    refine ⟨26059664127523115652484367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17373109418348743768322911 26059664127523115652484367)
    ·
      refine ⟨39089496191284673478726551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26059664127523115652484367 39089496191284673478726551)
      ·
        refine ⟨58634244286927010218089827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39089496191284673478726551 58634244286927010218089827)
        ·
          refine ⟨87951366430390515327134741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58634244286927010218089827 87951366430390515327134741)
          ·
            refine ⟨4122720301424555405959441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87951366430390515327134741 4122720301424555405959441)
            ·
              refine ⟨3092040226068416554469581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122720301424555405959441 3092040226068416554469581)
              ·
                refine ⟨1159515084775656207926093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3092040226068416554469581 1159515084775656207926093)
                ·
                  refine ⟨434818156790871077972285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159515084775656207926093 434818156790871077972285)
                  ·
                    rfl

theorem cell20_952656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_952656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952656 prefixEnd_952656 := by exact prefixLift 952656
  have htrace : WordTrace (prefixWord ++ tailWord_952656) baseStart_952656 baseEnd_952656 := by
    simpa [prefixWord, tailWord_952656, baseEnd_952656] using wordTrace_append hprefix tailTrace_952656
  have hstable : (prefixWord ++ tailWord_952656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952656).length < 2 ^ (prefixWord ++ tailWord_952656).sum := by decide
  have hdescent : baseEnd_952656 < baseStart_952656 := by decide
  rcases family_descends (prefixWord ++ tailWord_952656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952663 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_952663 : Nat := 118140960795 + 952663 * 2 ^ 59
def prefixEnd_952663 : Nat := 4983230072969 + 3 ^ 40 * 952663 * 2
def baseEnd_952663 : Nat := 434821351781610164738923

theorem tailTrace_952663 : CollatzResearch.WordTrace tailWord_952663 prefixEnd_952663 434821351781610164738923 := by
  unfold tailWord_952663
  simp only [CollatzResearch.WordTrace]
  refine ⟨34746474147672127732150643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23164316098448085154767095 34746474147672127732150643)
  ·
    refine ⟨52119711221508191598225965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34746474147672127732150643 52119711221508191598225965)
    ·
      refine ⟨19544891708065571849334737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52119711221508191598225965 19544891708065571849334737)
      ·
        refine ⟨14658668781049178887001053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19544891708065571849334737 14658668781049178887001053)
        ·
          refine ⟨5497000792893442082625395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14658668781049178887001053 5497000792893442082625395)
          ·
            refine ⟨8245501189340163123938093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497000792893442082625395 8245501189340163123938093)
            ·
              refine ⟨3092062946002561171476785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8245501189340163123938093 3092062946002561171476785)
              ·
                refine ⟨2319047209501920878607589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092062946002561171476785 2319047209501920878607589)
                ·
                  refine ⟨434821351781610164738923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2319047209501920878607589 434821351781610164738923)
                  ·
                    rfl

theorem cell20_952663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_952663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952663 prefixEnd_952663 := by exact prefixLift 952663
  have htrace : WordTrace (prefixWord ++ tailWord_952663) baseStart_952663 baseEnd_952663 := by
    simpa [prefixWord, tailWord_952663, baseEnd_952663] using wordTrace_append hprefix tailTrace_952663
  have hstable : (prefixWord ++ tailWord_952663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952663).length < 2 ^ (prefixWord ++ tailWord_952663).sum := by decide
  have hdescent : baseEnd_952663 < baseStart_952663 := by decide
  rcases family_descends (prefixWord ++ tailWord_952663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952701 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_952701 : Nat := 118140960795 + 952701 * 2 ^ 59
def prefixEnd_952701 : Nat := 4983230072969 + 3 ^ 40 * 952701 * 2
def baseEnd_952701 : Nat := 434838696017050921472101

theorem tailTrace_952701 : CollatzResearch.WordTrace tailWord_952701 prefixEnd_952701 434838696017050921472101 := by
  unfold tailWord_952701
  simp only [CollatzResearch.WordTrace]
  refine ⟨34747860121534460222033957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23165240081022973481355971 34747860121534460222033957)
  ·
    refine ⟨6515223772787711291631367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34747860121534460222033957 6515223772787711291631367)
    ·
      refine ⟨9772835659181566937447051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6515223772787711291631367 9772835659181566937447051)
      ·
        refine ⟨14659253488772350406170577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772835659181566937447051 14659253488772350406170577)
        ·
          refine ⟨10994440116579262804627933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14659253488772350406170577 10994440116579262804627933)
          ·
            refine ⟨4122915043717223551735475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10994440116579262804627933 4122915043717223551735475)
            ·
              refine ⟨6184372565575835327603213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122915043717223551735475 6184372565575835327603213)
              ·
                refine ⟨2319139712090938247851205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6184372565575835327603213 2319139712090938247851205)
                ·
                  refine ⟨434838696017050921472101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2319139712090938247851205 434838696017050921472101)
                  ·
                    rfl

theorem cell20_952701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_952701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952701 prefixEnd_952701 := by exact prefixLift 952701
  have htrace : WordTrace (prefixWord ++ tailWord_952701) baseStart_952701 baseEnd_952701 := by
    simpa [prefixWord, tailWord_952701, baseEnd_952701] using wordTrace_append hprefix tailTrace_952701
  have hstable : (prefixWord ++ tailWord_952701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952701).length < 2 ^ (prefixWord ++ tailWord_952701).sum := by decide
  have hdescent : baseEnd_952701 < baseStart_952701 := by decide
  rcases family_descends (prefixWord ++ tailWord_952701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952708 : List Nat := [2, 3, 2, 1, 1, 2, 2, 7]
def baseStart_952708 : Nat := 118140960795 + 952708 * 2 ^ 59
def prefixEnd_952708 : Nat := 4983230072969 + 3 ^ 40 * 952708 * 2
def baseEnd_952708 : Nat := 144947297002596669412913

theorem tailTrace_952708 : CollatzResearch.WordTrace tailWord_952708 prefixEnd_952708 144947297002596669412913 := by
  unfold tailWord_952708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17374057716254550208769389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23165410288339400278359185 17374057716254550208769389)
  ·
    refine ⟨6515271643595456328288521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17374057716254550208769389 6515271643595456328288521)
    ·
      refine ⟨4886453732696592246216391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6515271643595456328288521 4886453732696592246216391)
      ·
        refine ⟨7329680599044888369324587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886453732696592246216391 7329680599044888369324587)
        ·
          refine ⟨10994520898567332553986881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7329680599044888369324587 10994520898567332553986881)
          ·
            refine ⟨8245890673925499415490161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10994520898567332553986881 8245890673925499415490161)
            ·
              refine ⟨6184418005444124561617621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8245890673925499415490161 6184418005444124561617621)
              ·
                refine ⟨144947297002596669412913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6184418005444124561617621 144947297002596669412913)
                ·
                  rfl

theorem cell20_952708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_952708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952708 prefixEnd_952708 := by exact prefixLift 952708
  have htrace : WordTrace (prefixWord ++ tailWord_952708) baseStart_952708 baseEnd_952708 := by
    simpa [prefixWord, tailWord_952708, baseEnd_952708] using wordTrace_append hprefix tailTrace_952708
  have hstable : (prefixWord ++ tailWord_952708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952708).length < 2 ^ (prefixWord ++ tailWord_952708).sum := by decide
  have hdescent : baseEnd_952708 < baseStart_952708 := by decide
  rcases family_descends (prefixWord ++ tailWord_952708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952711 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 3]
def baseStart_952711 : Nat := 118140960795 + 952711 * 2 ^ 59
def prefixEnd_952711 : Nat := 4983230072969 + 3 ^ 40 * 952711 * 2
def baseEnd_952711 : Nat := 434843260289535331138727

theorem tailTrace_952711 : CollatzResearch.WordTrace tailWord_952711 prefixEnd_952711 434843260289535331138727 := by
  unfold tailWord_952711
  simp only [CollatzResearch.WordTrace]
  refine ⟨34748224851498231929897987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23165483234332154619931991 34748224851498231929897987)
  ·
    refine ⟨52122337277247347894846981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34748224851498231929897987 52122337277247347894846981)
    ·
      refine ⟨9772938239483877730283809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52122337277247347894846981 9772938239483877730283809)
      ·
        refine ⟨7329703679612908297712857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9772938239483877730283809 7329703679612908297712857)
        ·
          refine ⟨5497277759709681223284643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7329703679612908297712857 5497277759709681223284643)
          ·
            refine ⟨8245916639564521834926965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497277759709681223284643 8245916639564521834926965)
            ·
              refine ⟨773054684959173922024403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8245916639564521834926965 773054684959173922024403)
              ·
                refine ⟨1159582027438760883036605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773054684959173922024403 1159582027438760883036605)
                ·
                  refine ⟨434843260289535331138727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159582027438760883036605 434843260289535331138727)
                  ·
                    rfl

theorem cell20_952711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 3].length) (baseStart_952711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952711 prefixEnd_952711 := by exact prefixLift 952711
  have htrace : WordTrace (prefixWord ++ tailWord_952711) baseStart_952711 baseEnd_952711 := by
    simpa [prefixWord, tailWord_952711, baseEnd_952711] using wordTrace_append hprefix tailTrace_952711
  have hstable : (prefixWord ++ tailWord_952711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952711).length < 2 ^ (prefixWord ++ tailWord_952711).sum := by decide
  have hdescent : baseEnd_952711 < baseStart_952711 := by decide
  rcases family_descends (prefixWord ++ tailWord_952711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952718 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_952718 : Nat := 118140960795 + 952718 * 2 ^ 59
def prefixEnd_952718 : Nat := 4983230072969 + 3 ^ 40 * 952718 * 2
def baseEnd_952718 : Nat := 434846455280274417905365

theorem tailTrace_952718 : CollatzResearch.WordTrace tailWord_952718 prefixEnd_952718 434846455280274417905365 := by
  unfold tailWord_952718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4343560020309109015675351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23165653441648581416935205 4343560020309109015675351)
  ·
    refine ⟨6515340030463663523513027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4343560020309109015675351 6515340030463663523513027)
    ·
      refine ⟨9773010045695495285269541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6515340030463663523513027 9773010045695495285269541)
      ·
        refine ⟨1832439383567905365988039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9773010045695495285269541 1832439383567905365988039)
        ·
          refine ⟨2748659075351858048982059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832439383567905365988039 2748659075351858048982059)
          ·
            refine ⟨4122988613027787073473089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748659075351858048982059 4122988613027787073473089)
            ·
              refine ⟨3092241459770840305104817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122988613027787073473089 3092241459770840305104817)
              ·
                refine ⟨2319181094828130228828613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092241459770840305104817 2319181094828130228828613)
                ·
                  refine ⟨434846455280274417905365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2319181094828130228828613 434846455280274417905365)
                  ·
                    rfl

theorem cell20_952718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_952718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952718 prefixEnd_952718 := by exact prefixLift 952718
  have htrace : WordTrace (prefixWord ++ tailWord_952718) baseStart_952718 baseEnd_952718 := by
    simpa [prefixWord, tailWord_952718, baseEnd_952718] using wordTrace_append hprefix tailTrace_952718
  have hstable : (prefixWord ++ tailWord_952718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952718).length < 2 ^ (prefixWord ++ tailWord_952718).sum := by decide
  have hdescent : baseEnd_952718 < baseStart_952718 := by decide
  rcases family_descends (prefixWord ++ tailWord_952718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952794 : List Nat := [3, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_952794 : Nat := 118140960795 + 952794 * 2 ^ 59
def prefixEnd_952794 : Nat := 4983230072969 + 3 ^ 40 * 952794 * 2
def baseEnd_952794 : Nat := 434881143751155931371721

theorem tailTrace_952794 : CollatzResearch.WordTrace tailWord_952794 prefixEnd_952794 434881143751155931371721 := by
  unfold tailWord_952794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687813027549384276292359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23167501406798358070112957 8687813027549384276292359)
  ·
    refine ⟨13031719541324076414438539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8687813027549384276292359 13031719541324076414438539)
    ·
      refine ⟨19547579311986114621657809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13031719541324076414438539 19547579311986114621657809)
      ·
        refine ⟨14660684483989585966243357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19547579311986114621657809 14660684483989585966243357)
        ·
          refine ⟨5497756681496094737341259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14660684483989585966243357 5497756681496094737341259)
          ·
            refine ⟨8246635022244142106011889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497756681496094737341259 8246635022244142106011889)
            ·
              refine ⟨6184976266683106579508917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8246635022244142106011889 6184976266683106579508917)
              ·
                refine ⟨579841525001541241828961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6184976266683106579508917 579841525001541241828961)
                ·
                  refine ⟨434881143751155931371721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579841525001541241828961 434881143751155931371721)
                  ·
                    rfl

theorem cell20_952794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_952794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952794 prefixEnd_952794 := by exact prefixLift 952794
  have htrace : WordTrace (prefixWord ++ tailWord_952794) baseStart_952794 baseEnd_952794 := by
    simpa [prefixWord, tailWord_952794, baseEnd_952794] using wordTrace_append hprefix tailTrace_952794
  have hstable : (prefixWord ++ tailWord_952794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952794).length < 2 ^ (prefixWord ++ tailWord_952794).sum := by decide
  have hdescent : baseEnd_952794 < baseStart_952794 := by decide
  rcases family_descends (prefixWord ++ tailWord_952794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952808 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_952808 : Nat := 118140960795 + 952808 * 2 ^ 59
def prefixEnd_952808 : Nat := 4983230072969 + 3 ^ 40 * 952808 * 2
def baseEnd_952808 : Nat := 434887533732634104904997

theorem tailTrace_952808 : CollatzResearch.WordTrace tailWord_952808 prefixEnd_952808 434887533732634104904997 := by
  unfold tailWord_952808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17375881366073408748089539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23167841821431211664119385 17375881366073408748089539)
  ·
    refine ⟨26063822049110113122134309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17375881366073408748089539 26063822049110113122134309)
    ·
      refine ⟨4886966634208146210400183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26063822049110113122134309 4886966634208146210400183)
      ·
        refine ⟨7330449951312219315600275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886966634208146210400183 7330449951312219315600275)
        ·
          refine ⟨10995674926968328973400413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330449951312219315600275 10995674926968328973400413)
          ·
            refine ⟨4123378097613123365025155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10995674926968328973400413 4123378097613123365025155)
            ·
              refine ⟨6185067146419685047537733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123378097613123365025155 6185067146419685047537733)
              ·
                refine ⟨1159700089953690946413325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6185067146419685047537733 1159700089953690946413325)
                ·
                  refine ⟨434887533732634104904997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1159700089953690946413325 434887533732634104904997)
                  ·
                    rfl

theorem cell20_952808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_952808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952808 prefixEnd_952808 := by exact prefixLift 952808
  have htrace : WordTrace (prefixWord ++ tailWord_952808) baseStart_952808 baseEnd_952808 := by
    simpa [prefixWord, tailWord_952808, baseEnd_952808] using wordTrace_append hprefix tailTrace_952808
  have hstable : (prefixWord ++ tailWord_952808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952808).length < 2 ^ (prefixWord ++ tailWord_952808).sum := by decide
  have hdescent : baseEnd_952808 < baseStart_952808 := by decide
  rcases family_descends (prefixWord ++ tailWord_952808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952818 : List Nat := [3, 2, 1, 4, 2, 2, 1, 5]
def baseStart_952818 : Nat := 118140960795 + 952818 * 2 ^ 59
def prefixEnd_952818 : Nat := 4983230072969 + 3 ^ 40 * 952818 * 2
def baseEnd_952818 : Nat := 144964032668372838190541

theorem tailTrace_952818 : CollatzResearch.WordTrace tailWord_952818 prefixEnd_952818 144964032668372838190541 := by
  unfold tailWord_952818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8688031865527647301010777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23168084974740392802695405 8688031865527647301010777)
  ·
    refine ⟨6516023899145735475758083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8688031865527647301010777 6516023899145735475758083)
    ·
      refine ⟨9774035848718603213637125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516023899145735475758083 9774035848718603213637125)
      ·
        refine ⟨1832631721634738102556961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9774035848718603213637125 1832631721634738102556961)
        ·
          refine ⟨1374473791226053576917721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1832631721634738102556961 1374473791226053576917721)
          ·
            refine ⟨1030855343419540182688291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374473791226053576917721 1030855343419540182688291)
            ·
              refine ⟨1546283015129310274032437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030855343419540182688291 1546283015129310274032437)
              ·
                refine ⟨144964032668372838190541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1546283015129310274032437 144964032668372838190541)
                ·
                  rfl

theorem cell20_952818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_952818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952818 prefixEnd_952818 := by exact prefixLift 952818
  have htrace : WordTrace (prefixWord ++ tailWord_952818) baseStart_952818 baseEnd_952818 := by
    simpa [prefixWord, tailWord_952818, baseEnd_952818] using wordTrace_append hprefix tailTrace_952818
  have hstable : (prefixWord ++ tailWord_952818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952818).length < 2 ^ (prefixWord ++ tailWord_952818).sum := by decide
  have hdescent : baseEnd_952818 < baseStart_952818 := by decide
  rcases family_descends (prefixWord ++ tailWord_952818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952845 : List Nat := [1, 7, 1, 1, 1, 2, 2, 3, 2]
def baseStart_952845 : Nat := 118140960795 + 952845 * 2 ^ 59
def prefixEnd_952845 : Nat := 4983230072969 + 3 ^ 40 * 952845 * 2
def baseEnd_952845 : Nat := 434904421540826420671513

theorem tailTrace_952845 : CollatzResearch.WordTrace tailWord_952845 prefixEnd_952845 434904421540826420671513 := by
  unfold tailWord_952845
  simp only [CollatzResearch.WordTrace]
  refine ⟨34753112233012772815275989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23168741488675181876850659 34753112233012772815275989)
  ·
    refine ⟨814526067961236862858031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 34753112233012772815275989 814526067961236862858031)
    ·
      refine ⟨1221789101941855294287047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814526067961236862858031 1221789101941855294287047)
      ·
        refine ⟨1832683652912782941430571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221789101941855294287047 1832683652912782941430571)
        ·
          refine ⟨2749025479369174412145857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832683652912782941430571 2749025479369174412145857)
          ·
            refine ⟨2061769109526880809109393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2749025479369174412145857 2061769109526880809109393)
            ·
              refine ⟨1546326832145160606832045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061769109526880809109393 1546326832145160606832045)
              ·
                refine ⟨579872562054435227562017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1546326832145160606832045 579872562054435227562017)
                ·
                  refine ⟨434904421540826420671513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579872562054435227562017 434904421540826420671513)
                  ·
                    rfl

theorem cell20_952845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_952845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952845 prefixEnd_952845 := by exact prefixLift 952845
  have htrace : WordTrace (prefixWord ++ tailWord_952845) baseStart_952845 baseEnd_952845 := by
    simpa [prefixWord, tailWord_952845, baseEnd_952845] using wordTrace_append hprefix tailTrace_952845
  have hstable : (prefixWord ++ tailWord_952845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952845).length < 2 ^ (prefixWord ++ tailWord_952845).sum := by decide
  have hdescent : baseEnd_952845 < baseStart_952845 := by decide
  rcases family_descends (prefixWord ++ tailWord_952845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952860 : List Nat := [2, 2, 3, 1, 2, 3, 7]
def baseStart_952860 : Nat := 118140960795 + 952860 * 2 ^ 59
def prefixEnd_952860 : Nat := 4983230072969 + 3 ^ 40 * 952860 * 2
def baseEnd_952860 : Nat := 48323474216617003907939

theorem tailTrace_952860 : CollatzResearch.WordTrace tailWord_952860 prefixEnd_952860 48323474216617003907939 := by
  unfold tailWord_952860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376829663979215188536017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23169106218638953584714689 17376829663979215188536017)
  ·
    refine ⟨13032622247984411391402013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17376829663979215188536017 13032622247984411391402013)
    ·
      refine ⟨4887233342994154271775755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13032622247984411391402013 4887233342994154271775755)
      ·
        refine ⟨7330850014491231407663633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4887233342994154271775755 7330850014491231407663633)
        ·
          refine ⟨5498137510868423555747725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7330850014491231407663633 5498137510868423555747725)
          ·
            refine ⟨2061801566575658833405397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5498137510868423555747725 2061801566575658833405397)
            ·
              refine ⟨48323474216617003907939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2061801566575658833405397 48323474216617003907939)
              ·
                rfl

theorem cell20_952860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 7].length) (baseStart_952860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952860 prefixEnd_952860 := by exact prefixLift 952860
  have htrace : WordTrace (prefixWord ++ tailWord_952860) baseStart_952860 baseEnd_952860 := by
    simpa [prefixWord, tailWord_952860, baseEnd_952860] using wordTrace_append hprefix tailTrace_952860
  have hstable : (prefixWord ++ tailWord_952860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952860).length < 2 ^ (prefixWord ++ tailWord_952860).sum := by decide
  have hdescent : baseEnd_952860 < baseStart_952860 := by decide
  rcases family_descends (prefixWord ++ tailWord_952860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952894 : List Nat := [4, 2, 1, 4, 1, 1, 1, 6]
def baseStart_952894 : Nat := 118140960795 + 952894 * 2 ^ 59
def prefixEnd_952894 : Nat := 4983230072969 + 3 ^ 40 * 952894 * 2
def baseEnd_952894 : Nat := 144975595492000009345993

theorem tailTrace_952894 : CollatzResearch.WordTrace tailWord_952894 prefixEnd_952894 144975595492000009345993 := by
  unfold tailWord_952894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344362426229406772976217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23169932939890169455873157 4344362426229406772976217)
  ·
    refine ⟨3258271819672055079732163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4344362426229406772976217 3258271819672055079732163)
    ·
      refine ⟨4887407729508082619598245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258271819672055079732163 4887407729508082619598245)
      ·
        refine ⟨916388949282765491174671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4887407729508082619598245 916388949282765491174671)
        ·
          refine ⟨1374583423924148236762007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916388949282765491174671 1374583423924148236762007)
          ·
            refine ⟨2061875135886222355143011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374583423924148236762007 2061875135886222355143011)
            ·
              refine ⟨3092812703829333532714517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061875135886222355143011 3092812703829333532714517)
              ·
                refine ⟨144975595492000009345993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3092812703829333532714517 144975595492000009345993)
                ·
                  rfl

theorem cell20_952894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_952894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952894 prefixEnd_952894 := by exact prefixLift 952894
  have htrace : WordTrace (prefixWord ++ tailWord_952894) baseStart_952894 baseEnd_952894 := by
    simpa [prefixWord, tailWord_952894, baseEnd_952894] using wordTrace_append hprefix tailTrace_952894
  have hstable : (prefixWord ++ tailWord_952894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952894).length < 2 ^ (prefixWord ++ tailWord_952894).sum := by decide
  have hdescent : baseEnd_952894 < baseStart_952894 := by decide
  rcases family_descends (prefixWord ++ tailWord_952894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952900 : List Nat := [2, 3, 5, 1, 1, 2, 1, 3, 2]
def baseStart_952900 : Nat := 118140960795 + 952900 * 2 ^ 59
def prefixEnd_952900 : Nat := 4983230072969 + 3 ^ 40 * 952900 * 2
def baseEnd_952900 : Nat := 434929525039490673837955

theorem tailTrace_952900 : CollatzResearch.WordTrace tailWord_952900 prefixEnd_952900 434929525039490673837955 := by
  unfold tailWord_952900
  simp only [CollatzResearch.WordTrace]
  refine ⟨17377559123906758604264077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23170078831875678139018769 17377559123906758604264077)
  ·
    refine ⟨6516584671465034476599029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17377559123906758604264077 6516584671465034476599029)
    ·
      refine ⟨610929812949846982181159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6516584671465034476599029 610929812949846982181159)
      ·
        refine ⟨916394719424770473271739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610929812949846982181159 916394719424770473271739)
        ·
          refine ⟨1374592079137155709907609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916394719424770473271739 1374592079137155709907609)
          ·
            refine ⟨1030944059352866782430707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374592079137155709907609 1030944059352866782430707)
            ·
              refine ⟨1546416089029300173646061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030944059352866782430707 1546416089029300173646061)
              ·
                refine ⟨579906033385987565117273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1546416089029300173646061 579906033385987565117273)
                ·
                  refine ⟨434929525039490673837955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579906033385987565117273 434929525039490673837955)
                  ·
                    rfl

theorem cell20_952900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_952900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952900 prefixEnd_952900 := by exact prefixLift 952900
  have htrace : WordTrace (prefixWord ++ tailWord_952900) baseStart_952900 baseEnd_952900 := by
    simpa [prefixWord, tailWord_952900, baseEnd_952900] using wordTrace_append hprefix tailTrace_952900
  have hstable : (prefixWord ++ tailWord_952900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952900).length < 2 ^ (prefixWord ++ tailWord_952900).sum := by decide
  have hdescent : baseEnd_952900 < baseStart_952900 := by decide
  rcases family_descends (prefixWord ++ tailWord_952900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952929 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_952929 : Nat := 118140960795 + 952929 * 2 ^ 59
def prefixEnd_952929 : Nat := 4983230072969 + 3 ^ 40 * 952929 * 2
def baseEnd_952929 : Nat := 434942761429695461871169

theorem tailTrace_952929 : CollatzResearch.WordTrace tailWord_952929 prefixEnd_952929 434942761429695461871169 := by
  unfold tailWord_952929
  simp only [CollatzResearch.WordTrace]
  refine ⟨34756175964708455161333841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23170783976472303440889227 34756175964708455161333841)
  ·
    refine ⟨26067131973531341371000381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34756175964708455161333841 26067131973531341371000381)
    ·
      refine ⟨9775174490074253014125143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26067131973531341371000381 9775174490074253014125143)
      ·
        refine ⟨14662761735111379521187715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9775174490074253014125143 14662761735111379521187715)
        ·
          refine ⟨21994142602667069281781573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14662761735111379521187715 21994142602667069281781573)
          ·
            refine ⟨4123901738000075490334045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21994142602667069281781573 4123901738000075490334045)
            ·
              refine ⟨1546463151750028308875267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4123901738000075490334045 1546463151750028308875267)
              ·
                refine ⟨2319694727625042463312901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546463151750028308875267 2319694727625042463312901)
                ·
                  refine ⟨434942761429695461871169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2319694727625042463312901 434942761429695461871169)
                  ·
                    rfl

theorem cell20_952929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_952929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952929 prefixEnd_952929 := by exact prefixLift 952929
  have htrace : WordTrace (prefixWord ++ tailWord_952929) baseStart_952929 baseEnd_952929 := by
    simpa [prefixWord, tailWord_952929, baseEnd_952929] using wordTrace_append hprefix tailTrace_952929
  have hstable : (prefixWord ++ tailWord_952929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952929).length < 2 ^ (prefixWord ++ tailWord_952929).sum := by decide
  have hdescent : baseEnd_952929 < baseStart_952929 := by decide
  rcases family_descends (prefixWord ++ tailWord_952929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952980 : List Nat := [2, 4, 2, 2, 1, 1, 4, 2, 2]
def baseStart_952980 : Nat := 118140960795 + 952980 * 2 ^ 59
def prefixEnd_952980 : Nat := 4983230072969 + 3 ^ 40 * 952980 * 2
def baseEnd_952980 : Nat := 434966039219365951170961

theorem tailTrace_952980 : CollatzResearch.WordTrace tailWord_952980 prefixEnd_952980 434966039219365951170961 := by
  unfold tailWord_952980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17379018043761845435720197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23172024058349127247626929 17379018043761845435720197)
  ·
    refine ⟨3258565883205346019197537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17379018043761845435720197 3258565883205346019197537)
    ·
      refine ⟨2443924412404009514398153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3258565883205346019197537 2443924412404009514398153)
      ·
        refine ⟨1832943309303007135798615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2443924412404009514398153 1832943309303007135798615)
        ·
          refine ⟨2749414963954510703697923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832943309303007135798615 2749414963954510703697923)
          ·
            refine ⟨4124122445931766055546885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749414963954510703697923 4124122445931766055546885)
            ·
              refine ⟨773272958612206135415041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4124122445931766055546885 773272958612206135415041)
              ·
                refine ⟨579954718959154601561281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773272958612206135415041 579954718959154601561281)
                ·
                  refine ⟨434966039219365951170961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579954718959154601561281 434966039219365951170961)
                  ·
                    rfl

theorem cell20_952980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_952980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952980 prefixEnd_952980 := by exact prefixLift 952980
  have htrace : WordTrace (prefixWord ++ tailWord_952980) baseStart_952980 baseEnd_952980 := by
    simpa [prefixWord, tailWord_952980, baseEnd_952980] using wordTrace_append hprefix tailTrace_952980
  have hstable : (prefixWord ++ tailWord_952980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952980).length < 2 ^ (prefixWord ++ tailWord_952980).sum := by decide
  have hdescent : baseEnd_952980 < baseStart_952980 := by decide
  rcases family_descends (prefixWord ++ tailWord_952980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952984 : List Nat := [2, 1, 2, 4, 1, 1, 3, 4, 2]
def baseStart_952984 : Nat := 118140960795 + 952984 * 2 ^ 59
def prefixEnd_952984 : Nat := 4983230072969 + 3 ^ 40 * 952984 * 2
def baseEnd_952984 : Nat := 434967864928359715037611

theorem tailTrace_952984 : CollatzResearch.WordTrace tailWord_952984 prefixEnd_952984 434967864928359715037611 := by
  unfold tailWord_952984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17379090989754599777293003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23172121319672799703057337 17379090989754599777293003)
  ·
    refine ⟨26068636484631899665939505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17379090989754599777293003 26068636484631899665939505)
    ·
      refine ⟨19551477363473924749454629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26068636484631899665939505 19551477363473924749454629)
      ·
        refine ⟨3665902005651360890522743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19551477363473924749454629 3665902005651360890522743)
        ·
          refine ⟨5498853008477041335784115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665902005651360890522743 5498853008477041335784115)
          ·
            refine ⟨8248279512715562003676173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5498853008477041335784115 8248279512715562003676173)
            ·
              refine ⟨3093104817268335751378565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8248279512715562003676173 3093104817268335751378565)
              ·
                refine ⟨579957153237812953383481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3093104817268335751378565 579957153237812953383481)
                ·
                  refine ⟨434967864928359715037611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579957153237812953383481 434967864928359715037611)
                  ·
                    rfl

theorem cell20_952984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_952984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952984 prefixEnd_952984 := by exact prefixLift 952984
  have htrace : WordTrace (prefixWord ++ tailWord_952984) baseStart_952984 baseEnd_952984 := by
    simpa [prefixWord, tailWord_952984, baseEnd_952984] using wordTrace_append hprefix tailTrace_952984
  have hstable : (prefixWord ++ tailWord_952984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952984).length < 2 ^ (prefixWord ++ tailWord_952984).sum := by decide
  have hdescent : baseEnd_952984 < baseStart_952984 := by decide
  rcases family_descends (prefixWord ++ tailWord_952984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952995 : List Nat := [1, 1, 1, 4, 1, 1, 2, 9]
def baseStart_952995 : Nat := 118140960795 + 952995 * 2 ^ 59
def prefixEnd_952995 : Nat := 4983230072969 + 3 ^ 40 * 952995 * 2
def baseEnd_952995 : Nat := 144990961876030855223633

theorem tailTrace_952995 : CollatzResearch.WordTrace tailWord_952995 prefixEnd_952995 144990961876030855223633 := by
  unfold tailWord_952995
  simp only [CollatzResearch.WordTrace]
  refine ⟨34758583182469348433236439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23172388788312898955490959 34758583182469348433236439)
  ·
    refine ⟨52137874773704022649854659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34758583182469348433236439 52137874773704022649854659)
    ·
      refine ⟨78206812160556033974781989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52137874773704022649854659 78206812160556033974781989)
      ·
        refine ⟨14663777280104256370271623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78206812160556033974781989 14663777280104256370271623)
        ·
          refine ⟨21995665920156384555407435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14663777280104256370271623 21995665920156384555407435)
          ·
            refine ⟨32993498880234576833111153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21995665920156384555407435 32993498880234576833111153)
            ·
              refine ⟨24745124160175932624833365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32993498880234576833111153 24745124160175932624833365)
              ·
                refine ⟨144990961876030855223633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24745124160175932624833365 144990961876030855223633)
                ·
                  rfl

theorem cell20_952995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_952995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_952995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_952995 prefixEnd_952995 := by exact prefixLift 952995
  have htrace : WordTrace (prefixWord ++ tailWord_952995) baseStart_952995 baseEnd_952995 := by
    simpa [prefixWord, tailWord_952995, baseEnd_952995] using wordTrace_append hprefix tailTrace_952995
  have hstable : (prefixWord ++ tailWord_952995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952995).length < 2 ^ (prefixWord ++ tailWord_952995).sum := by decide
  have hdescent : baseEnd_952995 < baseStart_952995 := by decide
  rcases family_descends (prefixWord ++ tailWord_952995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953005 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_953005 : Nat := 118140960795 + 953005 * 2 ^ 59
def prefixEnd_953005 : Nat := 4983230072969 + 3 ^ 40 * 953005 * 2
def baseEnd_953005 : Nat := 434977449900576975337525

theorem tailTrace_953005 : CollatzResearch.WordTrace tailWord_953005 prefixEnd_953005 434977449900576975337525 := by
  unfold tailWord_953005
  simp only [CollatzResearch.WordTrace]
  refine ⟨34758947912433120141100469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23172631941622080094066979 34758947912433120141100469)
  ·
    refine ⟨3258651366790605013228169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34758947912433120141100469 3258651366790605013228169)
    ·
      refine ⟨2443988525092953759921127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3258651366790605013228169 2443988525092953759921127)
      ·
        refine ⟨3665982787639430639881691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443988525092953759921127 3665982787639430639881691)
        ·
          refine ⟨5498974181459145959822537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665982787639430639881691 5498974181459145959822537)
          ·
            refine ⟨4124230636094359469866903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5498974181459145959822537 4124230636094359469866903)
            ·
              refine ⟨6186345954141539204800355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124230636094359469866903 6186345954141539204800355)
              ·
                refine ⟨9279518931212308807200533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186345954141539204800355 9279518931212308807200533)
                ·
                  refine ⟨434977449900576975337525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9279518931212308807200533 434977449900576975337525)
                  ·
                    rfl

theorem cell20_953005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_953005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953005 prefixEnd_953005 := by exact prefixLift 953005
  have htrace : WordTrace (prefixWord ++ tailWord_953005) baseStart_953005 baseEnd_953005 := by
    simpa [prefixWord, tailWord_953005, baseEnd_953005] using wordTrace_append hprefix tailTrace_953005
  have hstable : (prefixWord ++ tailWord_953005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953005).length < 2 ^ (prefixWord ++ tailWord_953005).sum := by decide
  have hdescent : baseEnd_953005 < baseStart_953005 := by decide
  rcases family_descends (prefixWord ++ tailWord_953005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953036 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_953036 : Nat := 118140960795 + 953036 * 2 ^ 59
def prefixEnd_953036 : Nat := 4983230072969 + 3 ^ 40 * 953036 * 2
def baseEnd_953036 : Nat := 434991599145278645304065

theorem tailTrace_953036 : CollatzResearch.WordTrace tailWord_953036 prefixEnd_953036 434991599145278645304065 := by
  unfold tailWord_953036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17380039287660406217739481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23173385716880541623652641 17380039287660406217739481)
  ·
    refine ⟨13035029465745304663304611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17380039287660406217739481 13035029465745304663304611)
    ·
      refine ⟨19552544198617956994956917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13035029465745304663304611 19552544198617956994956917)
      ·
        refine ⟨1833051018620433468277211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19552544198617956994956917 1833051018620433468277211)
        ·
          refine ⟨2749576527930650202415817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833051018620433468277211 2749576527930650202415817)
          ·
            refine ⟨2062182395947987651811863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2749576527930650202415817 2062182395947987651811863)
            ·
              refine ⟨3093273593921981477717795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062182395947987651811863 3093273593921981477717795)
              ·
                refine ⟨4639910390882972216576693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093273593921981477717795 4639910390882972216576693)
                ·
                  refine ⟨434991599145278645304065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4639910390882972216576693 434991599145278645304065)
                  ·
                    rfl

theorem cell20_953036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_953036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953036 prefixEnd_953036 := by exact prefixLift 953036
  have htrace : WordTrace (prefixWord ++ tailWord_953036) baseStart_953036 baseEnd_953036 := by
    simpa [prefixWord, tailWord_953036, baseEnd_953036] using wordTrace_append hprefix tailTrace_953036
  have hstable : (prefixWord ++ tailWord_953036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953036).length < 2 ^ (prefixWord ++ tailWord_953036).sum := by decide
  have hdescent : baseEnd_953036 < baseStart_953036 := by decide
  rcases family_descends (prefixWord ++ tailWord_953036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953149 : List Nat := [1, 4, 1, 4, 3, 1, 2, 2, 2]
def baseStart_953149 : Nat := 118140960795 + 953149 * 2 ^ 59
def prefixEnd_953149 : Nat := 4983230072969 + 3 ^ 40 * 953149 * 2
def baseEnd_953149 : Nat := 435043175424352474536937

theorem tailTrace_953149 : CollatzResearch.WordTrace tailWord_953149 prefixEnd_953149 435043175424352474536937 := by
  unfold tailWord_953149
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764200023911432734342501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23176133349274288489561667 34764200023911432734342501)
  ·
    refine ⟨6518287504483393637689219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34764200023911432734342501 6518287504483393637689219)
    ·
      refine ⟨9777431256725090456533829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6518287504483393637689219 9777431256725090456533829)
      ·
        refine ⟨1833268360635954460600093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9777431256725090456533829 1833268360635954460600093)
        ·
          refine ⟨687475635238482922725035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1833268360635954460600093 687475635238482922725035)
          ·
            refine ⟨1031213452857724384087553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687475635238482922725035 1031213452857724384087553)
            ·
              refine ⟨773410089643293288065665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031213452857724384087553 773410089643293288065665)
              ·
                refine ⟨580057567232469966049249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773410089643293288065665 580057567232469966049249)
                ·
                  refine ⟨435043175424352474536937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580057567232469966049249 435043175424352474536937)
                  ·
                    rfl

theorem cell20_953149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_953149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953149 prefixEnd_953149 := by exact prefixLift 953149
  have htrace : WordTrace (prefixWord ++ tailWord_953149) baseStart_953149 baseEnd_953149 := by
    simpa [prefixWord, tailWord_953149, baseEnd_953149] using wordTrace_append hprefix tailTrace_953149
  have hstable : (prefixWord ++ tailWord_953149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953149).length < 2 ^ (prefixWord ++ tailWord_953149).sum := by decide
  have hdescent : baseEnd_953149 < baseStart_953149 := by decide
  rcases family_descends (prefixWord ++ tailWord_953149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953164 : List Nat := [2, 2, 1, 3, 3, 1, 3, 5]
def baseStart_953164 : Nat := 118140960795 + 953164 * 2 ^ 59
def prefixEnd_953164 : Nat := 4983230072969 + 3 ^ 40 * 953164 * 2
def baseEnd_953164 : Nat := 145016673944359696345625

theorem tailTrace_953164 : CollatzResearch.WordTrace tailWord_953164 prefixEnd_953164 145016673944359696345625 := by
  unfold tailWord_953164
  simp only [CollatzResearch.WordTrace]
  refine ⟨17382373559428545148069273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23176498079238060197425697 17382373559428545148069273)
  ·
    refine ⟨13036780169571408861051955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17382373559428545148069273 13036780169571408861051955)
    ·
      refine ⟨19555170254357113291577933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13036780169571408861051955 19555170254357113291577933)
      ·
        refine ⟨7333188845383917484341725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19555170254357113291577933 7333188845383917484341725)
        ·
          refine ⟨2749945817018969056628147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7333188845383917484341725 2749945817018969056628147)
          ·
            refine ⟨4124918725528453584942221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749945817018969056628147 4124918725528453584942221)
            ·
              refine ⟨1546844522073170094353333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4124918725528453584942221 1546844522073170094353333)
              ·
                refine ⟨145016673944359696345625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1546844522073170094353333 145016673944359696345625)
                ·
                  rfl

theorem cell20_953164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_953164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953164 prefixEnd_953164 := by exact prefixLift 953164
  have htrace : WordTrace (prefixWord ++ tailWord_953164) baseStart_953164 baseEnd_953164 := by
    simpa [prefixWord, tailWord_953164, baseEnd_953164] using wordTrace_append hprefix tailTrace_953164
  have hstable : (prefixWord ++ tailWord_953164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953164).length < 2 ^ (prefixWord ++ tailWord_953164).sum := by decide
  have hdescent : baseEnd_953164 < baseStart_953164 := by decide
  rcases family_descends (prefixWord ++ tailWord_953164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953178 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_953178 : Nat := 118140960795 + 953178 * 2 ^ 59
def prefixEnd_953178 : Nat := 4983230072969 + 3 ^ 40 * 953178 * 2
def baseEnd_953178 : Nat := 435056411814557262570151

theorem tailTrace_953178 : CollatzResearch.WordTrace tailWord_953178 prefixEnd_953178 435056411814557262570151 := by
  unfold tailWord_953178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691314435201592671787047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23176838493870913791432125 8691314435201592671787047)
  ·
    refine ⟨13036971652802389007680571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8691314435201592671787047 13036971652802389007680571)
    ·
      refine ⟨19555457479203583511520857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13036971652802389007680571 19555457479203583511520857)
      ·
        refine ⟨14666593109402687633640643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19555457479203583511520857 14666593109402687633640643)
        ·
          refine ⟨21999889664104031450460965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14666593109402687633640643 21999889664104031450460965)
          ·
            refine ⟨4124979312019505896961431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21999889664104031450460965 4124979312019505896961431)
            ·
              refine ⟨6187468968029258845442147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124979312019505896961431 6187468968029258845442147)
              ·
                refine ⟨9281203452043888268163221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187468968029258845442147 9281203452043888268163221)
                ·
                  refine ⟨435056411814557262570151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9281203452043888268163221 435056411814557262570151)
                  ·
                    rfl

theorem cell20_953178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_953178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953178 prefixEnd_953178 := by exact prefixLift 953178
  have htrace : WordTrace (prefixWord ++ tailWord_953178) baseStart_953178 baseEnd_953178 := by
    simpa [prefixWord, tailWord_953178, baseEnd_953178] using wordTrace_append hprefix tailTrace_953178
  have hstable : (prefixWord ++ tailWord_953178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953178).length < 2 ^ (prefixWord ++ tailWord_953178).sum := by decide
  have hdescent : baseEnd_953178 < baseStart_953178 := by decide
  rcases family_descends (prefixWord ++ tailWord_953178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953195 : List Nat := [1, 1, 1, 1, 2, 2, 5, 5, 2]
def baseStart_953195 : Nat := 118140960795 + 953195 * 2 ^ 59
def prefixEnd_953195 : Nat := 4983230072969 + 3 ^ 40 * 953195 * 2
def baseEnd_953195 : Nat := 435064171077780759003415

theorem tailTrace_953195 : CollatzResearch.WordTrace tailWord_953195 prefixEnd_953195 435064171077780759003415 := by
  unfold tailWord_953195
  simp only [CollatzResearch.WordTrace]
  refine ⟨34765877781744782590517039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23177251854496521727011359 34765877781744782590517039)
  ·
    refine ⟨52148816672617173885775559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34765877781744782590517039 52148816672617173885775559)
    ·
      refine ⟨78223225008925760828663339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52148816672617173885775559 78223225008925760828663339)
      ·
        refine ⟨117334837513388641242995009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78223225008925760828663339 117334837513388641242995009)
        ·
          refine ⟨88001128135041480932246257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117334837513388641242995009 88001128135041480932246257)
          ·
            refine ⟨66000846101281110699184693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88001128135041480932246257 66000846101281110699184693)
            ·
              refine ⟨6187579321995104128048565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66000846101281110699184693 6187579321995104128048565)
              ·
                refine ⟨580085561437041012004553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6187579321995104128048565 580085561437041012004553)
                ·
                  refine ⟨435064171077780759003415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580085561437041012004553 435064171077780759003415)
                  ·
                    rfl

theorem cell20_953195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 2].length) (baseStart_953195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953195 prefixEnd_953195 := by exact prefixLift 953195
  have htrace : WordTrace (prefixWord ++ tailWord_953195) baseStart_953195 baseEnd_953195 := by
    simpa [prefixWord, tailWord_953195, baseEnd_953195] using wordTrace_append hprefix tailTrace_953195
  have hstable : (prefixWord ++ tailWord_953195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953195).length < 2 ^ (prefixWord ++ tailWord_953195).sum := by decide
  have hdescent : baseEnd_953195 < baseStart_953195 := by decide
  rcases family_descends (prefixWord ++ tailWord_953195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953205 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 3]
def baseStart_953205 : Nat := 118140960795 + 953205 * 2 ^ 59
def prefixEnd_953205 : Nat := 4983230072969 + 3 ^ 40 * 953205 * 2
def baseEnd_953205 : Nat := 435068735350265168670041

theorem tailTrace_953205 : CollatzResearch.WordTrace tailWord_953205 prefixEnd_953205 435068735350265168670041 := by
  unfold tailWord_953205
  simp only [CollatzResearch.WordTrace]
  refine ⟨34766242511708554298381069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23177495007805702865587379 34766242511708554298381069)
  ·
    refine ⟨13037340941890707861892901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34766242511708554298381069 13037340941890707861892901)
    ·
      refine ⟨2444501426604507724104919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13037340941890707861892901 2444501426604507724104919)
      ·
        refine ⟨3666752139906761586157379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444501426604507724104919 3666752139906761586157379)
        ·
          refine ⟨5500128209860142379236069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666752139906761586157379 5500128209860142379236069)
          ·
            refine ⟨1031274039348776696106763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5500128209860142379236069 1031274039348776696106763)
            ·
              refine ⟨1546911059023165044160145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031274039348776696106763 1546911059023165044160145)
              ·
                refine ⟨1160183294267373783120109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1546911059023165044160145 1160183294267373783120109)
                ·
                  refine ⟨435068735350265168670041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160183294267373783120109 435068735350265168670041)
                  ·
                    rfl

theorem cell20_953205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_953205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953205 prefixEnd_953205 := by exact prefixLift 953205
  have htrace : WordTrace (prefixWord ++ tailWord_953205) baseStart_953205 baseEnd_953205 := by
    simpa [prefixWord, tailWord_953205, baseEnd_953205] using wordTrace_append hprefix tailTrace_953205
  have hstable : (prefixWord ++ tailWord_953205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953205).length < 2 ^ (prefixWord ++ tailWord_953205).sum := by decide
  have hdescent : baseEnd_953205 < baseStart_953205 := by decide
  rcases family_descends (prefixWord ++ tailWord_953205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953209 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_953209 : Nat := 118140960795 + 953209 * 2 ^ 59
def prefixEnd_953209 : Nat := 4983230072969 + 3 ^ 40 * 953209 * 2
def baseEnd_953209 : Nat := 435070561059258932536691

theorem tailTrace_953209 : CollatzResearch.WordTrace tailWord_953209 prefixEnd_953209 435070561059258932536691 := by
  unfold tailWord_953209
  simp only [CollatzResearch.WordTrace]
  refine ⟨34766388403694062981526681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23177592269129375321017787 34766388403694062981526681)
  ·
    refine ⟨26074791302770547236145011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34766388403694062981526681 26074791302770547236145011)
    ·
      refine ⟨39112186954155820854217517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26074791302770547236145011 39112186954155820854217517)
      ·
        refine ⟨14667070107808432820331569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39112186954155820854217517 14667070107808432820331569)
        ·
          refine ⟨11000302580856324615248677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14667070107808432820331569 11000302580856324615248677)
          ·
            refine ⟨2062556733910560865359127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11000302580856324615248677 2062556733910560865359127)
            ·
              refine ⟨3093835100865841298038691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062556733910560865359127 3093835100865841298038691)
              ·
                refine ⟨4640752651298761947058037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093835100865841298038691 4640752651298761947058037)
                ·
                  refine ⟨435070561059258932536691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4640752651298761947058037 435070561059258932536691)
                  ·
                    rfl

theorem cell20_953209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_953209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953209 prefixEnd_953209 := by exact prefixLift 953209
  have htrace : WordTrace (prefixWord ++ tailWord_953209) baseStart_953209 baseEnd_953209 := by
    simpa [prefixWord, tailWord_953209, baseEnd_953209] using wordTrace_append hprefix tailTrace_953209
  have hstable : (prefixWord ++ tailWord_953209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953209).length < 2 ^ (prefixWord ++ tailWord_953209).sum := by decide
  have hdescent : baseEnd_953209 < baseStart_953209 := by decide
  rcases family_descends (prefixWord ++ tailWord_953209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953247 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_953247 : Nat := 118140960795 + 953247 * 2 ^ 59
def prefixEnd_953247 : Nat := 4983230072969 + 3 ^ 40 * 953247 * 2
def baseEnd_953247 : Nat := 435087905294699689269869

theorem tailTrace_953247 : CollatzResearch.WordTrace tailWord_953247 prefixEnd_953247 435087905294699689269869 := by
  unfold tailWord_953247
  simp only [CollatzResearch.WordTrace]
  refine ⟨34767774377556395471409995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23178516251704263647606663 34767774377556395471409995)
  ·
    refine ⟨52151661566334593207114993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34767774377556395471409995 52151661566334593207114993)
    ·
      refine ⟨39113746174750944905336245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52151661566334593207114993 39113746174750944905336245)
      ·
        refine ⟨3666913703882901084875273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39113746174750944905336245 3666913703882901084875273)
        ·
          refine ⟨2750185277912175813656455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3666913703882901084875273 2750185277912175813656455)
          ·
            refine ⟨4125277916868263720484683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750185277912175813656455 4125277916868263720484683)
            ·
              refine ⟨6187916875302395580727025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125277916868263720484683 6187916875302395580727025)
              ·
                refine ⟨4640937656476796685545269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187916875302395580727025 4640937656476796685545269)
                ·
                  refine ⟨435087905294699689269869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4640937656476796685545269 435087905294699689269869)
                  ·
                    rfl

theorem cell20_953247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_953247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953247 prefixEnd_953247 := by exact prefixLift 953247
  have htrace : WordTrace (prefixWord ++ tailWord_953247) baseStart_953247 baseEnd_953247 := by
    simpa [prefixWord, tailWord_953247, baseEnd_953247] using wordTrace_append hprefix tailTrace_953247
  have hstable : (prefixWord ++ tailWord_953247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953247).length < 2 ^ (prefixWord ++ tailWord_953247).sum := by decide
  have hdescent : baseEnd_953247 < baseStart_953247 := by decide
  rcases family_descends (prefixWord ++ tailWord_953247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953271 : List Nat := [1, 1, 3, 1, 3, 1, 2, 6, 2]
def baseStart_953271 : Nat := 118140960795 + 953271 * 2 ^ 59
def prefixEnd_953271 : Nat := 4983230072969 + 3 ^ 40 * 953271 * 2
def baseEnd_953271 : Nat := 435098859548662272469771

theorem tailTrace_953271 : CollatzResearch.WordTrace tailWord_953271 prefixEnd_953271 435098859548662272469771 := by
  unfold tailWord_953271
  simp only [CollatzResearch.WordTrace]
  refine ⟨34768649729469447570283667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23179099819646298380189111 34768649729469447570283667)
  ·
    refine ⟨52152974594204171355425501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34768649729469447570283667 52152974594204171355425501)
    ·
      refine ⟨19557365472826564258284563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52152974594204171355425501 19557365472826564258284563)
      ·
        refine ⟨29336048209239846387426845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19557365472826564258284563 29336048209239846387426845)
        ·
          refine ⟨11001018078464942395285067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29336048209239846387426845 11001018078464942395285067)
          ·
            refine ⟨16501527117697413592927601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11001018078464942395285067 16501527117697413592927601)
            ·
              refine ⟨12376145338273060194695701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16501527117697413592927601 12376145338273060194695701)
              ·
                refine ⟨580131812731549696626361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12376145338273060194695701 580131812731549696626361)
                ·
                  refine ⟨435098859548662272469771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580131812731549696626361 435098859548662272469771)
                  ·
                    rfl

theorem cell20_953271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 2].length) (baseStart_953271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953271 prefixEnd_953271 := by exact prefixLift 953271
  have htrace : WordTrace (prefixWord ++ tailWord_953271) baseStart_953271 baseEnd_953271 := by
    simpa [prefixWord, tailWord_953271, baseEnd_953271] using wordTrace_append hprefix tailTrace_953271
  have hstable : (prefixWord ++ tailWord_953271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953271).length < 2 ^ (prefixWord ++ tailWord_953271).sum := by decide
  have hdescent : baseEnd_953271 < baseStart_953271 := by decide
  rcases family_descends (prefixWord ++ tailWord_953271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953278 : List Nat := [4, 2, 1, 1, 1, 2, 4, 5]
def baseStart_953278 : Nat := 118140960795 + 953278 * 2 ^ 59
def prefixEnd_953278 : Nat := 4983230072969 + 3 ^ 40 * 953278 * 2
def baseEnd_953278 : Nat := 145034018179800453078803

theorem tailTrace_953278 : CollatzResearch.WordTrace tailWord_953278 prefixEnd_953278 145034018179800453078803 := by
  unfold tailWord_953278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346113130055510970723561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23179270026962725177192325 4346113130055510970723561)
  ·
    refine ⟨3259584847541633228042671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4346113130055510970723561 3259584847541633228042671)
    ·
      refine ⟨4889377271312449842064007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3259584847541633228042671 4889377271312449842064007)
      ·
        refine ⟨7334065906968674763096011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889377271312449842064007 7334065906968674763096011)
        ·
          refine ⟨11001098860453012144644017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334065906968674763096011 11001098860453012144644017)
          ·
            refine ⟨8250824145339759108483013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11001098860453012144644017 8250824145339759108483013)
            ·
              refine ⟨1547029527251204832840565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8250824145339759108483013 1547029527251204832840565)
              ·
                refine ⟨145034018179800453078803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1547029527251204832840565 145034018179800453078803)
                ·
                  rfl

theorem cell20_953278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_953278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953278 prefixEnd_953278 := by exact prefixLift 953278
  have htrace : WordTrace (prefixWord ++ tailWord_953278) baseStart_953278 baseEnd_953278 := by
    simpa [prefixWord, tailWord_953278, baseEnd_953278] using wordTrace_append hprefix tailTrace_953278
  have hstable : (prefixWord ++ tailWord_953278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953278).length < 2 ^ (prefixWord ++ tailWord_953278).sum := by decide
  have hdescent : baseEnd_953278 < baseStart_953278 := by decide
  rcases family_descends (prefixWord ++ tailWord_953278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953292 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_953292 : Nat := 118140960795 + 953292 * 2 ^ 59
def prefixEnd_953292 : Nat := 4983230072969 + 3 ^ 40 * 953292 * 2
def baseEnd_953292 : Nat := 435108444520879532769685

theorem tailTrace_953292 : CollatzResearch.WordTrace tailWord_953292 prefixEnd_953292 435108444520879532769685 := by
  unfold tailWord_953292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17384707831196684078399065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23179610441595578771198753 17384707831196684078399065)
  ·
    refine ⟨13038530873397513058799299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17384707831196684078399065 13038530873397513058799299)
    ·
      refine ⟨19557796310096269588198949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13038530873397513058799299 19557796310096269588198949)
      ·
        refine ⟨3667086808143050547787303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19557796310096269588198949 3667086808143050547787303)
        ·
          refine ⟨5500630212214575821680955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667086808143050547787303 5500630212214575821680955)
          ·
            refine ⟨8250945318321863732521433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500630212214575821680955 8250945318321863732521433)
            ·
              refine ⟨6188208988741397799391075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8250945318321863732521433 6188208988741397799391075)
              ·
                refine ⟨9282313483112096699086613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188208988741397799391075 9282313483112096699086613)
                ·
                  refine ⟨435108444520879532769685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9282313483112096699086613 435108444520879532769685)
                  ·
                    rfl

theorem cell20_953292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_953292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953292 prefixEnd_953292 := by exact prefixLift 953292
  have htrace : WordTrace (prefixWord ++ tailWord_953292) baseStart_953292 baseEnd_953292 := by
    simpa [prefixWord, tailWord_953292, baseEnd_953292] using wordTrace_append hprefix tailTrace_953292
  have hstable : (prefixWord ++ tailWord_953292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953292).length < 2 ^ (prefixWord ++ tailWord_953292).sum := by decide
  have hdescent : baseEnd_953292 < baseStart_953292 := by decide
  rcases family_descends (prefixWord ++ tailWord_953292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953375 : List Nat := [1, 1, 2, 4, 1, 4, 7]
def baseStart_953375 : Nat := 118140960795 + 953375 * 2 ^ 59
def prefixEnd_953375 : Nat := 4983230072969 + 3 ^ 40 * 953375 * 2
def baseEnd_953375 : Nat := 48349591998055570333631

theorem tailTrace_953375 : CollatzResearch.WordTrace tailWord_953375 prefixEnd_953375 48349591998055570333631 := by
  unfold tailWord_953375
  simp only [CollatzResearch.WordTrace]
  refine ⟨34772442921092673332069579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23181628614061782221379719 34772442921092673332069579)
  ·
    refine ⟨52158664381639009998104369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34772442921092673332069579 52158664381639009998104369)
    ·
      refine ⟨39118998286229257498578277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52158664381639009998104369 39118998286229257498578277)
      ·
        refine ⟨7334812178667985780983427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39118998286229257498578277 7334812178667985780983427)
        ·
          refine ⟨11002218268001978671475141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334812178667985780983427 11002218268001978671475141)
          ·
            refine ⟨2062915925250371000901589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11002218268001978671475141 2062915925250371000901589)
            ·
              refine ⟨48349591998055570333631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2062915925250371000901589 48349591998055570333631)
              ·
                rfl

theorem cell20_953375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_953375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953375 prefixEnd_953375 := by exact prefixLift 953375
  have htrace : WordTrace (prefixWord ++ tailWord_953375) baseStart_953375 baseEnd_953375 := by
    simpa [prefixWord, tailWord_953375, baseEnd_953375] using wordTrace_append hprefix tailTrace_953375
  have hstable : (prefixWord ++ tailWord_953375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953375).length < 2 ^ (prefixWord ++ tailWord_953375).sum := by decide
  have hdescent : baseEnd_953375 < baseStart_953375 := by decide
  rcases family_descends (prefixWord ++ tailWord_953375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953378 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_953378 : Nat := 118140960795 + 953378 * 2 ^ 59
def prefixEnd_953378 : Nat := 4983230072969 + 3 ^ 40 * 953378 * 2
def baseEnd_953378 : Nat := 435147697264245455902667

theorem tailTrace_953378 : CollatzResearch.WordTrace tailWord_953378 prefixEnd_953378 435147697264245455902667 := by
  unfold tailWord_953378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8693138085020451211107197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23181701560054536562952525 8693138085020451211107197)
  ·
    refine ⟨3259926781882669204165199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8693138085020451211107197 3259926781882669204165199)
    ·
      refine ⟨4889890172824003806247799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3259926781882669204165199 4889890172824003806247799)
      ·
        refine ⟨7334835259236005709371699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889890172824003806247799 7334835259236005709371699)
        ·
          refine ⟨11002252888854008564057549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334835259236005709371699 11002252888854008564057549)
          ·
            refine ⟨4125844833320253211521581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11002252888854008564057549 4125844833320253211521581)
            ·
              refine ⟨1547191812495094954320593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4125844833320253211521581 1547191812495094954320593)
              ·
                refine ⟨1160393859371321215740445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547191812495094954320593 1160393859371321215740445)
                ·
                  refine ⟨435147697264245455902667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160393859371321215740445 435147697264245455902667)
                  ·
                    rfl

theorem cell20_953378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_953378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953378 prefixEnd_953378 := by exact prefixLift 953378
  have htrace : WordTrace (prefixWord ++ tailWord_953378) baseStart_953378 baseEnd_953378 := by
    simpa [prefixWord, tailWord_953378, baseEnd_953378] using wordTrace_append hprefix tailTrace_953378
  have hstable : (prefixWord ++ tailWord_953378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953378).length < 2 ^ (prefixWord ++ tailWord_953378).sum := by decide
  have hdescent : baseEnd_953378 < baseStart_953378 := by decide
  rcases family_descends (prefixWord ++ tailWord_953378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953427 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_953427 : Nat := 118140960795 + 953427 * 2 ^ 59
def prefixEnd_953427 : Nat := 4983230072969 + 3 ^ 40 * 953427 * 2
def baseEnd_953427 : Nat := 435170062199419063269133

theorem tailTrace_953427 : CollatzResearch.WordTrace tailWord_953427 prefixEnd_953427 435170062199419063269133 := by
  unfold tailWord_953427
  simp only [CollatzResearch.WordTrace]
  refine ⟨34774339516904286212962535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23182893011269524141975023 34774339516904286212962535)
  ·
    refine ⟨52161509275356429319443803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34774339516904286212962535 52161509275356429319443803)
    ·
      refine ⟨78242263913034643979165705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52161509275356429319443803 78242263913034643979165705)
      ·
        refine ⟨58681697934775982984374279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78242263913034643979165705 58681697934775982984374279)
        ·
          refine ⟨88022546902163974476561419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58681697934775982984374279 88022546902163974476561419)
          ·
            refine ⟨132033820353245961714842129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88022546902163974476561419 132033820353245961714842129)
            ·
              refine ⟨99025365264934471286131597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132033820353245961714842129 99025365264934471286131597)
              ·
                refine ⟨37134511974350426732299349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99025365264934471286131597 37134511974350426732299349)
                ·
                  refine ⟨435170062199419063269133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37134511974350426732299349 435170062199419063269133)
                  ·
                    rfl

theorem cell20_953427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_953427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953427 prefixEnd_953427 := by exact prefixLift 953427
  have htrace : WordTrace (prefixWord ++ tailWord_953427) baseStart_953427 baseEnd_953427 := by
    simpa [prefixWord, tailWord_953427, baseEnd_953427] using wordTrace_append hprefix tailTrace_953427
  have hstable : (prefixWord ++ tailWord_953427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953427).length < 2 ^ (prefixWord ++ tailWord_953427).sum := by decide
  have hdescent : baseEnd_953427 < baseStart_953427 := by decide
  rcases family_descends (prefixWord ++ tailWord_953427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953440 : List Nat := [2, 1, 1, 3, 2, 2, 5, 2, 2]
def baseStart_953440 : Nat := 118140960795 + 953440 * 2 ^ 59
def prefixEnd_953440 : Nat := 4983230072969 + 3 ^ 40 * 953440 * 2
def baseEnd_953440 : Nat := 435175995753648795835747

theorem tailTrace_953440 : CollatzResearch.WordTrace tailWord_953440 prefixEnd_953440 435175995753648795835747 := by
  unfold tailWord_953440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17387406832928594716592887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23183209110571459622123849 17387406832928594716592887)
  ·
    refine ⟨26081110249392892074889331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17387406832928594716592887 26081110249392892074889331)
    ·
      refine ⟨39121665374089338112333997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26081110249392892074889331 39121665374089338112333997)
      ·
        refine ⟨14670624515283501792125249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39121665374089338112333997 14670624515283501792125249)
        ·
          refine ⟨11002968386462626344093937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14670624515283501792125249 11002968386462626344093937)
          ·
            refine ⟨8252226289846969758070453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11002968386462626344093937 8252226289846969758070453)
            ·
              refine ⟨773646214673153414819105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8252226289846969758070453 773646214673153414819105)
              ·
                refine ⟨580234661004865061114329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773646214673153414819105 580234661004865061114329)
                ·
                  refine ⟨435175995753648795835747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580234661004865061114329 435175995753648795835747)
                  ·
                    rfl

theorem cell20_953440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_953440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953440 prefixEnd_953440 := by exact prefixLift 953440
  have htrace : WordTrace (prefixWord ++ tailWord_953440) baseStart_953440 baseEnd_953440 := by
    simpa [prefixWord, tailWord_953440, baseEnd_953440] using wordTrace_append hprefix tailTrace_953440
  have hstable : (prefixWord ++ tailWord_953440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953440).length < 2 ^ (prefixWord ++ tailWord_953440).sum := by decide
  have hdescent : baseEnd_953440 < baseStart_953440 := by decide
  rcases family_descends (prefixWord ++ tailWord_953440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953454 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_953454 : Nat := 118140960795 + 953454 * 2 ^ 59
def prefixEnd_953454 : Nat := 4983230072969 + 3 ^ 40 * 953454 * 2
def baseEnd_953454 : Nat := 435182385735126969369023

theorem tailTrace_953454 : CollatzResearch.WordTrace tailWord_953454 prefixEnd_953454 435182385735126969369023 := by
  unfold tailWord_953454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346915535975808728024427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23183549525204313216130277 4346915535975808728024427)
  ·
    refine ⟨6520373303963713092036641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4346915535975808728024427 6520373303963713092036641)
    ·
      refine ⟨4890279977972784819027481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6520373303963713092036641 4890279977972784819027481)
      ·
        refine ⟨3667709983479588614270611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4890279977972784819027481 3667709983479588614270611)
        ·
          refine ⟨5501564975219382921405917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667709983479588614270611 5501564975219382921405917)
          ·
            refine ⟨2063086865707268595527219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5501564975219382921405917 2063086865707268595527219)
            ·
              refine ⟨3094630298560902893290829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063086865707268595527219 3094630298560902893290829)
              ·
                refine ⟨1160486361960338584984061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3094630298560902893290829 1160486361960338584984061)
                ·
                  refine ⟨435182385735126969369023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160486361960338584984061 435182385735126969369023)
                  ·
                    rfl

theorem cell20_953454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_953454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953454 prefixEnd_953454 := by exact prefixLift 953454
  have htrace : WordTrace (prefixWord ++ tailWord_953454) baseStart_953454 baseEnd_953454 := by
    simpa [prefixWord, tailWord_953454, baseEnd_953454] using wordTrace_append hprefix tailTrace_953454
  have hstable : (prefixWord ++ tailWord_953454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953454).length < 2 ^ (prefixWord ++ tailWord_953454).sum := by decide
  have hdescent : baseEnd_953454 < baseStart_953454 := by decide
  rcases family_descends (prefixWord ++ tailWord_953454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953495 : List Nat := [1, 1, 3, 3, 3, 3, 2, 2, 2]
def baseStart_953495 : Nat := 118140960795 + 953495 * 2 ^ 59
def prefixEnd_953495 : Nat := 4983230072969 + 3 ^ 40 * 953495 * 2
def baseEnd_953495 : Nat := 435201099252313049002189

theorem tailTrace_953495 : CollatzResearch.WordTrace tailWord_953495 prefixEnd_953495 435201099252313049002189 := by
  unfold tailWord_953495
  simp only [CollatzResearch.WordTrace]
  refine ⟨34776819680657933826437939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23184546453771955884291959 34776819680657933826437939)
  ·
    refine ⟨52165229520986900739656909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34776819680657933826437939 52165229520986900739656909)
    ·
      refine ⟨19561961070370087777371341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52165229520986900739656909 19561961070370087777371341)
      ·
        refine ⟨7335735401388782916514253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19561961070370087777371341 7335735401388782916514253)
        ·
          refine ⟨2750900775520793593692845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7335735401388782916514253 2750900775520793593692845)
          ·
            refine ⟨1031587790820297597634817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2750900775520793593692845 1031587790820297597634817)
            ·
              refine ⟨773690843115223198226113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031587790820297597634817 773690843115223198226113)
              ·
                refine ⟨580268132336417398669585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773690843115223198226113 580268132336417398669585)
                ·
                  refine ⟨435201099252313049002189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580268132336417398669585 435201099252313049002189)
                  ·
                    rfl

theorem cell20_953495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2].length) (baseStart_953495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953495 prefixEnd_953495 := by exact prefixLift 953495
  have htrace : WordTrace (prefixWord ++ tailWord_953495) baseStart_953495 baseEnd_953495 := by
    simpa [prefixWord, tailWord_953495, baseEnd_953495] using wordTrace_append hprefix tailTrace_953495
  have hstable : (prefixWord ++ tailWord_953495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953495).length < 2 ^ (prefixWord ++ tailWord_953495).sum := by decide
  have hdescent : baseEnd_953495 < baseStart_953495 := by decide
  rcases family_descends (prefixWord ++ tailWord_953495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953541 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_953541 : Nat := 118140960795 + 953541 * 2 ^ 59
def prefixEnd_953541 : Nat := 4983230072969 + 3 ^ 40 * 953541 * 2
def baseEnd_953541 : Nat := 435222094905741333468667

theorem tailTrace_953541 : CollatzResearch.WordTrace tailWord_953541 prefixEnd_953541 435222094905741333468667 := by
  unfold tailWord_953541
  simp only [CollatzResearch.WordTrace]
  refine ⟨34778497438491283682612477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23185664958994189121741651 34778497438491283682612477)
  ·
    refine ⟨13041936539434231380979679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34778497438491283682612477 13041936539434231380979679)
    ·
      refine ⟨19562904809151347071469519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13041936539434231380979679 19562904809151347071469519)
      ·
        refine ⟨29344357213727020607204279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19562904809151347071469519 29344357213727020607204279)
        ·
          refine ⟨44016535820590530910806419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29344357213727020607204279 44016535820590530910806419)
          ·
            refine ⟨66024803730885796366209629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44016535820590530910806419 66024803730885796366209629)
            ·
              refine ⟨24759301399082173637328611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66024803730885796366209629 24759301399082173637328611)
              ·
                refine ⟨37138952098623260455992917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24759301399082173637328611 37138952098623260455992917)
                ·
                  refine ⟨435222094905741333468667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37138952098623260455992917 435222094905741333468667)
                  ·
                    rfl

theorem cell20_953541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_953541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953541 prefixEnd_953541 := by exact prefixLift 953541
  have htrace : WordTrace (prefixWord ++ tailWord_953541) baseStart_953541 baseEnd_953541 := by
    simpa [prefixWord, tailWord_953541, baseEnd_953541] using wordTrace_append hprefix tailTrace_953541
  have hstable : (prefixWord ++ tailWord_953541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953541).length < 2 ^ (prefixWord ++ tailWord_953541).sum := by decide
  have hdescent : baseEnd_953541 < baseStart_953541 := by decide
  rcases family_descends (prefixWord ++ tailWord_953541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953568 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_953568 : Nat := 118140960795 + 953568 * 2 ^ 59
def prefixEnd_953568 : Nat := 4983230072969 + 3 ^ 40 * 953568 * 2
def baseEnd_953568 : Nat := 435234418441449239568557

theorem tailTrace_953568 : CollatzResearch.WordTrace tailWord_953568 prefixEnd_953568 435234418441449239568557 := by
  unfold tailWord_953568
  simp only [CollatzResearch.WordTrace]
  refine ⟨17389741104696733646922679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23186321472928978195896905 17389741104696733646922679)
  ·
    refine ⟨26084611657045100470384019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17389741104696733646922679 26084611657045100470384019)
    ·
      refine ⟨39126917485567650705576029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26084611657045100470384019 39126917485567650705576029)
      ·
        refine ⟨14672594057087869014591011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39126917485567650705576029 14672594057087869014591011)
        ·
          refine ⟨22008891085631803521886517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14672594057087869014591011 22008891085631803521886517)
          ·
            refine ⟨2063333539277981580176861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22008891085631803521886517 2063333539277981580176861)
            ·
              refine ⟨773750077229243092566323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2063333539277981580176861 773750077229243092566323)
              ·
                refine ⟨1160625115843864638849485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773750077229243092566323 1160625115843864638849485)
                ·
                  refine ⟨435234418441449239568557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160625115843864638849485 435234418441449239568557)
                  ·
                    rfl

theorem cell20_953568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_953568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953568 prefixEnd_953568 := by exact prefixLift 953568
  have htrace : WordTrace (prefixWord ++ tailWord_953568) baseStart_953568 baseEnd_953568 := by
    simpa [prefixWord, tailWord_953568, baseEnd_953568] using wordTrace_append hprefix tailTrace_953568
  have hstable : (prefixWord ++ tailWord_953568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953568).length < 2 ^ (prefixWord ++ tailWord_953568).sum := by decide
  have hdescent : baseEnd_953568 < baseStart_953568 := by decide
  rcases family_descends (prefixWord ++ tailWord_953568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953582 : List Nat := [4, 1, 2, 1, 1, 1, 6, 4]
def baseStart_953582 : Nat := 118140960795 + 953582 * 2 ^ 59
def prefixEnd_953582 : Nat := 4983230072969 + 3 ^ 40 * 953582 * 2
def baseEnd_953582 : Nat := 145080269474309137700611

theorem tailTrace_953582 : CollatzResearch.WordTrace tailWord_953582 prefixEnd_953582 145080269474309137700611 := by
  unfold tailWord_953582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4347499103917843460606875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23186661887561831789903333 4347499103917843460606875)
  ·
    refine ⟨6521248655876765190910313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4347499103917843460606875 6521248655876765190910313)
    ·
      refine ⟨4890936491907573893182735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6521248655876765190910313 4890936491907573893182735)
      ·
        refine ⟨7336404737861360839774103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890936491907573893182735 7336404737861360839774103)
        ·
          refine ⟨11004607106792041259661155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7336404737861360839774103 11004607106792041259661155)
          ·
            refine ⟨16506910660188061889491733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11004607106792041259661155 16506910660188061889491733)
            ·
              refine ⟨773761437196315401069925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16506910660188061889491733 773761437196315401069925)
              ·
                refine ⟨145080269474309137700611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773761437196315401069925 145080269474309137700611)
                ·
                  rfl

theorem cell20_953582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_953582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953582 prefixEnd_953582 := by exact prefixLift 953582
  have htrace : WordTrace (prefixWord ++ tailWord_953582) baseStart_953582 baseEnd_953582 := by
    simpa [prefixWord, tailWord_953582, baseEnd_953582] using wordTrace_append hprefix tailTrace_953582
  have hstable : (prefixWord ++ tailWord_953582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953582).length < 2 ^ (prefixWord ++ tailWord_953582).sum := by decide
  have hdescent : baseEnd_953582 < baseStart_953582 := by decide
  rcases family_descends (prefixWord ++ tailWord_953582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953603 : List Nat := [1, 1, 1, 3, 2, 6, 6]
def baseStart_953603 : Nat := 118140960795 + 953603 * 2 ^ 59
def prefixEnd_953603 : Nat := 4983230072969 + 3 ^ 40 * 953603 * 2
def baseEnd_953603 : Nat := 48361154821682741489083

theorem tailTrace_953603 : CollatzResearch.WordTrace tailWord_953603 prefixEnd_953603 48361154821682741489083 := by
  unfold tailWord_953603
  simp only [CollatzResearch.WordTrace]
  refine ⟨34780758764266668271369463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23187172509511112180912975 34780758764266668271369463)
  ·
    refine ⟨52171138146400002407054195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34780758764266668271369463 52171138146400002407054195)
    ·
      refine ⟨78256707219600003610581293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52171138146400002407054195 78256707219600003610581293)
      ·
        refine ⟨29346265207350001353967985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78256707219600003610581293 29346265207350001353967985)
        ·
          refine ⟨22009698905512501015475989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29346265207350001353967985 22009698905512501015475989)
          ·
            refine ⟨1031704636195898485100437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22009698905512501015475989 1031704636195898485100437)
            ·
              refine ⟨48361154821682741489083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1031704636195898485100437 48361154821682741489083)
              ·
                rfl

theorem cell20_953603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 6].length) (baseStart_953603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953603 prefixEnd_953603 := by exact prefixLift 953603
  have htrace : WordTrace (prefixWord ++ tailWord_953603) baseStart_953603 baseEnd_953603 := by
    simpa [prefixWord, tailWord_953603, baseEnd_953603] using wordTrace_append hprefix tailTrace_953603
  have hstable : (prefixWord ++ tailWord_953603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953603).length < 2 ^ (prefixWord ++ tailWord_953603).sum := by decide
  have hdescent : baseEnd_953603 < baseStart_953603 := by decide
  rcases family_descends (prefixWord ++ tailWord_953603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953661 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 3]
def baseStart_953661 : Nat := 118140960795 + 953661 * 2 ^ 59
def prefixEnd_953661 : Nat := 4983230072969 + 3 ^ 40 * 953661 * 2
def baseEnd_953661 : Nat := 435276866175554249468177

theorem tailTrace_953661 : CollatzResearch.WordTrace tailWord_953661 prefixEnd_953661 435276866175554249468177 := by
  unfold tailWord_953661
  simp only [CollatzResearch.WordTrace]
  refine ⟨34782874198056544176980837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23188582798704362784653891 34782874198056544176980837)
  ·
    refine ⟨6521788912135602033183907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34782874198056544176980837 6521788912135602033183907)
    ·
      refine ⟨9782683368203403049775861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6521788912135602033183907 9782683368203403049775861)
      ·
        refine ⟨917126565769069035916487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9782683368203403049775861 917126565769069035916487)
        ·
          refine ⟨1375689848653603553874731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917126565769069035916487 1375689848653603553874731)
          ·
            refine ⟨2063534772980405330812097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375689848653603553874731 2063534772980405330812097)
            ·
              refine ⟨1547651079735303998109073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063534772980405330812097 1547651079735303998109073)
              ·
                refine ⟨1160738309801477998581805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547651079735303998109073 1160738309801477998581805)
                ·
                  refine ⟨435276866175554249468177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160738309801477998581805 435276866175554249468177)
                  ·
                    rfl

theorem cell20_953661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_953661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953661 prefixEnd_953661 := by exact prefixLift 953661
  have htrace : WordTrace (prefixWord ++ tailWord_953661) baseStart_953661 baseEnd_953661 := by
    simpa [prefixWord, tailWord_953661, baseEnd_953661] using wordTrace_append hprefix tailTrace_953661
  have hstable : (prefixWord ++ tailWord_953661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953661).length < 2 ^ (prefixWord ++ tailWord_953661).sum := by decide
  have hdescent : baseEnd_953661 < baseStart_953661 := by decide
  rcases family_descends (prefixWord ++ tailWord_953661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953696 : List Nat := [2, 1, 1, 3, 4, 2, 3, 4]
def baseStart_953696 : Nat := 118140960795 + 953696 * 2 ^ 59
def prefixEnd_953696 : Nat := 4983230072969 + 3 ^ 40 * 953696 * 2
def baseEnd_953696 : Nat := 145097613709749894433789

theorem tailTrace_953696 : CollatzResearch.WordTrace tailWord_953696 prefixEnd_953696 145097613709749894433789 := by
  unfold tailWord_953696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17392075376464872577252471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23189433835286496769669961 17392075376464872577252471)
  ·
    refine ⟨26088113064697308865878707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17392075376464872577252471 26088113064697308865878707)
    ·
      refine ⟨39132169597045963298818061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26088113064697308865878707 39132169597045963298818061)
      ·
        refine ⟨14674563598892236237056773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39132169597045963298818061 14674563598892236237056773)
        ·
          refine ⟨2751480674792294294448145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14674563598892236237056773 2751480674792294294448145)
          ·
            refine ⟨2063610506094220720836109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751480674792294294448145 2063610506094220720836109)
            ·
              refine ⟨773853939785332770313541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2063610506094220720836109 773853939785332770313541)
              ·
                refine ⟨145097613709749894433789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773853939785332770313541 145097613709749894433789)
                ·
                  rfl

theorem cell20_953696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_953696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953696 prefixEnd_953696 := by exact prefixLift 953696
  have htrace : WordTrace (prefixWord ++ tailWord_953696) baseStart_953696 baseEnd_953696 := by
    simpa [prefixWord, tailWord_953696, baseEnd_953696] using wordTrace_append hprefix tailTrace_953696
  have hstable : (prefixWord ++ tailWord_953696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953696).length < 2 ^ (prefixWord ++ tailWord_953696).sum := by decide
  have hdescent : baseEnd_953696 < baseStart_953696 := by decide
  rcases family_descends (prefixWord ++ tailWord_953696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953724 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_953724 : Nat := 118140960795 + 953724 * 2 ^ 59
def prefixEnd_953724 : Nat := 4983230072969 + 3 ^ 40 * 953724 * 2
def baseEnd_953724 : Nat := 435305621092206030367919

theorem tailTrace_953724 : CollatzResearch.WordTrace tailWord_953724 prefixEnd_953724 435305621092206030367919 := by
  unfold tailWord_953724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17392585998414152968262113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23190114664552203957682817 17392585998414152968262113)
  ·
    refine ⟨13044439498810614726196585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17392585998414152968262113 13044439498810614726196585)
    ·
      refine ⟨9783329624107961044647439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13044439498810614726196585 9783329624107961044647439)
      ·
        refine ⟨14674994436161941566971159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9783329624107961044647439 14674994436161941566971159)
        ·
          refine ⟨22012491654242912350456739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14674994436161941566971159 22012491654242912350456739)
          ·
            refine ⟨33018737481364368525685109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22012491654242912350456739 33018737481364368525685109)
            ·
              refine ⟨3095506638877909549282979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33018737481364368525685109 3095506638877909549282979)
              ·
                refine ⟨4643259958316864323924469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095506638877909549282979 4643259958316864323924469)
                ·
                  refine ⟨435305621092206030367919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4643259958316864323924469 435305621092206030367919)
                  ·
                    rfl

theorem cell20_953724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_953724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953724 prefixEnd_953724 := by exact prefixLift 953724
  have htrace : WordTrace (prefixWord ++ tailWord_953724) baseStart_953724 baseEnd_953724 := by
    simpa [prefixWord, tailWord_953724, baseEnd_953724] using wordTrace_append hprefix tailTrace_953724
  have hstable : (prefixWord ++ tailWord_953724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953724).length < 2 ^ (prefixWord ++ tailWord_953724).sum := by decide
  have hdescent : baseEnd_953724 < baseStart_953724 := by decide
  rcases family_descends (prefixWord ++ tailWord_953724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953796 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_953796 : Nat := 118140960795 + 953796 * 2 ^ 59
def prefixEnd_953796 : Nat := 4983230072969 + 3 ^ 40 * 953796 * 2
def baseEnd_953796 : Nat := 435338483854093779967625

theorem tailTrace_953796 : CollatzResearch.WordTrace tailWord_953796 prefixEnd_953796 435338483854093779967625 := by
  unfold tailWord_953796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17393899026283731116572621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23191865368378308155430161 17393899026283731116572621)
  ·
    refine ⟨6522712134856399168714733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17393899026283731116572621 6522712134856399168714733)
    ·
      refine ⟨2446017050571149688268025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6522712134856399168714733 2446017050571149688268025)
      ·
        refine ⟨1834512787928362266201019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2446017050571149688268025 1834512787928362266201019)
        ·
          refine ⟨2751769181892543399301529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834512787928362266201019 2751769181892543399301529)
          ·
            refine ⟨2063826886419407549476147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751769181892543399301529 2063826886419407549476147)
            ·
              refine ⟨3095740329629111324214221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063826886419407549476147 3095740329629111324214221)
              ·
                refine ⟨1160902623610916746580333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3095740329629111324214221 1160902623610916746580333)
                ·
                  refine ⟨435338483854093779967625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160902623610916746580333 435338483854093779967625)
                  ·
                    rfl

theorem cell20_953796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_953796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953796 prefixEnd_953796 := by exact prefixLift 953796
  have htrace : WordTrace (prefixWord ++ tailWord_953796) baseStart_953796 baseEnd_953796 := by
    simpa [prefixWord, tailWord_953796, baseEnd_953796] using wordTrace_append hprefix tailTrace_953796
  have hstable : (prefixWord ++ tailWord_953796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953796).length < 2 ^ (prefixWord ++ tailWord_953796).sum := by decide
  have hdescent : baseEnd_953796 < baseStart_953796 := by decide
  rcases family_descends (prefixWord ++ tailWord_953796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953807 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_953807 : Nat := 118140960795 + 953807 * 2 ^ 59
def prefixEnd_953807 : Nat := 4983230072969 + 3 ^ 40 * 953807 * 2
def baseEnd_953807 : Nat := 435343504553826630600913

theorem tailTrace_953807 : CollatzResearch.WordTrace tailWord_953807 prefixEnd_953807 435343504553826630600913 := by
  unfold tailWord_953807
  simp only [CollatzResearch.WordTrace]
  refine ⟨34788199255527611111795675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23192132837018407407863783 34788199255527611111795675)
  ·
    refine ⟨52182298883291416667693513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34788199255527611111795675 52182298883291416667693513)
    ·
      refine ⟨39136724162468562500770135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52182298883291416667693513 39136724162468562500770135)
      ·
        refine ⟨58705086243702843751155203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39136724162468562500770135 58705086243702843751155203)
        ·
          refine ⟨88057629365554265626732805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58705086243702843751155203 88057629365554265626732805)
          ·
            refine ⟨16510805506041424805012401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88057629365554265626732805 16510805506041424805012401)
            ·
              refine ⟨12383104129531068603759301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16510805506041424805012401 12383104129531068603759301)
              ·
                refine ⟨2321832024287075363204869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12383104129531068603759301 2321832024287075363204869)
                ·
                  refine ⟨435343504553826630600913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321832024287075363204869 435343504553826630600913)
                  ·
                    rfl

theorem cell20_953807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_953807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953807 prefixEnd_953807 := by exact prefixLift 953807
  have htrace : WordTrace (prefixWord ++ tailWord_953807) baseStart_953807 baseEnd_953807 := by
    simpa [prefixWord, tailWord_953807, baseEnd_953807] using wordTrace_append hprefix tailTrace_953807
  have hstable : (prefixWord ++ tailWord_953807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953807).length < 2 ^ (prefixWord ++ tailWord_953807).sum := by decide
  have hdescent : baseEnd_953807 < baseStart_953807 := by decide
  rcases family_descends (prefixWord ++ tailWord_953807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953834 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_953834 : Nat := 118140960795 + 953834 * 2 ^ 59
def prefixEnd_953834 : Nat := 4983230072969 + 3 ^ 40 * 953834 * 2
def baseEnd_953834 : Nat := 435355828089534536700803

theorem tailTrace_953834 : CollatzResearch.WordTrace tailWord_953834 prefixEnd_953834 435355828089534536700803 := by
  unfold tailWord_953834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697296006607448680757139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23192789350953196482019037 8697296006607448680757139)
  ·
    refine ⟨13045944009911173021135709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8697296006607448680757139 13045944009911173021135709)
    ·
      refine ⟨4892229003716689882925891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13045944009911173021135709 4892229003716689882925891)
      ·
        refine ⟨7338343505575034824388837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892229003716689882925891 7338343505575034824388837)
        ·
          refine ⟨1375939407295319029572907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7338343505575034824388837 1375939407295319029572907)
          ·
            refine ⟨2063909110942978544359361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375939407295319029572907 2063909110942978544359361)
            ·
              refine ⟨1547931833207233908269521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063909110942978544359361 1547931833207233908269521)
              ·
                refine ⟨1160948874905425431202141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547931833207233908269521 1160948874905425431202141)
                ·
                  refine ⟨435355828089534536700803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1160948874905425431202141 435355828089534536700803)
                  ·
                    rfl

theorem cell20_953834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_953834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953834 prefixEnd_953834 := by exact prefixLift 953834
  have htrace : WordTrace (prefixWord ++ tailWord_953834) baseStart_953834 baseEnd_953834 := by
    simpa [prefixWord, tailWord_953834, baseEnd_953834] using wordTrace_append hprefix tailTrace_953834
  have hstable : (prefixWord ++ tailWord_953834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953834).length < 2 ^ (prefixWord ++ tailWord_953834).sum := by decide
  have hdescent : baseEnd_953834 < baseStart_953834 := by decide
  rcases family_descends (prefixWord ++ tailWord_953834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953841 : List Nat := [1, 2, 2, 2, 3, 3, 1, 4, 2]
def baseStart_953841 : Nat := 118140960795 + 953841 * 2 ^ 59
def prefixEnd_953841 : Nat := 4983230072969 + 3 ^ 40 * 953841 * 2
def baseEnd_953841 : Nat := 435359023080273623467441

theorem tailTrace_953841 : CollatzResearch.WordTrace tailWord_953841 prefixEnd_953841 435359023080273623467441 := by
  unfold tailWord_953841
  simp only [CollatzResearch.WordTrace]
  refine ⟨34789439337404434918533377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23192959558269623279022251 34789439337404434918533377)
  ·
    refine ⟨26092079503053326188900033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34789439337404434918533377 26092079503053326188900033)
    ·
      refine ⟨19569059627289994641675025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26092079503053326188900033 19569059627289994641675025)
      ·
        refine ⟨14676794720467495981256269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19569059627289994641675025 14676794720467495981256269)
        ·
          refine ⟨5503798020175310992971101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14676794720467495981256269 5503798020175310992971101)
          ·
            refine ⟨2063924257565741622364163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5503798020175310992971101 2063924257565741622364163)
            ·
              refine ⟨3095886386348612433546245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063924257565741622364163 3095886386348612433546245)
              ·
                refine ⟨580478697440364831289921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3095886386348612433546245 580478697440364831289921)
                ·
                  refine ⟨435359023080273623467441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580478697440364831289921 435359023080273623467441)
                  ·
                    rfl

theorem cell20_953841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_953841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953841 prefixEnd_953841 := by exact prefixLift 953841
  have htrace : WordTrace (prefixWord ++ tailWord_953841) baseStart_953841 baseEnd_953841 := by
    simpa [prefixWord, tailWord_953841, baseEnd_953841] using wordTrace_append hprefix tailTrace_953841
  have hstable : (prefixWord ++ tailWord_953841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953841).length < 2 ^ (prefixWord ++ tailWord_953841).sum := by decide
  have hdescent : baseEnd_953841 < baseStart_953841 := by decide
  rcases family_descends (prefixWord ++ tailWord_953841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953952 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_953952 : Nat := 118140960795 + 953952 * 2 ^ 59
def prefixEnd_953952 : Nat := 4983230072969 + 3 ^ 40 * 953952 * 2
def baseEnd_953952 : Nat := 435409686504850570766987

theorem tailTrace_953952 : CollatzResearch.WordTrace tailWord_953952 prefixEnd_953952 435409686504850570766987 := by
  unfold tailWord_953952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396743920001150437912055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23195658560001533917216073 17396743920001150437912055)
  ·
    refine ⟨26095115880001725656868083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17396743920001150437912055 26095115880001725656868083)
    ·
      refine ⟨39142673820002588485302125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26095115880001725656868083 39142673820002588485302125)
      ·
        refine ⟨14678502682500970681988297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39142673820002588485302125 14678502682500970681988297)
        ·
          refine ⟨11008877011875728011491223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14678502682500970681988297 11008877011875728011491223)
          ·
            refine ⟨16513315517813592017236835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11008877011875728011491223 16513315517813592017236835)
            ·
              refine ⟨24769973276720388025855253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16513315517813592017236835 24769973276720388025855253)
              ·
                refine ⟨1161092497346268188711965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24769973276720388025855253 1161092497346268188711965)
                ·
                  refine ⟨435409686504850570766987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161092497346268188711965 435409686504850570766987)
                  ·
                    rfl

theorem cell20_953952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_953952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953952 prefixEnd_953952 := by exact prefixLift 953952
  have htrace : WordTrace (prefixWord ++ tailWord_953952) baseStart_953952 baseEnd_953952 := by
    simpa [prefixWord, tailWord_953952, baseEnd_953952] using wordTrace_append hprefix tailTrace_953952
  have hstable : (prefixWord ++ tailWord_953952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953952).length < 2 ^ (prefixWord ++ tailWord_953952).sum := by decide
  have hdescent : baseEnd_953952 < baseStart_953952 := by decide
  rcases family_descends (prefixWord ++ tailWord_953952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953965 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 3]
def baseStart_953965 : Nat := 118140960795 + 953965 * 2 ^ 59
def prefixEnd_953965 : Nat := 4983230072969 + 3 ^ 40 * 953965 * 2
def baseEnd_953965 : Nat := 435415620059080303333601

theorem tailTrace_953965 : CollatzResearch.WordTrace tailWord_953965 prefixEnd_953965 435415620059080303333601 := by
  unfold tailWord_953965
  simp only [CollatzResearch.WordTrace]
  refine ⟨34793961988955204096047349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23195974659303469397364899 34793961988955204096047349)
  ·
    refine ⟨3261933936464550384004439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34793961988955204096047349 3261933936464550384004439)
    ·
      refine ⟨4892900904696825576006659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261933936464550384004439 4892900904696825576006659)
      ·
        refine ⟨7339351357045238364009989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892900904696825576006659 7339351357045238364009989)
        ·
          refine ⟨1376128379445982193251873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7339351357045238364009989 1376128379445982193251873)
          ·
            refine ⟨1032096284584486644938905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1376128379445982193251873 1032096284584486644938905)
            ·
              refine ⟨774072213438364983704179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032096284584486644938905 774072213438364983704179)
              ·
                refine ⟨1161108320157547475556269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774072213438364983704179 1161108320157547475556269)
                ·
                  refine ⟨435415620059080303333601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161108320157547475556269 435415620059080303333601)
                  ·
                    rfl

theorem cell20_953965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_953965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_953965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_953965 prefixEnd_953965 := by exact prefixLift 953965
  have htrace : WordTrace (prefixWord ++ tailWord_953965) baseStart_953965 baseEnd_953965 := by
    simpa [prefixWord, tailWord_953965, baseEnd_953965] using wordTrace_append hprefix tailTrace_953965
  have hstable : (prefixWord ++ tailWord_953965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953965).length < 2 ^ (prefixWord ++ tailWord_953965).sum := by decide
  have hdescent : baseEnd_953965 < baseStart_953965 := by decide
  rcases family_descends (prefixWord ++ tailWord_953965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954007 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 3]
def baseStart_954007 : Nat := 118140960795 + 954007 * 2 ^ 59
def prefixEnd_954007 : Nat := 4983230072969 + 3 ^ 40 * 954007 * 2
def baseEnd_954007 : Nat := 435434790003514823933429

theorem tailTrace_954007 : CollatzResearch.WordTrace tailWord_954007 prefixEnd_954007 435434790003514823933429 := by
  unfold tailWord_954007
  simp only [CollatzResearch.WordTrace]
  refine ⟨34795493854803045269076275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23196995903202030179384183 34795493854803045269076275)
  ·
    refine ⟨52193240782204567903614413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34795493854803045269076275 52193240782204567903614413)
    ·
      refine ⟨19572465293326712963855405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52193240782204567903614413 19572465293326712963855405)
      ·
        refine ⟨7339674484997517361445777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19572465293326712963855405 7339674484997517361445777)
        ·
          refine ⟨5504755863748138021084333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7339674484997517361445777 5504755863748138021084333)
          ·
            refine ⟨2064283448905551757906625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5504755863748138021084333 2064283448905551757906625)
            ·
              refine ⟨1548212586679163818429969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064283448905551757906625 1548212586679163818429969)
              ·
                refine ⟨1161159440009372863822477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548212586679163818429969 1161159440009372863822477)
                ·
                  refine ⟨435434790003514823933429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161159440009372863822477 435434790003514823933429)
                  ·
                    rfl

theorem cell20_954007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_954007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954007 prefixEnd_954007 := by exact prefixLift 954007
  have htrace : WordTrace (prefixWord ++ tailWord_954007) baseStart_954007 baseEnd_954007 := by
    simpa [prefixWord, tailWord_954007, baseEnd_954007] using wordTrace_append hprefix tailTrace_954007
  have hstable : (prefixWord ++ tailWord_954007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954007).length < 2 ^ (prefixWord ++ tailWord_954007).sum := by decide
  have hdescent : baseEnd_954007 < baseStart_954007 := by decide
  rcases family_descends (prefixWord ++ tailWord_954007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954035 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_954035 : Nat := 118140960795 + 954035 * 2 ^ 59
def prefixEnd_954035 : Nat := 4983230072969 + 3 ^ 40 * 954035 * 2
def baseEnd_954035 : Nat := 435447569966471170999981

theorem tailTrace_954035 : CollatzResearch.WordTrace tailWord_954035 prefixEnd_954035 435447569966471170999981 := by
  unfold tailWord_954035
  simp only [CollatzResearch.WordTrace]
  refine ⟨34796515098701606051095559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23197676732467737367397039 34796515098701606051095559)
  ·
    refine ⟨52194772648052409076643339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34796515098701606051095559 52194772648052409076643339)
    ·
      refine ⟨78292158972078613614965009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52194772648052409076643339 78292158972078613614965009)
      ·
        refine ⟨58719119229058960211223757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78292158972078613614965009 58719119229058960211223757)
        ·
          refine ⟨22019669710897110079208909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58719119229058960211223757 22019669710897110079208909)
          ·
            refine ⟨8257376141586416279703341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22019669710897110079208909 8257376141586416279703341)
            ·
              refine ⟨3096516053094906104888753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8257376141586416279703341 3096516053094906104888753)
              ·
                refine ⟨2322387039821179578666565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096516053094906104888753 2322387039821179578666565)
                ·
                  refine ⟨435447569966471170999981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322387039821179578666565 435447569966471170999981)
                  ·
                    rfl

theorem cell20_954035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_954035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954035 prefixEnd_954035 := by exact prefixLift 954035
  have htrace : WordTrace (prefixWord ++ tailWord_954035) baseStart_954035 baseEnd_954035 := by
    simpa [prefixWord, tailWord_954035, baseEnd_954035] using wordTrace_append hprefix tailTrace_954035
  have hstable : (prefixWord ++ tailWord_954035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954035).length < 2 ^ (prefixWord ++ tailWord_954035).sum := by decide
  have hdescent : baseEnd_954035 < baseStart_954035 := by decide
  rcases family_descends (prefixWord ++ tailWord_954035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954073 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_954073 : Nat := 118140960795 + 954073 * 2 ^ 59
def prefixEnd_954073 : Nat := 4983230072969 + 3 ^ 40 * 954073 * 2
def baseEnd_954073 : Nat := 435464914201911927733159

theorem tailTrace_954073 : CollatzResearch.WordTrace tailWord_954073 prefixEnd_954073 435464914201911927733159 := by
  unfold tailWord_954073
  simp only [CollatzResearch.WordTrace]
  refine ⟨34797901072563938540978873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23198600715042625693985915 34797901072563938540978873)
  ·
    refine ⟨26098425804422953905734155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34797901072563938540978873 26098425804422953905734155)
    ·
      refine ⟨39147638706634430858601233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26098425804422953905734155 39147638706634430858601233)
      ·
        refine ⟨29360729029975823143950925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39147638706634430858601233 29360729029975823143950925)
        ·
          refine ⟨11010273386240933678981597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29360729029975823143950925 11010273386240933678981597)
          ·
            refine ⟨4128852519840350129618099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11010273386240933678981597 4128852519840350129618099)
            ·
              refine ⟨6193278779760525194427149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128852519840350129618099 6193278779760525194427149)
              ·
                refine ⟨2322479542410196947910181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6193278779760525194427149 2322479542410196947910181)
                ·
                  refine ⟨435464914201911927733159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322479542410196947910181 435464914201911927733159)
                  ·
                    rfl

theorem cell20_954073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_954073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954073 prefixEnd_954073 := by exact prefixLift 954073
  have htrace : WordTrace (prefixWord ++ tailWord_954073) baseStart_954073 baseEnd_954073 := by
    simpa [prefixWord, tailWord_954073, baseEnd_954073] using wordTrace_append hprefix tailTrace_954073
  have hstable : (prefixWord ++ tailWord_954073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954073).length < 2 ^ (prefixWord ++ tailWord_954073).sum := by decide
  have hdescent : baseEnd_954073 < baseStart_954073 := by decide
  rcases family_descends (prefixWord ++ tailWord_954073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954097 : List Nat := [1, 2, 2, 2, 2, 3, 4, 4]
def baseStart_954097 : Nat := 118140960795 + 954097 * 2 ^ 59
def prefixEnd_954097 : Nat := 4983230072969 + 3 ^ 40 * 954097 * 2
def baseEnd_954097 : Nat := 145158622818624836977687

theorem tailTrace_954097 : CollatzResearch.WordTrace tailWord_954097 prefixEnd_954097 145158622818624836977687 := by
  unfold tailWord_954097
  simp only [CollatzResearch.WordTrace]
  refine ⟨34798776424476990639852545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23199184282984660426568363 34798776424476990639852545)
  ·
    refine ⟨26099082318357742979889409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34798776424476990639852545 26099082318357742979889409)
    ·
      refine ⟨19574311738768307234917057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26099082318357742979889409 19574311738768307234917057)
      ·
        refine ⟨14680733804076230426187793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19574311738768307234917057 14680733804076230426187793)
        ·
          refine ⟨11010550353057172819640845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14680733804076230426187793 11010550353057172819640845)
          ·
            refine ⟨4128956382396439807365317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11010550353057172819640845 4128956382396439807365317)
            ·
              refine ⟨774179321699332463880997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4128956382396439807365317 774179321699332463880997)
              ·
                refine ⟨145158622818624836977687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774179321699332463880997 145158622818624836977687)
                ·
                  rfl

theorem cell20_954097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_954097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954097 prefixEnd_954097 := by exact prefixLift 954097
  have htrace : WordTrace (prefixWord ++ tailWord_954097) baseStart_954097 baseEnd_954097 := by
    simpa [prefixWord, tailWord_954097, baseEnd_954097] using wordTrace_append hprefix tailTrace_954097
  have hstable : (prefixWord ++ tailWord_954097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954097).length < 2 ^ (prefixWord ++ tailWord_954097).sum := by decide
  have hdescent : baseEnd_954097 < baseStart_954097 := by decide
  rcases family_descends (prefixWord ++ tailWord_954097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954100 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_954100 : Nat := 118140960795 + 954100 * 2 ^ 59
def prefixEnd_954100 : Nat := 4983230072969 + 3 ^ 40 * 954100 * 2
def baseEnd_954100 : Nat := 435477237737619833833049

theorem tailTrace_954100 : CollatzResearch.WordTrace tailWord_954100 prefixEnd_954100 435477237737619833833049 := by
  unfold tailWord_954100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17399442921733061076105877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23199257228977414768141169 17399442921733061076105877)
  ·
    refine ⟨815598886956237237942463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17399442921733061076105877 815598886956237237942463)
    ·
      refine ⟨1223398330434355856913695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815598886956237237942463 1223398330434355856913695)
      ·
        refine ⟨1835097495651533785370543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223398330434355856913695 1835097495651533785370543)
        ·
          refine ⟨2752646243477300678055815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835097495651533785370543 2752646243477300678055815)
          ·
            refine ⟨4128969365215951017083723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752646243477300678055815 4128969365215951017083723)
            ·
              refine ⟨6193454047823926525625585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128969365215951017083723 6193454047823926525625585)
              ·
                refine ⟨4645090535867944894219189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6193454047823926525625585 4645090535867944894219189)
                ·
                  refine ⟨435477237737619833833049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4645090535867944894219189 435477237737619833833049)
                  ·
                    rfl

theorem cell20_954100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_954100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954100 prefixEnd_954100 := by exact prefixLift 954100
  have htrace : WordTrace (prefixWord ++ tailWord_954100) baseStart_954100 baseEnd_954100 := by
    simpa [prefixWord, tailWord_954100, baseEnd_954100] using wordTrace_append hprefix tailTrace_954100
  have hstable : (prefixWord ++ tailWord_954100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954100).length < 2 ^ (prefixWord ++ tailWord_954100).sum := by decide
  have hdescent : baseEnd_954100 < baseStart_954100 := by decide
  rcases family_descends (prefixWord ++ tailWord_954100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954135 : List Nat := [1, 1, 3, 4, 2, 2, 2, 5]
def baseStart_954135 : Nat := 118140960795 + 954135 * 2 ^ 59
def prefixEnd_954135 : Nat := 4983230072969 + 3 ^ 40 * 954135 * 2
def baseEnd_954135 : Nat := 145164404230438422555413

theorem tailTrace_954135 : CollatzResearch.WordTrace tailWord_954135 prefixEnd_954135 145164404230438422555413 := by
  unfold tailWord_954135
  simp only [CollatzResearch.WordTrace]
  refine ⟨34800162398339323129735859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23200108265559548753157239 34800162398339323129735859)
  ·
    refine ⟨52200243597508984694603789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34800162398339323129735859 52200243597508984694603789)
    ·
      refine ⟨19575091349065869260476421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52200243597508984694603789 19575091349065869260476421)
      ·
        refine ⟨3670329627949850486339329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19575091349065869260476421 3670329627949850486339329)
        ·
          refine ⟨2752747220962387864754497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3670329627949850486339329 2752747220962387864754497)
          ·
            refine ⟨2064560415721790898565873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2752747220962387864754497 2064560415721790898565873)
            ·
              refine ⟨1548420311791343173924405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064560415721790898565873 1548420311791343173924405)
              ·
                refine ⟨145164404230438422555413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1548420311791343173924405 145164404230438422555413)
                ·
                  rfl

theorem cell20_954135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_954135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954135 prefixEnd_954135 := by exact prefixLift 954135
  have htrace : WordTrace (prefixWord ++ tailWord_954135) baseStart_954135 baseEnd_954135 := by
    simpa [prefixWord, tailWord_954135, baseEnd_954135] using wordTrace_append hprefix tailTrace_954135
  have hstable : (prefixWord ++ tailWord_954135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954135).length < 2 ^ (prefixWord ++ tailWord_954135).sum := by decide
  have hdescent : baseEnd_954135 < baseStart_954135 := by decide
  rcases family_descends (prefixWord ++ tailWord_954135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954138 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_954138 : Nat := 118140960795 + 954138 * 2 ^ 59
def prefixEnd_954138 : Nat := 4983230072969 + 3 ^ 40 * 954138 * 2
def baseEnd_954138 : Nat := 435494581973060590566227

theorem tailTrace_954138 : CollatzResearch.WordTrace tailWord_954138 prefixEnd_954138 435494581973060590566227 := by
  unfold tailWord_954138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700067954332113660523767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23200181211552303094730045 8700067954332113660523767)
  ·
    refine ⟨13050101931498170490785651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8700067954332113660523767 13050101931498170490785651)
    ·
      refine ⟨19575152897247255736178477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13050101931498170490785651 19575152897247255736178477)
      ·
        refine ⟨7340682336467720901066929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19575152897247255736178477 7340682336467720901066929)
        ·
          refine ⟨5505511752350790675800197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7340682336467720901066929 5505511752350790675800197)
          ·
            refine ⟨1032283453565773251712537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5505511752350790675800197 1032283453565773251712537)
            ·
              refine ⟨774212590174329938784403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032283453565773251712537 774212590174329938784403)
              ·
                refine ⟨1161318885261494908176605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774212590174329938784403 1161318885261494908176605)
                ·
                  refine ⟨435494581973060590566227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161318885261494908176605 435494581973060590566227)
                  ·
                    rfl

theorem cell20_954138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_954138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954138 prefixEnd_954138 := by exact prefixLift 954138
  have htrace : WordTrace (prefixWord ++ tailWord_954138) baseStart_954138 baseEnd_954138 := by
    simpa [prefixWord, tailWord_954138, baseEnd_954138] using wordTrace_append hprefix tailTrace_954138
  have hstable : (prefixWord ++ tailWord_954138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954138).length < 2 ^ (prefixWord ++ tailWord_954138).sum := by decide
  have hdescent : baseEnd_954138 < baseStart_954138 := by decide
  rcases family_descends (prefixWord ++ tailWord_954138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954156 : List Nat := [2, 2, 1, 1, 1, 5, 2, 6]
def baseStart_954156 : Nat := 118140960795 + 954156 * 2 ^ 59
def prefixEnd_954156 : Nat := 4983230072969 + 3 ^ 40 * 954156 * 2
def baseEnd_954156 : Nat := 145167599221177509322051

theorem tailTrace_954156 : CollatzResearch.WordTrace tailWord_954156 prefixEnd_954156 145167599221177509322051 := by
  unfold tailWord_954156
  simp only [CollatzResearch.WordTrace]
  refine ⟨17400464165631621858125161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23200618887508829144166881 17400464165631621858125161)
  ·
    refine ⟨13050348124223716393593871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17400464165631621858125161 13050348124223716393593871)
    ·
      refine ⟨19575522186335574590390807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13050348124223716393593871 19575522186335574590390807)
      ·
        refine ⟨29363283279503361885586211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19575522186335574590390807 29363283279503361885586211)
        ·
          refine ⟨44044924919255042828379317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29363283279503361885586211 44044924919255042828379317)
          ·
            refine ⟨4129211711180160265160561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44044924919255042828379317 4129211711180160265160561)
            ·
              refine ⟨3096908783385120198870421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129211711180160265160561 3096908783385120198870421)
              ·
                refine ⟨145167599221177509322051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3096908783385120198870421 145167599221177509322051)
                ·
                  rfl

theorem cell20_954156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_954156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954156 prefixEnd_954156 := by exact prefixLift 954156
  have htrace : WordTrace (prefixWord ++ tailWord_954156) baseStart_954156 baseEnd_954156 := by
    simpa [prefixWord, tailWord_954156, baseEnd_954156] using wordTrace_append hprefix tailTrace_954156
  have hstable : (prefixWord ++ tailWord_954156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954156).length < 2 ^ (prefixWord ++ tailWord_954156).sum := by decide
  have hdescent : baseEnd_954156 < baseStart_954156 := by decide
  rcases family_descends (prefixWord ++ tailWord_954156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954183 : List Nat := [1, 1, 4, 1, 2, 1, 6, 2, 2]
def baseStart_954183 : Nat := 118140960795 + 954183 * 2 ^ 59
def prefixEnd_954183 : Nat := 4983230072969 + 3 ^ 40 * 954183 * 2
def baseEnd_954183 : Nat := 435515121199240434066043

theorem tailTrace_954183 : CollatzResearch.WordTrace tailWord_954183 prefixEnd_954183 435515121199240434066043 := by
  unfold tailWord_954183
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801913102165427327483203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23201275401443618218322135 34801913102165427327483203)
  ·
    refine ⟨52202869653248140991224805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34801913102165427327483203 52202869653248140991224805)
    ·
      refine ⟨9788038059984026435854651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52202869653248140991224805 9788038059984026435854651)
      ·
        refine ⟨14682057089976039653781977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788038059984026435854651 14682057089976039653781977)
        ·
          refine ⟨11011542817482029740336483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14682057089976039653781977 11011542817482029740336483)
          ·
            refine ⟨16517314226223044610504725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11011542817482029740336483 16517314226223044610504725)
            ·
              refine ⟨774249104354205216117409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16517314226223044610504725 774249104354205216117409)
              ·
                refine ⟨580686828265653912088057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774249104354205216117409 580686828265653912088057)
                ·
                  refine ⟨435515121199240434066043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580686828265653912088057 435515121199240434066043)
                  ·
                    rfl

theorem cell20_954183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 2].length) (baseStart_954183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954183 prefixEnd_954183 := by exact prefixLift 954183
  have htrace : WordTrace (prefixWord ++ tailWord_954183) baseStart_954183 baseEnd_954183 := by
    simpa [prefixWord, tailWord_954183, baseEnd_954183] using wordTrace_append hprefix tailTrace_954183
  have hstable : (prefixWord ++ tailWord_954183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954183).length < 2 ^ (prefixWord ++ tailWord_954183).sum := by decide
  have hdescent : baseEnd_954183 < baseStart_954183 := by decide
  rcases family_descends (prefixWord ++ tailWord_954183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954238 : List Nat := [4, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_954238 : Nat := 118140960795 + 954238 * 2 ^ 59
def prefixEnd_954238 : Nat := 4983230072969 + 3 ^ 40 * 954238 * 2
def baseEnd_954238 : Nat := 435540224697904687232485

theorem tailTrace_954238 : CollatzResearch.WordTrace tailWord_954238 prefixEnd_954238 435540224697904687232485 := by
  unfold tailWord_954238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350489889620771465091921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23202612744644114480490245 4350489889620771465091921)
  ·
    refine ⟨3262867417215578598818941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4350489889620771465091921 3262867417215578598818941)
    ·
      refine ⟨1223575281455841974557103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3262867417215578598818941 1223575281455841974557103)
      ·
        refine ⟨1835362922183762961835655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223575281455841974557103 1835362922183762961835655)
        ·
          refine ⟨2753044383275644442753483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835362922183762961835655 2753044383275644442753483)
          ·
            refine ⟨4129566574913466664130225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753044383275644442753483 4129566574913466664130225)
            ·
              refine ⟨3097174931185099998097669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129566574913466664130225 3097174931185099998097669)
              ·
                refine ⟨580720299597206249643313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3097174931185099998097669 580720299597206249643313)
                ·
                  refine ⟨435540224697904687232485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580720299597206249643313 435540224697904687232485)
                  ·
                    rfl

theorem cell20_954238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_954238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954238 prefixEnd_954238 := by exact prefixLift 954238
  have htrace : WordTrace (prefixWord ++ tailWord_954238) baseStart_954238 baseEnd_954238 := by
    simpa [prefixWord, tailWord_954238, baseEnd_954238] using wordTrace_append hprefix tailTrace_954238
  have hstable : (prefixWord ++ tailWord_954238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954238).length < 2 ^ (prefixWord ++ tailWord_954238).sum := by decide
  have hdescent : baseEnd_954238 < baseStart_954238 := by decide
  rcases family_descends (prefixWord ++ tailWord_954238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954263 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_954263 : Nat := 118140960795 + 954263 * 2 ^ 59
def prefixEnd_954263 : Nat := 4983230072969 + 3 ^ 40 * 954263 * 2
def baseEnd_954263 : Nat := 435551635379115711399049

theorem tailTrace_954263 : CollatzResearch.WordTrace tailWord_954263 prefixEnd_954263 435551635379115711399049 := by
  unfold tailWord_954263
  simp only [CollatzResearch.WordTrace]
  refine ⟨34804830941875600990395443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23203220627917067326930295 34804830941875600990395443)
  ·
    refine ⟨52207246412813401485593165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34804830941875600990395443 52207246412813401485593165)
    ·
      refine ⟨19577717404805025557097437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52207246412813401485593165 19577717404805025557097437)
      ·
        refine ⟨7341644026801884583911539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19577717404805025557097437 7341644026801884583911539)
        ·
          refine ⟨11012466040202826875867309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341644026801884583911539 11012466040202826875867309)
          ·
            refine ⟨4129674765076060078450241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11012466040202826875867309 4129674765076060078450241)
            ·
              refine ⟨3097256073807045058837681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129674765076060078450241 3097256073807045058837681)
              ·
                refine ⟨2322942055355283794128261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3097256073807045058837681 2322942055355283794128261)
                ·
                  refine ⟨435551635379115711399049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322942055355283794128261 435551635379115711399049)
                  ·
                    rfl

theorem cell20_954263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_954263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954263 prefixEnd_954263 := by exact prefixLift 954263
  have htrace : WordTrace (prefixWord ++ tailWord_954263) baseStart_954263 baseEnd_954263 := by
    simpa [prefixWord, tailWord_954263, baseEnd_954263] using wordTrace_append hprefix tailTrace_954263
  have hstable : (prefixWord ++ tailWord_954263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954263).length < 2 ^ (prefixWord ++ tailWord_954263).sum := by decide
  have hdescent : baseEnd_954263 < baseStart_954263 := by decide
  rcases family_descends (prefixWord ++ tailWord_954263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954266 : List Nat := [3, 1, 1, 4, 2, 3, 2, 4]
def baseStart_954266 : Nat := 118140960795 + 954266 * 2 ^ 59
def prefixEnd_954266 : Nat := 4983230072969 + 3 ^ 40 * 954266 * 2
def baseEnd_954266 : Nat := 145184334886953678099679

theorem tailTrace_954266 : CollatzResearch.WordTrace tailWord_954266 prefixEnd_954266 145184334886953678099679 := by
  unfold tailWord_954266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701235090216183125688663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23203293573909821668503101 8701235090216183125688663)
  ·
    refine ⟨13051852635324274688532995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8701235090216183125688663 13051852635324274688532995)
    ·
      refine ⟨19577778952986412032799493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13051852635324274688532995 19577778952986412032799493)
      ·
        refine ⟨3670833553684952256149905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19577778952986412032799493 3670833553684952256149905)
        ·
          refine ⟨2753125165263714192112429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3670833553684952256149905 2753125165263714192112429)
          ·
            refine ⟨1032421936973892822042161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2753125165263714192112429 1032421936973892822042161)
            ·
              refine ⟨774316452730419616531621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032421936973892822042161 774316452730419616531621)
              ·
                refine ⟨145184334886953678099679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774316452730419616531621 145184334886953678099679)
                ·
                  rfl

theorem cell20_954266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_954266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954266 prefixEnd_954266 := by exact prefixLift 954266
  have htrace : WordTrace (prefixWord ++ tailWord_954266) baseStart_954266 baseEnd_954266 := by
    simpa [prefixWord, tailWord_954266, baseEnd_954266] using wordTrace_append hprefix tailTrace_954266
  have hstable : (prefixWord ++ tailWord_954266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954266).length < 2 ^ (prefixWord ++ tailWord_954266).sum := by decide
  have hdescent : baseEnd_954266 < baseStart_954266 := by decide
  rcases family_descends (prefixWord ++ tailWord_954266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954297 : List Nat := [1, 2, 1, 4, 2, 1, 5, 2, 2]
def baseStart_954297 : Nat := 118140960795 + 954297 * 2 ^ 59
def prefixEnd_954297 : Nat := 4983230072969 + 3 ^ 40 * 954297 * 2
def baseEnd_954297 : Nat := 435567153905562704265577

theorem tailTrace_954297 : CollatzResearch.WordTrace tailWord_954297 prefixEnd_954297 435567153905562704265577 := by
  unfold tailWord_954297
  simp only [CollatzResearch.WordTrace]
  refine ⟨34806071023752424797133145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23204047349168283198088763 34806071023752424797133145)
  ·
    refine ⟨26104553267814318597849859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34806071023752424797133145 26104553267814318597849859)
    ·
      refine ⟨39156829901721477896774789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26104553267814318597849859 39156829901721477896774789)
      ·
        refine ⟨7341905606572777105645273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39156829901721477896774789 7341905606572777105645273)
        ·
          refine ⟨5506429204929582829233955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7341905606572777105645273 5506429204929582829233955)
          ·
            refine ⟨8259643807394374243850933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506429204929582829233955 8259643807394374243850933)
            ·
              refine ⟨774341606943222585361025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8259643807394374243850933 774341606943222585361025)
              ·
                refine ⟨580756205207416939020769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774341606943222585361025 580756205207416939020769)
                ·
                  refine ⟨435567153905562704265577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580756205207416939020769 435567153905562704265577)
                  ·
                    rfl

theorem cell20_954297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_954297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954297 prefixEnd_954297 := by exact prefixLift 954297
  have htrace : WordTrace (prefixWord ++ tailWord_954297) baseStart_954297 baseEnd_954297 := by
    simpa [prefixWord, tailWord_954297, baseEnd_954297] using wordTrace_append hprefix tailTrace_954297
  have hstable : (prefixWord ++ tailWord_954297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954297).length < 2 ^ (prefixWord ++ tailWord_954297).sum := by decide
  have hdescent : baseEnd_954297 < baseStart_954297 := by decide
  rcases family_descends (prefixWord ++ tailWord_954297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954394 : List Nat := [3, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_954394 : Nat := 118140960795 + 954394 * 2 ^ 59
def prefixEnd_954394 : Nat := 4983230072969 + 3 ^ 40 * 954394 * 2
def baseEnd_954394 : Nat := 435611427348661478031847

theorem tailTrace_954394 : CollatzResearch.WordTrace tailWord_954394 prefixEnd_954394 435611427348661478031847 := by
  unfold tailWord_954394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8702402226100252590853559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23206405936267340242276157 8702402226100252590853559)
  ·
    refine ⟨13053603339150378886280339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8702402226100252590853559 13053603339150378886280339)
    ·
      refine ⟨19580405008725568329420509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13053603339150378886280339 19580405008725568329420509)
      ·
        refine ⟨7342651878272088123532691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19580405008725568329420509 7342651878272088123532691)
        ·
          refine ⟨11013977817408132185299037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7342651878272088123532691 11013977817408132185299037)
          ·
            refine ⟨4130241681528049569487139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11013977817408132185299037 4130241681528049569487139)
            ·
              refine ⟨6195362522292074354230709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4130241681528049569487139 6195362522292074354230709)
              ·
                refine ⟨580815236464881970709129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6195362522292074354230709 580815236464881970709129)
                ·
                  refine ⟨435611427348661478031847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580815236464881970709129 435611427348661478031847)
                  ·
                    rfl

theorem cell20_954394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_954394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954394 prefixEnd_954394 := by exact prefixLift 954394
  have htrace : WordTrace (prefixWord ++ tailWord_954394) baseStart_954394 baseEnd_954394 := by
    simpa [prefixWord, tailWord_954394, baseEnd_954394] using wordTrace_append hprefix tailTrace_954394
  have hstable : (prefixWord ++ tailWord_954394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954394).length < 2 ^ (prefixWord ++ tailWord_954394).sum := by decide
  have hdescent : baseEnd_954394 < baseStart_954394 := by decide
  rcases family_descends (prefixWord ++ tailWord_954394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954404 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_954404 : Nat := 118140960795 + 954404 * 2 ^ 59
def prefixEnd_954404 : Nat := 4983230072969 + 3 ^ 40 * 954404 * 2
def baseEnd_954404 : Nat := 435615991621145887698473

theorem tailTrace_954404 : CollatzResearch.WordTrace tailWord_954404 prefixEnd_954404 435615991621145887698473 := by
  unfold tailWord_954404
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404986817182391035639133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23206649089576521380852177 17404986817182391035639133)
  ·
    refine ⟨6526870056443396638364675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17404986817182391035639133 6526870056443396638364675)
    ·
      refine ⟨9790305084665094957547013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6526870056443396638364675 9790305084665094957547013)
      ·
        refine ⟨1835682203374705304540065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9790305084665094957547013 1835682203374705304540065)
        ·
          refine ⟨1376761652531028978405049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835682203374705304540065 1376761652531028978405049)
          ·
            refine ⟨1032571239398271733803787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1376761652531028978405049 1032571239398271733803787)
            ·
              refine ⟨1548856859097407600705681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032571239398271733803787 1548856859097407600705681)
              ·
                refine ⟨1161642644323055700529261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548856859097407600705681 1161642644323055700529261)
                ·
                  refine ⟨435615991621145887698473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161642644323055700529261 435615991621145887698473)
                  ·
                    rfl

theorem cell20_954404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_954404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954404 prefixEnd_954404 := by exact prefixLift 954404
  have htrace : WordTrace (prefixWord ++ tailWord_954404) baseStart_954404 baseEnd_954404 := by
    simpa [prefixWord, tailWord_954404, baseEnd_954404] using wordTrace_append hprefix tailTrace_954404
  have hstable : (prefixWord ++ tailWord_954404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954404).length < 2 ^ (prefixWord ++ tailWord_954404).sum := by decide
  have hdescent : baseEnd_954404 < baseStart_954404 := by decide
  rcases family_descends (prefixWord ++ tailWord_954404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954443 : List Nat := [1, 1, 1, 1, 3, 1, 2, 10]
def baseStart_954443 : Nat := 118140960795 + 954443 * 2 ^ 59
def prefixEnd_954443 : Nat := 4983230072969 + 3 ^ 40 * 954443 * 2
def baseEnd_954443 : Nat := 145211264094611695132771

theorem tailTrace_954443 : CollatzResearch.WordTrace tailWord_954443 prefixEnd_954443 145211264094611695132771 := by
  unfold tailWord_954443
  simp only [CollatzResearch.WordTrace]
  refine ⟨34811396081223491731947983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23207597387482327821298655 34811396081223491731947983)
  ·
    refine ⟨52217094121835237597921975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34811396081223491731947983 52217094121835237597921975)
    ·
      refine ⟨78325641182752856396882963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52217094121835237597921975 78325641182752856396882963)
      ·
        refine ⟨117488461774129284595324445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78325641182752856396882963 117488461774129284595324445)
        ·
          refine ⟨44058173165298481723246667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117488461774129284595324445 44058173165298481723246667)
          ·
            refine ⟨66087259747947722584870001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44058173165298481723246667 66087259747947722584870001)
            ·
              refine ⟨49565444810960791938652501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66087259747947722584870001 49565444810960791938652501)
              ·
                refine ⟨145211264094611695132771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49565444810960791938652501 145211264094611695132771)
                ·
                  rfl

theorem cell20_954443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_954443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954443 prefixEnd_954443 := by exact prefixLift 954443
  have htrace : WordTrace (prefixWord ++ tailWord_954443) baseStart_954443 baseEnd_954443 := by
    simpa [prefixWord, tailWord_954443, baseEnd_954443] using wordTrace_append hprefix tailTrace_954443
  have hstable : (prefixWord ++ tailWord_954443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954443).length < 2 ^ (prefixWord ++ tailWord_954443).sum := by decide
  have hdescent : baseEnd_954443 < baseStart_954443 := by decide
  rcases family_descends (prefixWord ++ tailWord_954443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954460 : List Nat := [2, 2, 4, 1, 1, 2, 8]
def baseStart_954460 : Nat := 118140960795 + 954460 * 2 ^ 59
def prefixEnd_954460 : Nat := 4983230072969 + 3 ^ 40 * 954460 * 2
def baseEnd_954460 : Nat := 48404616838562064647953

theorem tailTrace_954460 : CollatzResearch.WordTrace tailWord_954460 prefixEnd_954460 48404616838562064647953 := by
  unfold tailWord_954460
  simp only [CollatzResearch.WordTrace]
  refine ⟨17406008061080951817658417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23208010748107935756877889 17406008061080951817658417)
  ·
    refine ⟨13054506045810713863243813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17406008061080951817658417 13054506045810713863243813)
    ·
      refine ⟨2447719883589508849358215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13054506045810713863243813 2447719883589508849358215)
      ·
        refine ⟨3671579825384263274037323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447719883589508849358215 3671579825384263274037323)
        ·
          refine ⟨5507369738076394911055985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3671579825384263274037323 5507369738076394911055985)
          ·
            refine ⟨4130527303557296183291989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5507369738076394911055985 4130527303557296183291989)
            ·
              refine ⟨48404616838562064647953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4130527303557296183291989 48404616838562064647953)
              ·
                rfl

theorem cell20_954460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 8].length) (baseStart_954460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954460 prefixEnd_954460 := by exact prefixLift 954460
  have htrace : WordTrace (prefixWord ++ tailWord_954460) baseStart_954460 baseEnd_954460 := by
    simpa [prefixWord, tailWord_954460, baseEnd_954460] using wordTrace_append hprefix tailTrace_954460
  have hstable : (prefixWord ++ tailWord_954460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954460).length < 2 ^ (prefixWord ++ tailWord_954460).sum := by decide
  have hdescent : baseEnd_954460 < baseStart_954460 := by decide
  rcases family_descends (prefixWord ++ tailWord_954460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954462 : List Nat := [4, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_954462 : Nat := 118140960795 + 954462 * 2 ^ 59
def prefixEnd_954462 : Nat := 4983230072969 + 3 ^ 40 * 954462 * 2
def baseEnd_954462 : Nat := 435642464401555463764903

theorem tailTrace_954462 : CollatzResearch.WordTrace tailWord_954462 prefixEnd_954462 435642464401555463764903 := by
  unfold tailWord_954462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4351511133519332247111205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23208059378769771984593093 4351511133519332247111205)
  ·
    refine ⟨815908337534874796333351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4351511133519332247111205 815908337534874796333351)
    ·
      refine ⟨1223862506302312194500027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815908337534874796333351 1223862506302312194500027)
      ·
        refine ⟨1835793759453468291750041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223862506302312194500027 1835793759453468291750041)
        ·
          refine ⟨1376845319590101218812531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835793759453468291750041 1376845319590101218812531)
          ·
            refine ⟨2065267979385151828218797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376845319590101218812531 2065267979385151828218797)
            ·
              refine ⟨774475492269431935582049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2065267979385151828218797 774475492269431935582049)
              ·
                refine ⟨580856619202073951686537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774475492269431935582049 580856619202073951686537)
                ·
                  refine ⟨435642464401555463764903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580856619202073951686537 435642464401555463764903)
                  ·
                    rfl

theorem cell20_954462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_954462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954462 prefixEnd_954462 := by exact prefixLift 954462
  have htrace : WordTrace (prefixWord ++ tailWord_954462) baseStart_954462 baseEnd_954462 := by
    simpa [prefixWord, tailWord_954462, baseEnd_954462] using wordTrace_append hprefix tailTrace_954462
  have hstable : (prefixWord ++ tailWord_954462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954462).length < 2 ^ (prefixWord ++ tailWord_954462).sum := by decide
  have hdescent : baseEnd_954462 < baseStart_954462 := by decide
  rcases family_descends (prefixWord ++ tailWord_954462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954466 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_954466 : Nat := 118140960795 + 954466 * 2 ^ 59
def prefixEnd_954466 : Nat := 4983230072969 + 3 ^ 40 * 954466 * 2
def baseEnd_954466 : Nat := 435644290110549227631553

theorem tailTrace_954466 : CollatzResearch.WordTrace tailWord_954466 prefixEnd_954466 435644290110549227631553 := by
  unfold tailWord_954466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8703058740035041665008813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23208156640093444440023501 8703058740035041665008813)
  ·
    refine ⟨3263647027513140624378305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8703058740035041665008813 3263647027513140624378305)
    ·
      refine ⟨2447735270634855468283729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3263647027513140624378305 2447735270634855468283729)
      ·
        refine ⟨1835801452976141601212797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2447735270634855468283729 1835801452976141601212797)
        ·
          refine ⟨688425544866053100454799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1835801452976141601212797 688425544866053100454799)
          ·
            refine ⟨1032638317299079650682199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688425544866053100454799 1032638317299079650682199)
            ·
              refine ⟨1548957475948619476023299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032638317299079650682199 1548957475948619476023299)
              ·
                refine ⟨2323436213922929214034949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548957475948619476023299 2323436213922929214034949)
                ·
                  refine ⟨435644290110549227631553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323436213922929214034949 435644290110549227631553)
                  ·
                    rfl

theorem cell20_954466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_954466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954466 prefixEnd_954466 := by exact prefixLift 954466
  have htrace : WordTrace (prefixWord ++ tailWord_954466) baseStart_954466 baseEnd_954466 := by
    simpa [prefixWord, tailWord_954466, baseEnd_954466] using wordTrace_append hprefix tailTrace_954466
  have hstable : (prefixWord ++ tailWord_954466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954466).length < 2 ^ (prefixWord ++ tailWord_954466).sum := by decide
  have hdescent : baseEnd_954466 < baseStart_954466 := by decide
  rcases family_descends (prefixWord ++ tailWord_954466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954467 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_954467 : Nat := 118140960795 + 954467 * 2 ^ 59
def prefixEnd_954467 : Nat := 4983230072969 + 3 ^ 40 * 954467 * 2
def baseEnd_954467 : Nat := 435644746537797668598215

theorem tailTrace_954467 : CollatzResearch.WordTrace tailWord_954467 prefixEnd_954467 435644746537797668598215 := by
  unfold tailWord_954467
  simp only [CollatzResearch.WordTrace]
  refine ⟨34812271433136543830821655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23208180955424362553881103 34812271433136543830821655)
  ·
    refine ⟨52218407149704815746232483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34812271433136543830821655 52218407149704815746232483)
    ·
      refine ⟨78327610724557223619348725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52218407149704815746232483 78327610724557223619348725)
      ·
        refine ⟨7343213505427239714313943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78327610724557223619348725 7343213505427239714313943)
        ·
          refine ⟨11014820258140859571470915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343213505427239714313943 11014820258140859571470915)
          ·
            refine ⟨16522230387211289357206373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11014820258140859571470915 16522230387211289357206373)
            ·
              refine ⟨3097918197602116754476195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16522230387211289357206373 3097918197602116754476195)
              ·
                refine ⟨4646877296403175131714293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097918197602116754476195 4646877296403175131714293)
                ·
                  refine ⟨435644746537797668598215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4646877296403175131714293 435644746537797668598215)
                  ·
                    rfl

theorem cell20_954467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_954467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954467 prefixEnd_954467 := by exact prefixLift 954467
  have htrace : WordTrace (prefixWord ++ tailWord_954467) baseStart_954467 baseEnd_954467 := by
    simpa [prefixWord, tailWord_954467, baseEnd_954467] using wordTrace_append hprefix tailTrace_954467
  have hstable : (prefixWord ++ tailWord_954467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954467).length < 2 ^ (prefixWord ++ tailWord_954467).sum := by decide
  have hdescent : baseEnd_954467 < baseStart_954467 := by decide
  rcases family_descends (prefixWord ++ tailWord_954467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954519 : List Nat := [1, 1, 3, 3, 12]
def baseStart_954519 : Nat := 118140960795 + 954519 * 2 ^ 59
def prefixEnd_954519 : Nat := 4983230072969 + 3 ^ 40 * 954519 * 2
def baseEnd_954519 : Nat := 5378623219194032084749

theorem tailTrace_954519 : CollatzResearch.WordTrace tailWord_954519 prefixEnd_954519 5378623219194032084749 := by
  unfold tailWord_954519
  simp only [CollatzResearch.WordTrace]
  refine ⟨34814168028948156711714611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23209445352632104474476407 34814168028948156711714611)
  ·
    refine ⟨52221252043422235067571917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34814168028948156711714611 52221252043422235067571917)
    ·
      refine ⟨19582969516283338150339469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52221252043422235067571917 19582969516283338150339469)
      ·
        refine ⟨7343613568606251806377301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19582969516283338150339469 7343613568606251806377301)
        ·
          refine ⟨5378623219194032084749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7343613568606251806377301 5378623219194032084749)
          ·
            rfl

theorem cell20_954519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 12].length) (baseStart_954519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954519 prefixEnd_954519 := by exact prefixLift 954519
  have htrace : WordTrace (prefixWord ++ tailWord_954519) baseStart_954519 baseEnd_954519 := by
    simpa [prefixWord, tailWord_954519, baseEnd_954519] using wordTrace_append hprefix tailTrace_954519
  have hstable : (prefixWord ++ tailWord_954519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954519).length < 2 ^ (prefixWord ++ tailWord_954519).sum := by decide
  have hdescent : baseEnd_954519 < baseStart_954519 := by decide
  rcases family_descends (prefixWord ++ tailWord_954519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954525 : List Nat := [1, 4, 2, 1, 1, 3, 4, 2, 2]
def baseStart_954525 : Nat := 118140960795 + 954525 * 2 ^ 59
def prefixEnd_954525 : Nat := 4983230072969 + 3 ^ 40 * 954525 * 2
def baseEnd_954525 : Nat := 435671219318207244664645

theorem tailTrace_954525 : CollatzResearch.WordTrace tailWord_954525 prefixEnd_954525 435671219318207244664645 := by
  unfold tailWord_954525
  simp only [CollatzResearch.WordTrace]
  refine ⟨34814386866926419736433029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23209591244617613157622019 34814386866926419736433029)
  ·
    refine ⟨6527697537548703700581193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34814386866926419736433029 6527697537548703700581193)
    ·
      refine ⟨4895773153161527775435895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6527697537548703700581193 4895773153161527775435895)
      ·
        refine ⟨7343659729742291663153843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895773153161527775435895 7343659729742291663153843)
        ·
          refine ⟨11015489594613437494730765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343659729742291663153843 11015489594613437494730765)
          ·
            refine ⟨4130808597980039060524037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11015489594613437494730765 4130808597980039060524037)
            ·
              refine ⟨774526612121257323848257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4130808597980039060524037 774526612121257323848257)
              ·
                refine ⟨580894959090942992886193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774526612121257323848257 580894959090942992886193)
                ·
                  refine ⟨435671219318207244664645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580894959090942992886193 435671219318207244664645)
                  ·
                    rfl

theorem cell20_954525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_954525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954525 prefixEnd_954525 := by exact prefixLift 954525
  have htrace : WordTrace (prefixWord ++ tailWord_954525) baseStart_954525 baseEnd_954525 := by
    simpa [prefixWord, tailWord_954525, baseEnd_954525] using wordTrace_append hprefix tailTrace_954525
  have hstable : (prefixWord ++ tailWord_954525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954525).length < 2 ^ (prefixWord ++ tailWord_954525).sum := by decide
  have hdescent : baseEnd_954525 < baseStart_954525 := by decide
  rcases family_descends (prefixWord ++ tailWord_954525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954532 : List Nat := [2, 3, 1, 2, 5, 1, 1, 5]
def baseStart_954532 : Nat := 118140960795 + 954532 * 2 ^ 59
def prefixEnd_954532 : Nat := 4983230072969 + 3 ^ 40 * 954532 * 2
def baseEnd_954532 : Nat := 145224804769648777143761

theorem tailTrace_954532 : CollatzResearch.WordTrace tailWord_954532 prefixEnd_954532 145224804769648777143761 := by
  unfold tailWord_954532
  simp only [CollatzResearch.WordTrace]
  refine ⟨17407321088950529965968925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23209761451934039954625233 17407321088950529965968925)
  ·
    refine ⟨6527745408356448737238347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17407321088950529965968925 6527745408356448737238347)
    ·
      refine ⟨9791618112534673105857521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6527745408356448737238347 9791618112534673105857521)
      ·
        refine ⟨7343713584401004829393141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9791618112534673105857521 7343713584401004829393141)
        ·
          refine ⟨688473148537594202755607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7343713584401004829393141 688473148537594202755607)
          ·
            refine ⟨1032709722806391304133411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688473148537594202755607 1032709722806391304133411)
            ·
              refine ⟨1549064584209586956200117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032709722806391304133411 1549064584209586956200117)
              ·
                refine ⟨145224804769648777143761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1549064584209586956200117 145224804769648777143761)
                ·
                  rfl

theorem cell20_954532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_954532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954532 prefixEnd_954532 := by exact prefixLift 954532
  have htrace : WordTrace (prefixWord ++ tailWord_954532) baseStart_954532 baseEnd_954532 := by
    simpa [prefixWord, tailWord_954532, baseEnd_954532] using wordTrace_append hprefix tailTrace_954532
  have hstable : (prefixWord ++ tailWord_954532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954532).length < 2 ^ (prefixWord ++ tailWord_954532).sum := by decide
  have hdescent : baseEnd_954532 < baseStart_954532 := by decide
  rcases family_descends (prefixWord ++ tailWord_954532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954574 : List Nat := [4, 1, 1, 1, 4, 2, 7]
def baseStart_954574 : Nat := 118140960795 + 954574 * 2 ^ 59
def prefixEnd_954574 : Nat := 4983230072969 + 3 ^ 40 * 954574 * 2
def baseEnd_954574 : Nat := 48410398250375650225679

theorem tailTrace_954574 : CollatzResearch.WordTrace tailWord_954574 prefixEnd_954574 48410398250375650225679 := by
  unfold tailWord_954574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352021755468612638120847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23210782695832600736644517 4352021755468612638120847)
  ·
    refine ⟨6528032633202918957181271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4352021755468612638120847 6528032633202918957181271)
    ·
      refine ⟨9792048949804378435771907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6528032633202918957181271 9792048949804378435771907)
      ·
        refine ⟨14688073424706567653657861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9792048949804378435771907 14688073424706567653657861)
        ·
          refine ⟨2754013767132481435060849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14688073424706567653657861 2754013767132481435060849)
          ·
            refine ⟨2065510325349361076295637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754013767132481435060849 2065510325349361076295637)
            ·
              refine ⟨48410398250375650225679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2065510325349361076295637 48410398250375650225679)
              ·
                rfl

theorem cell20_954574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 7].length) (baseStart_954574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954574 prefixEnd_954574 := by exact prefixLift 954574
  have htrace : WordTrace (prefixWord ++ tailWord_954574) baseStart_954574 baseEnd_954574 := by
    simpa [prefixWord, tailWord_954574, baseEnd_954574] using wordTrace_append hprefix tailTrace_954574
  have hstable : (prefixWord ++ tailWord_954574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954574).length < 2 ^ (prefixWord ++ tailWord_954574).sum := by decide
  have hdescent : baseEnd_954574 < baseStart_954574 := by decide
  rcases family_descends (prefixWord ++ tailWord_954574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954584 : List Nat := [2, 1, 2, 2, 4, 1, 2, 4, 2]
def baseStart_954584 : Nat := 118140960795 + 954584 * 2 ^ 59
def prefixEnd_954584 : Nat := 4983230072969 + 3 ^ 40 * 954584 * 2
def baseEnd_954584 : Nat := 435698148525865261697737

theorem tailTrace_954584 : CollatzResearch.WordTrace tailWord_954584 prefixEnd_954584 435698148525865261697737 := by
  unfold tailWord_954584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17408269386856336406415403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23211025849141781875220537 17408269386856336406415403)
  ·
    refine ⟨26112404080284504609623105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17408269386856336406415403 26112404080284504609623105)
    ·
      refine ⟨19584303060213378457217329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26112404080284504609623105 19584303060213378457217329)
      ·
        refine ⟨14688227295160033842912997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19584303060213378457217329 14688227295160033842912997)
        ·
          refine ⟨2754042617842506345546187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14688227295160033842912997 2754042617842506345546187)
          ·
            refine ⟨4131063926763759518319281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754042617842506345546187 4131063926763759518319281)
            ·
              refine ⟨3098297945072819638739461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131063926763759518319281 3098297945072819638739461)
              ·
                refine ⟨580930864701153682263649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3098297945072819638739461 580930864701153682263649)
                ·
                  refine ⟨435698148525865261697737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580930864701153682263649 435698148525865261697737)
                  ·
                    rfl

theorem cell20_954584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_954584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954584 prefixEnd_954584 := by exact prefixLift 954584
  have htrace : WordTrace (prefixWord ++ tailWord_954584) baseStart_954584 baseEnd_954584 := by
    simpa [prefixWord, tailWord_954584, baseEnd_954584] using wordTrace_append hprefix tailTrace_954584
  have hstable : (prefixWord ++ tailWord_954584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954584).length < 2 ^ (prefixWord ++ tailWord_954584).sum := by decide
  have hdescent : baseEnd_954584 < baseStart_954584 := by decide
  rcases family_descends (prefixWord ++ tailWord_954584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954633 : List Nat := [1, 2, 1, 1, 3, 4, 8]
def baseStart_954633 : Nat := 118140960795 + 954633 * 2 ^ 59
def prefixEnd_954633 : Nat := 4983230072969 + 3 ^ 40 * 954633 * 2
def baseEnd_954633 : Nat := 48413390384559874340467

theorem tailTrace_954633 : CollatzResearch.WordTrace tailWord_954633 prefixEnd_954633 48413390384559874340467 := by
  unfold tailWord_954633
  simp only [CollatzResearch.WordTrace]
  refine ⟨34818325950535154181364553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23212217300356769454243035 34818325950535154181364553)
  ·
    refine ⟨26113744462901365636023415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34818325950535154181364553 26113744462901365636023415)
    ·
      refine ⟨39170616694352048454035123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26113744462901365636023415 39170616694352048454035123)
      ·
        refine ⟨58755925041528072681052685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39170616694352048454035123 58755925041528072681052685)
        ·
          refine ⟨22033471890573027255394757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58755925041528072681052685 22033471890573027255394757)
          ·
            refine ⟨4131275979482442610386517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22033471890573027255394757 4131275979482442610386517)
            ·
              refine ⟨48413390384559874340467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4131275979482442610386517 48413390384559874340467)
              ·
                rfl

theorem cell20_954633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_954633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954633 prefixEnd_954633 := by exact prefixLift 954633
  have htrace : WordTrace (prefixWord ++ tailWord_954633) baseStart_954633 baseEnd_954633 := by
    simpa [prefixWord, tailWord_954633, baseEnd_954633] using wordTrace_append hprefix tailTrace_954633
  have hstable : (prefixWord ++ tailWord_954633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954633).length < 2 ^ (prefixWord ++ tailWord_954633).sum := by decide
  have hdescent : baseEnd_954633 < baseStart_954633 := by decide
  rcases family_descends (prefixWord ++ tailWord_954633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954643 : List Nat := [1, 1, 1, 2, 1, 3, 1, 8, 2]
def baseStart_954643 : Nat := 118140960795 + 954643 * 2 ^ 59
def prefixEnd_954643 : Nat := 4983230072969 + 3 ^ 40 * 954643 * 2
def baseEnd_954643 : Nat := 435725077733523278730829

theorem tailTrace_954643 : CollatzResearch.WordTrace tailWord_954643 prefixEnd_954643 435725077733523278730829 := by
  unfold tailWord_954643
  simp only [CollatzResearch.WordTrace]
  refine ⟨34818690680498925889228583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23212460453665950592819055 34818690680498925889228583)
  ·
    refine ⟨52228036020748388833842875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34818690680498925889228583 52228036020748388833842875)
    ·
      refine ⟨78342054031122583250764313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52228036020748388833842875 78342054031122583250764313)
      ·
        refine ⟨58756540523341937438073235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78342054031122583250764313 58756540523341937438073235)
        ·
          refine ⟨88134810785012906157109853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58756540523341937438073235 88134810785012906157109853)
          ·
            refine ⟨33050554044379839808916195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88134810785012906157109853 33050554044379839808916195)
            ·
              refine ⟨49575831066569759713374293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33050554044379839808916195 49575831066569759713374293)
              ·
                refine ⟨580966770311364371641105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 49575831066569759713374293 580966770311364371641105)
                ·
                  refine ⟨435725077733523278730829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580966770311364371641105 435725077733523278730829)
                  ·
                    rfl

theorem cell20_954643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 2].length) (baseStart_954643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954643 prefixEnd_954643 := by exact prefixLift 954643
  have htrace : WordTrace (prefixWord ++ tailWord_954643) baseStart_954643 baseEnd_954643 := by
    simpa [prefixWord, tailWord_954643, baseEnd_954643] using wordTrace_append hprefix tailTrace_954643
  have hstable : (prefixWord ++ tailWord_954643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954643).length < 2 ^ (prefixWord ++ tailWord_954643).sum := by decide
  have hdescent : baseEnd_954643 < baseStart_954643 := by decide
  rcases family_descends (prefixWord ++ tailWord_954643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954653 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 3]
def baseStart_954653 : Nat := 118140960795 + 954653 * 2 ^ 59
def prefixEnd_954653 : Nat := 4983230072969 + 3 ^ 40 * 954653 * 2
def baseEnd_954653 : Nat := 435729642006007688397455

theorem tailTrace_954653 : CollatzResearch.WordTrace tailWord_954653 prefixEnd_954653 435729642006007688397455 := by
  unfold tailWord_954653
  simp only [CollatzResearch.WordTrace]
  refine ⟨34819055410462697597092613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23212703606975131731395075 34819055410462697597092613)
  ·
    refine ⟨6528572889461755799454865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34819055410462697597092613 6528572889461755799454865)
    ·
      refine ⟨4896429667096316849591149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6528572889461755799454865 4896429667096316849591149)
      ·
        refine ⟨1836161125161118818596681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4896429667096316849591149 1836161125161118818596681)
        ·
          refine ⟨1377120843870839113947511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836161125161118818596681 1377120843870839113947511)
          ·
            refine ⟨2065681265806258670921267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377120843870839113947511 2065681265806258670921267)
            ·
              refine ⟨3098521898709388006381901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065681265806258670921267 3098521898709388006381901)
              ·
                refine ⟨1161945712016020502393213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3098521898709388006381901 1161945712016020502393213)
                ·
                  refine ⟨435729642006007688397455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161945712016020502393213 435729642006007688397455)
                  ·
                    rfl

theorem cell20_954653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_954653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954653 prefixEnd_954653 := by exact prefixLift 954653
  have htrace : WordTrace (prefixWord ++ tailWord_954653) baseStart_954653 baseEnd_954653 := by
    simpa [prefixWord, tailWord_954653, baseEnd_954653] using wordTrace_append hprefix tailTrace_954653
  have hstable : (prefixWord ++ tailWord_954653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954653).length < 2 ^ (prefixWord ++ tailWord_954653).sum := by decide
  have hdescent : baseEnd_954653 < baseStart_954653 := by decide
  rcases family_descends (prefixWord ++ tailWord_954653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954671 : List Nat := [1, 1, 2, 1, 2, 1, 6, 6]
def baseStart_954671 : Nat := 118140960795 + 954671 * 2 ^ 59
def prefixEnd_954671 : Nat := 4983230072969 + 3 ^ 40 * 954671 * 2
def baseEnd_954671 : Nat := 145245952565493208599127

theorem tailTrace_954671 : CollatzResearch.WordTrace tailWord_954671 prefixEnd_954671 145245952565493208599127 := by
  unfold tailWord_954671
  simp only [CollatzResearch.WordTrace]
  refine ⟨34819711924397486671247867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23213141282931657780831911 34819711924397486671247867)
  ·
    refine ⟨52229567886596230006871801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34819711924397486671247867 52229567886596230006871801)
    ·
      refine ⟨39172175914947172505153851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52229567886596230006871801 39172175914947172505153851)
      ·
        refine ⟨58758263872420758757730777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39172175914947172505153851 58758263872420758757730777)
        ·
          refine ⟨44068697904315569068298083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58758263872420758757730777 44068697904315569068298083)
          ·
            refine ⟨66103046856473353602447125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44068697904315569068298083 66103046856473353602447125)
            ·
              refine ⟨3098580321397188450114709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66103046856473353602447125 3098580321397188450114709)
              ·
                refine ⟨145245952565493208599127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3098580321397188450114709 145245952565493208599127)
                ·
                  rfl

theorem cell20_954671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_954671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954671 prefixEnd_954671 := by exact prefixLift 954671
  have htrace : WordTrace (prefixWord ++ tailWord_954671) baseStart_954671 baseEnd_954671 := by
    simpa [prefixWord, tailWord_954671, baseEnd_954671] using wordTrace_append hprefix tailTrace_954671
  have hstable : (prefixWord ++ tailWord_954671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954671).length < 2 ^ (prefixWord ++ tailWord_954671).sum := by decide
  have hdescent : baseEnd_954671 < baseStart_954671 := by decide
  rcases family_descends (prefixWord ++ tailWord_954671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954733 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_954733 : Nat := 118140960795 + 954733 * 2 ^ 59
def prefixEnd_954733 : Nat := 4983230072969 + 3 ^ 40 * 954733 * 2
def baseEnd_954733 : Nat := 435766156185882965730461

theorem tailTrace_954733 : CollatzResearch.WordTrace tailWord_954733 prefixEnd_954733 435766156185882965730461 := by
  unfold tailWord_954733
  simp only [CollatzResearch.WordTrace]
  refine ⟨34821973250172871260004853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23214648833448580840003235 34821973250172871260004853)
  ·
    refine ⟨3264559992203706680625455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34821973250172871260004853 3264559992203706680625455)
    ·
      refine ⟨4896839988305560020938183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3264559992203706680625455 4896839988305560020938183)
      ·
        refine ⟨7345259982458340031407275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896839988305560020938183 7345259982458340031407275)
        ·
          refine ⟨11017889973687510047110913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345259982458340031407275 11017889973687510047110913)
          ·
            refine ⟨8263417480265632535333185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11017889973687510047110913 8263417480265632535333185)
            ·
              refine ⟨6197563110199224401499889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8263417480265632535333185 6197563110199224401499889)
              ·
                refine ⟨4648172332649418301124917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6197563110199224401499889 4648172332649418301124917)
                ·
                  refine ⟨435766156185882965730461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648172332649418301124917 435766156185882965730461)
                  ·
                    rfl

theorem cell20_954733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_954733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954733 prefixEnd_954733 := by exact prefixLift 954733
  have htrace : WordTrace (prefixWord ++ tailWord_954733) baseStart_954733 baseEnd_954733 := by
    simpa [prefixWord, tailWord_954733, baseEnd_954733] using wordTrace_append hprefix tailTrace_954733
  have hstable : (prefixWord ++ tailWord_954733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954733).length < 2 ^ (prefixWord ++ tailWord_954733).sum := by decide
  have hdescent : baseEnd_954733 < baseStart_954733 := by decide
  rcases family_descends (prefixWord ++ tailWord_954733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954736 : List Nat := [2, 1, 1, 1, 4, 4, 2, 3, 2]
def baseStart_954736 : Nat := 118140960795 + 954736 * 2 ^ 59
def prefixEnd_954736 : Nat := 4983230072969 + 3 ^ 40 * 954736 * 2
def baseEnd_954736 : Nat := 435767525467628288630449

theorem tailTrace_954736 : CollatzResearch.WordTrace tailWord_954736 prefixEnd_954736 435767525467628288630449 := by
  unfold tailWord_954736
  simp only [CollatzResearch.WordTrace]
  refine ⟨17411041334581001386182031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23214721779441335181576041 17411041334581001386182031)
  ·
    refine ⟨26116562001871502079273047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17411041334581001386182031 26116562001871502079273047)
    ·
      refine ⟨39174843002807253118909571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26116562001871502079273047 39174843002807253118909571)
      ·
        refine ⟨58762264504210879678364357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39174843002807253118909571 58762264504210879678364357)
        ·
          refine ⟨11017924594539539939693317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58762264504210879678364357 11017924594539539939693317)
          ·
            refine ⟨2065860861476163738692497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11017924594539539939693317 2065860861476163738692497)
            ·
              refine ⟨1549395646107122804019373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065860861476163738692497 1549395646107122804019373)
              ·
                refine ⟨581023367290171051507265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549395646107122804019373 581023367290171051507265)
                ·
                  refine ⟨435767525467628288630449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581023367290171051507265 435767525467628288630449)
                  ·
                    rfl

theorem cell20_954736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_954736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954736 prefixEnd_954736 := by exact prefixLift 954736
  have htrace : WordTrace (prefixWord ++ tailWord_954736) baseStart_954736 baseEnd_954736 := by
    simpa [prefixWord, tailWord_954736, baseEnd_954736] using wordTrace_append hprefix tailTrace_954736
  have hstable : (prefixWord ++ tailWord_954736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954736).length < 2 ^ (prefixWord ++ tailWord_954736).sum := by decide
  have hdescent : baseEnd_954736 < baseStart_954736 := by decide
  rcases family_descends (prefixWord ++ tailWord_954736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954747 : List Nat := [1, 1, 1, 1, 1, 8, 7]
def baseStart_954747 : Nat := 118140960795 + 954747 * 2 ^ 59
def prefixEnd_954747 : Nat := 4983230072969 + 3 ^ 40 * 954747 * 2
def baseEnd_954747 : Nat := 48419171796373459918193

theorem tailTrace_954747 : CollatzResearch.WordTrace tailWord_954747 prefixEnd_954747 48419171796373459918193 := by
  unfold tailWord_954747
  simp only [CollatzResearch.WordTrace]
  refine ⟨34822483872122151651014495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23214989248081434434009663 34822483872122151651014495)
  ·
    refine ⟨52233725808183227476521743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34822483872122151651014495 52233725808183227476521743)
    ·
      refine ⟨78350588712274841214782615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52233725808183227476521743 78350588712274841214782615)
      ·
        refine ⟨117525883068412261822173923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78350588712274841214782615 117525883068412261822173923)
        ·
          refine ⟨176288824602618392733260885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117525883068412261822173923 176288824602618392733260885)
          ·
            refine ⟨2065884663311934289842901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 176288824602618392733260885 2065884663311934289842901)
            ·
              refine ⟨48419171796373459918193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2065884663311934289842901 48419171796373459918193)
              ·
                rfl

theorem cell20_954747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_954747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954747 prefixEnd_954747 := by exact prefixLift 954747
  have htrace : WordTrace (prefixWord ++ tailWord_954747) baseStart_954747 baseEnd_954747 := by
    simpa [prefixWord, tailWord_954747, baseEnd_954747] using wordTrace_append hprefix tailTrace_954747
  have hstable : (prefixWord ++ tailWord_954747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954747).length < 2 ^ (prefixWord ++ tailWord_954747).sum := by decide
  have hdescent : baseEnd_954747 < baseStart_954747 := by decide
  rcases family_descends (prefixWord ++ tailWord_954747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954791 : List Nat := [1, 1, 6, 1, 1, 4, 1, 3, 2]
def baseStart_954791 : Nat := 118140960795 + 954791 * 2 ^ 59
def prefixEnd_954791 : Nat := 4983230072969 + 3 ^ 40 * 954791 * 2
def baseEnd_954791 : Nat := 435792628966292541796891

theorem tailTrace_954791 : CollatzResearch.WordTrace tailWord_954791 prefixEnd_954791 435792628966292541796891 := by
  unfold tailWord_954791
  simp only [CollatzResearch.WordTrace]
  refine ⟨34824088683962747165616227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23216059122641831443744151 34824088683962747165616227)
  ·
    refine ⟨52236133025944120748424341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34824088683962747165616227 52236133025944120748424341)
    ·
      refine ⟨2448568735591130660082391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52236133025944120748424341 2448568735591130660082391)
      ·
        refine ⟨3672853103386695990123587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448568735591130660082391 3672853103386695990123587)
        ·
          refine ⟨5509279655080043985185381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672853103386695990123587 5509279655080043985185381)
          ·
            refine ⟨1032989935327508247222259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5509279655080043985185381 1032989935327508247222259)
            ·
              refine ⟨1549484902991262370833389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032989935327508247222259 1549484902991262370833389)
              ·
                refine ⟨581056838621723389062521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549484902991262370833389 581056838621723389062521)
                ·
                  refine ⟨435792628966292541796891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581056838621723389062521 435792628966292541796891)
                  ·
                    rfl

theorem cell20_954791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 2].length) (baseStart_954791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954791 prefixEnd_954791 := by exact prefixLift 954791
  have htrace : WordTrace (prefixWord ++ tailWord_954791) baseStart_954791 baseEnd_954791 := by
    simpa [prefixWord, tailWord_954791, baseEnd_954791] using wordTrace_append hprefix tailTrace_954791
  have hstable : (prefixWord ++ tailWord_954791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954791).length < 2 ^ (prefixWord ++ tailWord_954791).sum := by decide
  have hdescent : baseEnd_954791 < baseStart_954791 := by decide
  rcases family_descends (prefixWord ++ tailWord_954791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954809 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_954809 : Nat := 118140960795 + 954809 * 2 ^ 59
def prefixEnd_954809 : Nat := 4983230072969 + 3 ^ 40 * 954809 * 2
def baseEnd_954809 : Nat := 435800844656764479196817

theorem tailTrace_954809 : CollatzResearch.WordTrace tailWord_954809 prefixEnd_954809 435800844656764479196817 := by
  unfold tailWord_954809
  simp only [CollatzResearch.WordTrace]
  refine ⟨34824745197897536239771481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23216496798598357493180987 34824745197897536239771481)
  ·
    refine ⟨26118558898423152179828611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34824745197897536239771481 26118558898423152179828611)
    ·
      refine ⟨39177838347634728269742917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26118558898423152179828611 39177838347634728269742917)
      ·
        refine ⟨7345844690181511550576797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39177838347634728269742917 7345844690181511550576797)
        ·
          refine ⟨2754691758818066831466299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7345844690181511550576797 2754691758818066831466299)
          ·
            refine ⟨4132037638227100247199449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754691758818066831466299 4132037638227100247199449)
            ·
              refine ⟨3099028228670325185399587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132037638227100247199449 3099028228670325185399587)
              ·
                refine ⟨4648542343005487778099381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099028228670325185399587 4648542343005487778099381)
                ·
                  refine ⟨435800844656764479196817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648542343005487778099381 435800844656764479196817)
                  ·
                    rfl

theorem cell20_954809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_954809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954809 prefixEnd_954809 := by exact prefixLift 954809
  have htrace : WordTrace (prefixWord ++ tailWord_954809) baseStart_954809 baseEnd_954809 := by
    simpa [prefixWord, tailWord_954809, baseEnd_954809] using wordTrace_append hprefix tailTrace_954809
  have hstable : (prefixWord ++ tailWord_954809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954809).length < 2 ^ (prefixWord ++ tailWord_954809).sum := by decide
  have hdescent : baseEnd_954809 < baseStart_954809 := by decide
  rcases family_descends (prefixWord ++ tailWord_954809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954812 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_954812 : Nat := 118140960795 + 954812 * 2 ^ 59
def prefixEnd_954812 : Nat := 4983230072969 + 3 ^ 40 * 954812 * 2
def baseEnd_954812 : Nat := 435802213938509802096805

theorem tailTrace_954812 : CollatzResearch.WordTrace tailWord_954812 prefixEnd_954812 435802213938509802096805 := by
  unfold tailWord_954812
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412427308443333876065345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23216569744591111834753793 17412427308443333876065345)
  ·
    refine ⟨13059320481332500407049009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17412427308443333876065345 13059320481332500407049009)
    ·
      refine ⟨9794490360999375305286757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13059320481332500407049009 9794490360999375305286757)
      ·
        refine ⟨1836466942687382869741267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9794490360999375305286757 1836466942687382869741267)
        ·
          refine ⟨2754700414031074304611901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836466942687382869741267 2754700414031074304611901)
          ·
            refine ⟨1033012655261652864229463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2754700414031074304611901 1033012655261652864229463)
            ·
              refine ⟨1549518982892479296344195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033012655261652864229463 1549518982892479296344195)
              ·
                refine ⟨2324278474338718944516293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549518982892479296344195 2324278474338718944516293)
                ·
                  refine ⟨435802213938509802096805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324278474338718944516293 435802213938509802096805)
                  ·
                    rfl

theorem cell20_954812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_954812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954812 prefixEnd_954812 := by exact prefixLift 954812
  have htrace : WordTrace (prefixWord ++ tailWord_954812) baseStart_954812 baseEnd_954812 := by
    simpa [prefixWord, tailWord_954812, baseEnd_954812] using wordTrace_append hprefix tailTrace_954812
  have hstable : (prefixWord ++ tailWord_954812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954812).length < 2 ^ (prefixWord ++ tailWord_954812).sum := by decide
  have hdescent : baseEnd_954812 < baseStart_954812 := by decide
  rcases family_descends (prefixWord ++ tailWord_954812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954823 : List Nat := [1, 1, 4, 1, 1, 4, 1, 7]
def baseStart_954823 : Nat := 118140960795 + 954823 * 2 ^ 59
def prefixEnd_954823 : Nat := 4983230072969 + 3 ^ 40 * 954823 * 2
def baseEnd_954823 : Nat := 145269078212747550910031

theorem tailTrace_954823 : CollatzResearch.WordTrace tailWord_954823 prefixEnd_954823 145269078212747550910031 := by
  unfold tailWord_954823
  simp only [CollatzResearch.WordTrace]
  refine ⟨34825255819846816630781123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23216837213231211087187415 34825255819846816630781123)
  ·
    refine ⟨52237883729770224946171685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34825255819846816630781123 52237883729770224946171685)
    ·
      refine ⟨9794603199331917177407191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52237883729770224946171685 9794603199331917177407191)
      ·
        refine ⟨14691904798997875766110787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794603199331917177407191 14691904798997875766110787)
        ·
          refine ⟨22037857198496813649166181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14691904798997875766110787 22037857198496813649166181)
          ·
            refine ⟨4132098224718152559218659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22037857198496813649166181 4132098224718152559218659)
            ·
              refine ⟨6198147337077228838827989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4132098224718152559218659 6198147337077228838827989)
              ·
                refine ⟨145269078212747550910031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6198147337077228838827989 145269078212747550910031)
                ·
                  rfl

theorem cell20_954823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_954823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954823 prefixEnd_954823 := by exact prefixLift 954823
  have htrace : WordTrace (prefixWord ++ tailWord_954823) baseStart_954823 baseEnd_954823 := by
    simpa [prefixWord, tailWord_954823, baseEnd_954823] using wordTrace_append hprefix tailTrace_954823
  have hstable : (prefixWord ++ tailWord_954823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954823).length < 2 ^ (prefixWord ++ tailWord_954823).sum := by decide
  have hdescent : baseEnd_954823 < baseStart_954823 := by decide
  rcases family_descends (prefixWord ++ tailWord_954823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954885 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 3]
def baseStart_954885 : Nat := 118140960795 + 954885 * 2 ^ 59
def prefixEnd_954885 : Nat := 4983230072969 + 3 ^ 40 * 954885 * 2
def baseEnd_954885 : Nat := 435835533127645992663173

theorem tailTrace_954885 : CollatzResearch.WordTrace tailWord_954885 prefixEnd_954885 435835533127645992663173 := by
  unfold tailWord_954885
  simp only [CollatzResearch.WordTrace]
  refine ⟨34827517145622201219538109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23218344763748134146358739 34827517145622201219538109)
  ·
    refine ⟨13060318929608325457326791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34827517145622201219538109 13060318929608325457326791)
    ·
      refine ⟨19590478394412488185990187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13060318929608325457326791 19590478394412488185990187)
      ·
        refine ⟨29385717591618732278985281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19590478394412488185990187 29385717591618732278985281)
        ·
          refine ⟨22039288193714049209238961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29385717591618732278985281 22039288193714049209238961)
          ·
            refine ⟨16529466145285536906929221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22039288193714049209238961 16529466145285536906929221)
            ·
              refine ⟨3099274902241038170049229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16529466145285536906929221 3099274902241038170049229)
              ·
                refine ⟨1162228088340389313768461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3099274902241038170049229 1162228088340389313768461)
                ·
                  refine ⟨435835533127645992663173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162228088340389313768461 435835533127645992663173)
                  ·
                    rfl

theorem cell20_954885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_954885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954885 prefixEnd_954885 := by exact prefixLift 954885
  have htrace : WordTrace (prefixWord ++ tailWord_954885) baseStart_954885 baseEnd_954885 := by
    simpa [prefixWord, tailWord_954885, baseEnd_954885] using wordTrace_append hprefix tailTrace_954885
  have hstable : (prefixWord ++ tailWord_954885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954885).length < 2 ^ (prefixWord ++ tailWord_954885).sum := by decide
  have hdescent : baseEnd_954885 < baseStart_954885 := by decide
  rcases family_descends (prefixWord ++ tailWord_954885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954892 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_954892 : Nat := 118140960795 + 954892 * 2 ^ 59
def prefixEnd_954892 : Nat := 4983230072969 + 3 ^ 40 * 954892 * 2
def baseEnd_954892 : Nat := 435838728118385079429811

theorem tailTrace_954892 : CollatzResearch.WordTrace tailWord_954892 prefixEnd_954892 435838728118385079429811 := by
  unfold tailWord_954892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17413886228298420707521465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23218514971064560943361953 17413886228298420707521465)
  ·
    refine ⟨13060414671223815530641099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17413886228298420707521465 13060414671223815530641099)
    ·
      refine ⟨19590622006835723295961649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13060414671223815530641099 19590622006835723295961649)
      ·
        refine ⟨14692966505126792471971237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19590622006835723295961649 14692966505126792471971237)
        ·
          refine ⟨2754931219711273588494607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14692966505126792471971237 2754931219711273588494607)
          ·
            refine ⟨4132396829566910382741911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754931219711273588494607 4132396829566910382741911)
            ·
              refine ⟨6198595244350365574112867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4132396829566910382741911 6198595244350365574112867)
              ·
                refine ⟨9297892866525548361169301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6198595244350365574112867 9297892866525548361169301)
                ·
                  refine ⟨435838728118385079429811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9297892866525548361169301 435838728118385079429811)
                  ·
                    rfl

theorem cell20_954892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_954892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954892 prefixEnd_954892 := by exact prefixLift 954892
  have htrace : WordTrace (prefixWord ++ tailWord_954892) baseStart_954892 baseEnd_954892 := by
    simpa [prefixWord, tailWord_954892, baseEnd_954892] using wordTrace_append hprefix tailTrace_954892
  have hstable : (prefixWord ++ tailWord_954892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954892).length < 2 ^ (prefixWord ++ tailWord_954892).sum := by decide
  have hdescent : baseEnd_954892 < baseStart_954892 := by decide
  rcases family_descends (prefixWord ++ tailWord_954892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954919 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 5]
def baseStart_954919 : Nat := 118140960795 + 954919 * 2 ^ 59
def prefixEnd_954919 : Nat := 4983230072969 + 3 ^ 40 * 954919 * 2
def baseEnd_954919 : Nat := 435851051654092985529701

theorem tailTrace_954919 : CollatzResearch.WordTrace tailWord_954919 prefixEnd_954919 435851051654092985529701 := by
  unfold tailWord_954919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34828757227499025026275811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23219171484999350017517207 34828757227499025026275811)
  ·
    refine ⟨52243135841248537539413717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34828757227499025026275811 52243135841248537539413717)
    ·
      refine ⟨1224448496279262598580009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 52243135841248537539413717 1224448496279262598580009)
      ·
        refine ⟨918336372209446948935007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1224448496279262598580009 918336372209446948935007)
        ·
          refine ⟨1377504558314170423402511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918336372209446948935007 1377504558314170423402511)
          ·
            refine ⟨2066256837471255635103767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377504558314170423402511 2066256837471255635103767)
            ·
              refine ⟨3099385256206883452655651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066256837471255635103767 3099385256206883452655651)
              ·
                refine ⟨4649077884310325178983477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099385256206883452655651 4649077884310325178983477)
                ·
                  refine ⟨435851051654092985529701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4649077884310325178983477 435851051654092985529701)
                  ·
                    rfl

theorem cell20_954919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_954919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954919 prefixEnd_954919 := by exact prefixLift 954919
  have htrace : WordTrace (prefixWord ++ tailWord_954919) baseStart_954919 baseEnd_954919 := by
    simpa [prefixWord, tailWord_954919, baseEnd_954919] using wordTrace_append hprefix tailTrace_954919
  have hstable : (prefixWord ++ tailWord_954919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954919).length < 2 ^ (prefixWord ++ tailWord_954919).sum := by decide
  have hdescent : baseEnd_954919 < baseStart_954919 := by decide
  rcases family_descends (prefixWord ++ tailWord_954919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954926 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_954926 : Nat := 118140960795 + 954926 * 2 ^ 59
def prefixEnd_954926 : Nat := 4983230072969 + 3 ^ 40 * 954926 * 2
def baseEnd_954926 : Nat := 435854246644832072296339

theorem tailTrace_954926 : CollatzResearch.WordTrace tailWord_954926 prefixEnd_954926 435854246644832072296339 := by
  unfold tailWord_954926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353626567309208152722579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23219341692315776814520421 4353626567309208152722579)
  ·
    refine ⟨6530439850963812229083869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4353626567309208152722579 6530439850963812229083869)
    ·
      refine ⟨2448914944111429585906451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6530439850963812229083869 2448914944111429585906451)
      ·
        refine ⟨3673372416167144378859677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448914944111429585906451 3673372416167144378859677)
        ·
          refine ⟨1377514656062679142072379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3673372416167144378859677 1377514656062679142072379)
          ·
            refine ⟨2066271984094018713108569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377514656062679142072379 2066271984094018713108569)
            ·
              refine ⟨1549703988070514034831427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066271984094018713108569 1549703988070514034831427)
              ·
                refine ⟨2324555982105771052247141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549703988070514034831427 2324555982105771052247141)
                ·
                  refine ⟨435854246644832072296339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324555982105771052247141 435854246644832072296339)
                  ·
                    rfl

theorem cell20_954926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_954926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954926 prefixEnd_954926 := by exact prefixLift 954926
  have htrace : WordTrace (prefixWord ++ tailWord_954926) baseStart_954926 baseEnd_954926 := by
    simpa [prefixWord, tailWord_954926, baseEnd_954926] using wordTrace_append hprefix tailTrace_954926
  have hstable : (prefixWord ++ tailWord_954926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954926).length < 2 ^ (prefixWord ++ tailWord_954926).sum := by decide
  have hdescent : baseEnd_954926 < baseStart_954926 := by decide
  rcases family_descends (prefixWord ++ tailWord_954926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954930 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_954930 : Nat := 118140960795 + 954930 * 2 ^ 59
def prefixEnd_954930 : Nat := 4983230072969 + 3 ^ 40 * 954930 * 2
def baseEnd_954930 : Nat := 435856072353825836162989

theorem tailTrace_954930 : CollatzResearch.WordTrace tailWord_954930 prefixEnd_954930 435856072353825836162989 := by
  unfold tailWord_954930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707289607614793476231561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23219438953639449269950829 8707289607614793476231561)
  ·
    refine ⟨6530467205711095107173671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8707289607614793476231561 6530467205711095107173671)
    ·
      refine ⟨9795700808566642660760507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6530467205711095107173671 9795700808566642660760507)
      ·
        refine ⟨14693551212849963991140761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9795700808566642660760507 14693551212849963991140761)
        ·
          refine ⟨11020163409637472993355571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14693551212849963991140761 11020163409637472993355571)
          ·
            refine ⟨16530245114456209490033357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11020163409637472993355571 16530245114456209490033357)
            ·
              refine ⟨6198841917921078558762509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16530245114456209490033357 6198841917921078558762509)
              ·
                refine ⟨2324565719220404459535941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6198841917921078558762509 2324565719220404459535941)
                ·
                  refine ⟨435856072353825836162989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324565719220404459535941 435856072353825836162989)
                  ·
                    rfl

theorem cell20_954930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_954930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954930 prefixEnd_954930 := by exact prefixLift 954930
  have htrace : WordTrace (prefixWord ++ tailWord_954930) baseStart_954930 baseEnd_954930 := by
    simpa [prefixWord, tailWord_954930, baseEnd_954930] using wordTrace_append hprefix tailTrace_954930
  have hstable : (prefixWord ++ tailWord_954930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954930).length < 2 ^ (prefixWord ++ tailWord_954930).sum := by decide
  have hdescent : baseEnd_954930 < baseStart_954930 := by decide
  rcases family_descends (prefixWord ++ tailWord_954930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954937 : List Nat := [1, 2, 1, 5, 1, 1, 2, 7]
def baseStart_954937 : Nat := 118140960795 + 954937 * 2 ^ 59
def prefixEnd_954937 : Nat := 4983230072969 + 3 ^ 40 * 954937 * 2
def baseEnd_954937 : Nat := 145286422448188307643209

theorem tailTrace_954937 : CollatzResearch.WordTrace tailWord_954937 prefixEnd_954937 145286422448188307643209 := by
  unfold tailWord_954937
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829413741433814100431065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23219609160955876066954043 34829413741433814100431065)
  ·
    refine ⟨26122060306075360575323299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34829413741433814100431065 26122060306075360575323299)
    ·
      refine ⟨39183090459113040862984949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26122060306075360575323299 39183090459113040862984949)
      ·
        refine ⟨3673414730541847580904839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39183090459113040862984949 3673414730541847580904839)
        ·
          refine ⟨5510122095812771371357259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673414730541847580904839 5510122095812771371357259)
          ·
            refine ⟨8265183143719157057035889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510122095812771371357259 8265183143719157057035889)
            ·
              refine ⟨6198887357789367792776917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8265183143719157057035889 6198887357789367792776917)
              ·
                refine ⟨145286422448188307643209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6198887357789367792776917 145286422448188307643209)
                ·
                  rfl

theorem cell20_954937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_954937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954937 prefixEnd_954937 := by exact prefixLift 954937
  have htrace : WordTrace (prefixWord ++ tailWord_954937) baseStart_954937 baseEnd_954937 := by
    simpa [prefixWord, tailWord_954937, baseEnd_954937] using wordTrace_append hprefix tailTrace_954937
  have hstable : (prefixWord ++ tailWord_954937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954937).length < 2 ^ (prefixWord ++ tailWord_954937).sum := by decide
  have hdescent : baseEnd_954937 < baseStart_954937 := by decide
  rcases family_descends (prefixWord ++ tailWord_954937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954950 : List Nat := [6, 1, 1, 1, 2, 1, 4, 4]
def baseStart_954950 : Nat := 118140960795 + 954950 * 2 ^ 59
def prefixEnd_954950 : Nat := 4983230072969 + 3 ^ 40 * 954950 * 2
def baseEnd_954950 : Nat := 145288400299598218498747

theorem tailTrace_954950 : CollatzResearch.WordTrace tailWord_954950 prefixEnd_954950 145288400299598218498747 := by
  unfold tailWord_954950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088433996574584916270447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23219925260257811547102869 1088433996574584916270447)
  ·
    refine ⟨1632650994861877374405671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1088433996574584916270447 1632650994861877374405671)
    ·
      refine ⟨2448976492292816061608507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632650994861877374405671 2448976492292816061608507)
      ·
        refine ⟨3673464738439224092412761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448976492292816061608507 3673464738439224092412761)
        ·
          refine ⟨2755098553829418069309571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3673464738439224092412761 2755098553829418069309571)
          ·
            refine ⟨4132647830744127103964357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755098553829418069309571 4132647830744127103964357)
            ·
              refine ⟨774871468264523831993317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4132647830744127103964357 774871468264523831993317)
              ·
                refine ⟨145288400299598218498747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774871468264523831993317 145288400299598218498747)
                ·
                  rfl

theorem cell20_954950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_954950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954950 prefixEnd_954950 := by exact prefixLift 954950
  have htrace : WordTrace (prefixWord ++ tailWord_954950) baseStart_954950 baseEnd_954950 := by
    simpa [prefixWord, tailWord_954950, baseEnd_954950] using wordTrace_append hprefix tailTrace_954950
  have hstable : (prefixWord ++ tailWord_954950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954950).length < 2 ^ (prefixWord ++ tailWord_954950).sum := by decide
  have hdescent : baseEnd_954950 < baseStart_954950 := by decide
  rcases family_descends (prefixWord ++ tailWord_954950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954954 : List Nat := [3, 1, 2, 1, 1, 4, 4, 4]
def baseStart_954954 : Nat := 118140960795 + 954954 * 2 ^ 59
def prefixEnd_954954 : Nat := 4983230072969 + 3 ^ 40 * 954954 * 2
def baseEnd_954954 : Nat := 145289008869262806454297

theorem tailTrace_954954 : CollatzResearch.WordTrace tailWord_954954 prefixEnd_954954 145289008869262806454297 := by
  unfold tailWord_954954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707508445593056500949979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23220022521581484002533277 8707508445593056500949979)
  ·
    refine ⟨13061262668389584751424969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8707508445593056500949979 13061262668389584751424969)
    ·
      refine ⟨9795947001292188563568727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13061262668389584751424969 9795947001292188563568727)
      ·
        refine ⟨14693920501938282845353091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9795947001292188563568727 14693920501938282845353091)
        ·
          refine ⟨22040880752907424268029637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14693920501938282845353091 22040880752907424268029637)
          ·
            refine ⟨4132665141170142050255557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22040880752907424268029637 4132665141170142050255557)
            ·
              refine ⟨774874713969401634422917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4132665141170142050255557 774874713969401634422917)
              ·
                refine ⟨145289008869262806454297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774874713969401634422917 145289008869262806454297)
                ·
                  rfl

theorem cell20_954954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_954954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954954 prefixEnd_954954 := by exact prefixLift 954954
  have htrace : WordTrace (prefixWord ++ tailWord_954954) baseStart_954954 baseEnd_954954 := by
    simpa [prefixWord, tailWord_954954, baseEnd_954954] using wordTrace_append hprefix tailTrace_954954
  have hstable : (prefixWord ++ tailWord_954954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954954).length < 2 ^ (prefixWord ++ tailWord_954954).sum := by decide
  have hdescent : baseEnd_954954 < baseStart_954954 := by decide
  rcases family_descends (prefixWord ++ tailWord_954954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954964 : List Nat := [2, 4, 1, 1, 1, 3, 3, 3, 2]
def baseStart_954964 : Nat := 118140960795 + 954964 * 2 ^ 59
def prefixEnd_954964 : Nat := 4983230072969 + 3 ^ 40 * 954964 * 2
def baseEnd_954964 : Nat := 435871590880272829029517

theorem tailTrace_954964 : CollatzResearch.WordTrace tailWord_954964 prefixEnd_954964 435871590880272829029517 := by
  unfold tailWord_954964
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415199256167998855831973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23220265674890665141109297 17415199256167998855831973)
  ·
    refine ⟨3265349860531499785468495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17415199256167998855831973 3265349860531499785468495)
    ·
      refine ⟨4898024790797249678202743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265349860531499785468495 4898024790797249678202743)
      ·
        refine ⟨7347037186195874517304115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898024790797249678202743 7347037186195874517304115)
        ·
          refine ⟨11020555779293811775956173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347037186195874517304115 11020555779293811775956173)
          ·
            refine ⟨4132708417235179415983565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11020555779293811775956173 4132708417235179415983565)
            ·
              refine ⟨1549765656463192280993837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4132708417235179415983565 1549765656463192280993837)
              ·
                refine ⟨581162121173697105372689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549765656463192280993837 581162121173697105372689)
                ·
                  refine ⟨435871590880272829029517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581162121173697105372689 435871590880272829029517)
                  ·
                    rfl

theorem cell20_954964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_954964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954964 prefixEnd_954964 := by exact prefixLift 954964
  have htrace : WordTrace (prefixWord ++ tailWord_954964) baseStart_954964 baseEnd_954964 := by
    simpa [prefixWord, tailWord_954964, baseEnd_954964] using wordTrace_append hprefix tailTrace_954964
  have hstable : (prefixWord ++ tailWord_954964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954964).length < 2 ^ (prefixWord ++ tailWord_954964).sum := by decide
  have hdescent : baseEnd_954964 < baseStart_954964 := by decide
  rcases family_descends (prefixWord ++ tailWord_954964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954981 : List Nat := [1, 3, 1, 3, 4, 1, 3, 2, 2]
def baseStart_954981 : Nat := 118140960795 + 954981 * 2 ^ 59
def prefixEnd_954981 : Nat := 4983230072969 + 3 ^ 40 * 954981 * 2
def baseEnd_954981 : Nat := 435879350143496325462781

theorem tailTrace_954981 : CollatzResearch.WordTrace tailWord_954981 prefixEnd_954981 435879350143496325462781 := by
  unfold tailWord_954981
  simp only [CollatzResearch.WordTrace]
  refine ⟨34831018553274409615032797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23220679035516273076688531 34831018553274409615032797)
  ·
    refine ⟨13061631957477903605637299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34831018553274409615032797 13061631957477903605637299)
    ·
      refine ⟨19592447936216855408455949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061631957477903605637299 19592447936216855408455949)
      ·
        refine ⟨7347167976081320778170981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19592447936216855408455949 7347167976081320778170981)
        ·
          refine ⟨1377593995515247645907059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7347167976081320778170981 1377593995515247645907059)
          ·
            refine ⟨2066390993272871468860589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377593995515247645907059 2066390993272871468860589)
            ·
              refine ⟨774896622477326800822721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2066390993272871468860589 774896622477326800822721)
              ·
                refine ⟨581172466857995100617041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774896622477326800822721 581172466857995100617041)
                ·
                  refine ⟨435879350143496325462781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581172466857995100617041 435879350143496325462781)
                  ·
                    rfl

theorem cell20_954981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_954981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954981 prefixEnd_954981 := by exact prefixLift 954981
  have htrace : WordTrace (prefixWord ++ tailWord_954981) baseStart_954981 baseEnd_954981 := by
    simpa [prefixWord, tailWord_954981, baseEnd_954981] using wordTrace_append hprefix tailTrace_954981
  have hstable : (prefixWord ++ tailWord_954981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954981).length < 2 ^ (prefixWord ++ tailWord_954981).sum := by decide
  have hdescent : baseEnd_954981 < baseStart_954981 := by decide
  rcases family_descends (prefixWord ++ tailWord_954981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954992 : List Nat := [2, 1, 1, 1, 7, 1, 2, 5]
def baseStart_954992 : Nat := 118140960795 + 954992 * 2 ^ 59
def prefixEnd_954992 : Nat := 4983230072969 + 3 ^ 40 * 954992 * 2
def baseEnd_954992 : Nat := 145294790281076392032023

theorem tailTrace_954992 : CollatzResearch.WordTrace tailWord_954992 prefixEnd_954992 145294790281076392032023 := by
  unfold tailWord_954992
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415709878117279246841615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23220946504156372329122153 17415709878117279246841615)
  ·
    refine ⟨26123564817175918870262423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17415709878117279246841615 26123564817175918870262423)
    ·
      refine ⟨39185347225763878305393635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26123564817175918870262423 39185347225763878305393635)
      ·
        refine ⟨58778020838645817458090453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39185347225763878305393635 58778020838645817458090453)
        ·
          refine ⟨1377609863405761346673995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58778020838645817458090453 1377609863405761346673995)
          ·
            refine ⟨2066414795108642020010993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377609863405761346673995 2066414795108642020010993)
            ·
              refine ⟨1549811096331481515008245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066414795108642020010993 1549811096331481515008245)
              ·
                refine ⟨145294790281076392032023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1549811096331481515008245 145294790281076392032023)
                ·
                  rfl

theorem cell20_954992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_954992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_954992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_954992 prefixEnd_954992 := by exact prefixLift 954992
  have htrace : WordTrace (prefixWord ++ tailWord_954992) baseStart_954992 baseEnd_954992 := by
    simpa [prefixWord, tailWord_954992, baseEnd_954992] using wordTrace_append hprefix tailTrace_954992
  have hstable : (prefixWord ++ tailWord_954992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954992).length < 2 ^ (prefixWord ++ tailWord_954992).sum := by decide
  have hdescent : baseEnd_954992 < baseStart_954992 := by decide
  rcases family_descends (prefixWord ++ tailWord_954992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955013 : List Nat := [1, 3, 1, 1, 4, 2, 2, 6]
def baseStart_955013 : Nat := 118140960795 + 955013 * 2 ^ 59
def prefixEnd_955013 : Nat := 4983230072969 + 3 ^ 40 * 955013 * 2
def baseEnd_955013 : Nat := 145297985271815478798661

theorem tailTrace_955013 : CollatzResearch.WordTrace tailWord_955013 prefixEnd_955013 145297985271815478798661 := by
  unfold tailWord_955013
  simp only [CollatzResearch.WordTrace]
  refine ⟨34832185689158479080197693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23221457126105652720131795 34832185689158479080197693)
  ·
    refine ⟨13062069633434429655074135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34832185689158479080197693 13062069633434429655074135)
    ·
      refine ⟨19593104450151644482611203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13062069633434429655074135 19593104450151644482611203)
      ·
        refine ⟨29389656675227466723916805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19593104450151644482611203 29389656675227466723916805)
        ·
          refine ⟨5510560626605150010734401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29389656675227466723916805 5510560626605150010734401)
          ·
            refine ⟨4132920469953862508050801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5510560626605150010734401 4132920469953862508050801)
            ·
              refine ⟨3099690352465396881038101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132920469953862508050801 3099690352465396881038101)
              ·
                refine ⟨145297985271815478798661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3099690352465396881038101 145297985271815478798661)
                ·
                  rfl

theorem cell20_955013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_955013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955013 prefixEnd_955013 := by exact prefixLift 955013
  have htrace : WordTrace (prefixWord ++ tailWord_955013) baseStart_955013 baseEnd_955013 := by
    simpa [prefixWord, tailWord_955013, baseEnd_955013] using wordTrace_append hprefix tailTrace_955013
  have hstable : (prefixWord ++ tailWord_955013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955013).length < 2 ^ (prefixWord ++ tailWord_955013).sum := by decide
  have hdescent : baseEnd_955013 < baseStart_955013 := by decide
  rcases family_descends (prefixWord ++ tailWord_955013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955020 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_955020 : Nat := 118140960795 + 955020 * 2 ^ 59
def prefixEnd_955020 : Nat := 4983230072969 + 3 ^ 40 * 955020 * 2
def baseEnd_955020 : Nat := 435897150806185523162621

theorem tailTrace_955020 : CollatzResearch.WordTrace tailWord_955020 prefixEnd_955020 435897150806185523162621 := by
  unfold tailWord_955020
  simp only [CollatzResearch.WordTrace]
  refine ⟨17416220500066559637851257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23221627333422079517135009 17416220500066559637851257)
  ·
    refine ⟨13062165375049919728388443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17416220500066559637851257 13062165375049919728388443)
    ·
      refine ⟨19593248062574879592582665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13062165375049919728388443 19593248062574879592582665)
      ·
        refine ⟨14694936046931159694436999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19593248062574879592582665 14694936046931159694436999)
        ·
          refine ⟨22042404070396739541655499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14694936046931159694436999 22042404070396739541655499)
          ·
            refine ⟨33063606105595109312483249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22042404070396739541655499 33063606105595109312483249)
            ·
              refine ⟨24797704579196331984362437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33063606105595109312483249 24797704579196331984362437)
              ·
                refine ⟨4649569608599312247067957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24797704579196331984362437 4649569608599312247067957)
                ·
                  refine ⟨435897150806185523162621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4649569608599312247067957 435897150806185523162621)
                  ·
                    rfl

theorem cell20_955020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_955020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955020 prefixEnd_955020 := by exact prefixLift 955020
  have htrace : WordTrace (prefixWord ++ tailWord_955020) baseStart_955020 baseEnd_955020 := by
    simpa [prefixWord, tailWord_955020, baseEnd_955020] using wordTrace_append hprefix tailTrace_955020
  have hstable : (prefixWord ++ tailWord_955020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955020).length < 2 ^ (prefixWord ++ tailWord_955020).sum := by decide
  have hdescent : baseEnd_955020 < baseStart_955020 := by decide
  rcases family_descends (prefixWord ++ tailWord_955020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955027 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_955027 : Nat := 118140960795 + 955027 * 2 ^ 59
def prefixEnd_955027 : Nat := 4983230072969 + 3 ^ 40 * 955027 * 2
def baseEnd_955027 : Nat := 435900345796924609929259

theorem tailTrace_955027 : CollatzResearch.WordTrace tailWord_955027 prefixEnd_955027 435900345796924609929259 := by
  unfold tailWord_955027
  simp only [CollatzResearch.WordTrace]
  refine ⟨34832696311107759471207335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23221797540738506314138223 34832696311107759471207335)
  ·
    refine ⟨52249044466661639206811003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34832696311107759471207335 52249044466661639206811003)
    ·
      refine ⟨78373566699992458810216505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52249044466661639206811003 78373566699992458810216505)
      ·
        refine ⟨58780175024994344107662379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78373566699992458810216505 58780175024994344107662379)
        ·
          refine ⟨88170262537491516161493569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58780175024994344107662379 88170262537491516161493569)
          ·
            refine ⟨66127696903118637121120177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88170262537491516161493569 66127696903118637121120177)
            ·
              refine ⟨49595772677338977840840133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66127696903118637121120177 49595772677338977840840133)
              ·
                refine ⟨9299207377001058345157525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49595772677338977840840133 9299207377001058345157525)
                ·
                  refine ⟨435900345796924609929259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9299207377001058345157525 435900345796924609929259)
                  ·
                    rfl

theorem cell20_955027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_955027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955027 prefixEnd_955027 := by exact prefixLift 955027
  have htrace : WordTrace (prefixWord ++ tailWord_955027) baseStart_955027 baseEnd_955027 := by
    simpa [prefixWord, tailWord_955027, baseEnd_955027] using wordTrace_append hprefix tailTrace_955027
  have hstable : (prefixWord ++ tailWord_955027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955027).length < 2 ^ (prefixWord ++ tailWord_955027).sum := by decide
  have hdescent : baseEnd_955027 < baseStart_955027 := by decide
  rcases family_descends (prefixWord ++ tailWord_955027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955037 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 3]
def baseStart_955037 : Nat := 118140960795 + 955037 * 2 ^ 59
def prefixEnd_955037 : Nat := 4983230072969 + 3 ^ 40 * 955037 * 2
def baseEnd_955037 : Nat := 435904910069409019595885

theorem tailTrace_955037 : CollatzResearch.WordTrace tailWord_955037 prefixEnd_955037 435904910069409019595885 := by
  unfold tailWord_955037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34833061041071531179071365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23222040694047687452714243 34833061041071531179071365)
  ·
    refine ⟨6531198945200912096075881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34833061041071531179071365 6531198945200912096075881)
    ·
      refine ⟨4898399208900684072056911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6531198945200912096075881 4898399208900684072056911)
      ·
        refine ⟨7347598813351026108085367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898399208900684072056911 7347598813351026108085367)
        ·
          refine ⟨11021398220026539162128051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347598813351026108085367 11021398220026539162128051)
          ·
            refine ⟨16532097330039808743192077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021398220026539162128051 16532097330039808743192077)
            ·
              refine ⟨6199536498764928278697029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16532097330039808743192077 6199536498764928278697029)
              ·
                refine ⟨1162413093518424052255693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6199536498764928278697029 1162413093518424052255693)
                ·
                  refine ⟨435904910069409019595885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162413093518424052255693 435904910069409019595885)
                  ·
                    rfl

theorem cell20_955037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_955037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955037 prefixEnd_955037 := by exact prefixLift 955037
  have htrace : WordTrace (prefixWord ++ tailWord_955037) baseStart_955037 baseEnd_955037 := by
    simpa [prefixWord, tailWord_955037, baseEnd_955037] using wordTrace_append hprefix tailTrace_955037
  have hstable : (prefixWord ++ tailWord_955037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955037).length < 2 ^ (prefixWord ++ tailWord_955037).sum := by decide
  have hdescent : baseEnd_955037 < baseStart_955037 := by decide
  rcases family_descends (prefixWord ++ tailWord_955037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955040 : List Nat := [2, 1, 1, 4, 4, 1, 1, 4, 2]
def baseStart_955040 : Nat := 118140960795 + 955040 * 2 ^ 59
def prefixEnd_955040 : Nat := 4983230072969 + 3 ^ 40 * 955040 * 2
def baseEnd_955040 : Nat := 435906279351154342495873

theorem tailTrace_955040 : CollatzResearch.WordTrace tailWord_955040 prefixEnd_955040 435906279351154342495873 := by
  unfold tailWord_955040
  simp only [CollatzResearch.WordTrace]
  refine ⟨17416585230030331345715287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23222113640040441794287049 17416585230030331345715287)
  ·
    refine ⟨26124877845045497018572931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17416585230030331345715287 26124877845045497018572931)
    ·
      refine ⟨39187316767568245527859397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26124877845045497018572931 39187316767568245527859397)
      ·
        refine ⟨7347621893919046036473637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39187316767568245527859397 7347621893919046036473637)
        ·
          refine ⟨1377679105109821131838807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7347621893919046036473637 1377679105109821131838807)
          ·
            refine ⟨2066518657664731697758211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377679105109821131838807 2066518657664731697758211)
            ·
              refine ⟨3099777986497097546637317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066518657664731697758211 3099777986497097546637317)
              ·
                refine ⟨581208372468205789994497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3099777986497097546637317 581208372468205789994497)
                ·
                  refine ⟨435906279351154342495873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581208372468205789994497 435906279351154342495873)
                  ·
                    rfl

theorem cell20_955040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_955040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955040 prefixEnd_955040 := by exact prefixLift 955040
  have htrace : WordTrace (prefixWord ++ tailWord_955040) baseStart_955040 baseEnd_955040 := by
    simpa [prefixWord, tailWord_955040, baseEnd_955040] using wordTrace_append hprefix tailTrace_955040
  have hstable : (prefixWord ++ tailWord_955040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955040).length < 2 ^ (prefixWord ++ tailWord_955040).sum := by decide
  have hdescent : baseEnd_955040 < baseStart_955040 := by decide
  rcases family_descends (prefixWord ++ tailWord_955040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955044 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_955044 : Nat := 118140960795 + 955044 * 2 ^ 59
def prefixEnd_955044 : Nat := 4983230072969 + 3 ^ 40 * 955044 * 2
def baseEnd_955044 : Nat := 435908105060148106362523

theorem tailTrace_955044 : CollatzResearch.WordTrace tailWord_955044 prefixEnd_955044 435908105060148106362523 := by
  unfold tailWord_955044
  simp only [CollatzResearch.WordTrace]
  refine ⟨17416658176023085687288093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23222210901364114249717457 17416658176023085687288093)
  ·
    refine ⟨6531246816008657132733035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17416658176023085687288093 6531246816008657132733035)
    ·
      refine ⟨9796870224012985699099553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6531246816008657132733035 9796870224012985699099553)
      ·
        refine ⟨7347652668009739274324665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9796870224012985699099553 7347652668009739274324665)
        ·
          refine ⟨5510739501007304455743499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7347652668009739274324665 5510739501007304455743499)
          ·
            refine ⟨8266109251510956683615249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510739501007304455743499 8266109251510956683615249)
            ·
              refine ⟨6199581938633217512711437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8266109251510956683615249 6199581938633217512711437)
              ·
                refine ⟨2324843226987456567266789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6199581938633217512711437 2324843226987456567266789)
                ·
                  refine ⟨435908105060148106362523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324843226987456567266789 435908105060148106362523)
                  ·
                    rfl

theorem cell20_955044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_955044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955044 prefixEnd_955044 := by exact prefixLift 955044
  have htrace : WordTrace (prefixWord ++ tailWord_955044) baseStart_955044 baseEnd_955044 := by
    simpa [prefixWord, tailWord_955044, baseEnd_955044] using wordTrace_append hprefix tailTrace_955044
  have hstable : (prefixWord ++ tailWord_955044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955044).length < 2 ^ (prefixWord ++ tailWord_955044).sum := by decide
  have hdescent : baseEnd_955044 < baseStart_955044 := by decide
  rcases family_descends (prefixWord ++ tailWord_955044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955058 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_955058 : Nat := 118140960795 + 955058 * 2 ^ 59
def prefixEnd_955058 : Nat := 4983230072969 + 3 ^ 40 * 955058 * 2
def baseEnd_955058 : Nat := 435914495041626279895799

theorem tailTrace_955058 : CollatzResearch.WordTrace tailWord_955058 prefixEnd_955058 435914495041626279895799 := by
  unfold tailWord_955058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708456743498862941396457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23222551315996967843723885 8708456743498862941396457)
  ·
    refine ⟨6531342557624147206047343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8708456743498862941396457 6531342557624147206047343)
    ·
      refine ⟨9797013836436220809071015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6531342557624147206047343 9797013836436220809071015)
      ·
        refine ⟨14695520754654331213606523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9797013836436220809071015 14695520754654331213606523)
        ·
          refine ⟨22043281131981496820409785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14695520754654331213606523 22043281131981496820409785)
          ·
            refine ⟨16532460848986122615307339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22043281131981496820409785 16532460848986122615307339)
            ·
              refine ⟨24798691273479183922961009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16532460848986122615307339 24798691273479183922961009)
              ·
                refine ⟨18599018455109387942220757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24798691273479183922961009 18599018455109387942220757)
                ·
                  refine ⟨435914495041626279895799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18599018455109387942220757 435914495041626279895799)
                  ·
                    rfl

theorem cell20_955058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_955058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955058 prefixEnd_955058 := by exact prefixLift 955058
  have htrace : WordTrace (prefixWord ++ tailWord_955058) baseStart_955058 baseEnd_955058 := by
    simpa [prefixWord, tailWord_955058, baseEnd_955058] using wordTrace_append hprefix tailTrace_955058
  have hstable : (prefixWord ++ tailWord_955058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955058).length < 2 ^ (prefixWord ++ tailWord_955058).sum := by decide
  have hdescent : baseEnd_955058 < baseStart_955058 := by decide
  rcases family_descends (prefixWord ++ tailWord_955058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955061 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_955061 : Nat := 118140960795 + 955061 * 2 ^ 59
def prefixEnd_955061 : Nat := 4983230072969 + 3 ^ 40 * 955061 * 2
def baseEnd_955061 : Nat := 435915864323371602795787

theorem tailTrace_955061 : CollatzResearch.WordTrace tailWord_955061 prefixEnd_955061 435915864323371602795787 := by
  unfold tailWord_955061
  simp only [CollatzResearch.WordTrace]
  refine ⟨34833936392984583277945037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23222624261989722185296691 34833936392984583277945037)
  ·
    refine ⟨13062726147369218729229389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34833936392984583277945037 13062726147369218729229389)
    ·
      refine ⟨4898522305263457023461021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13062726147369218729229389 4898522305263457023461021)
      ·
        refine ⟨1836945864473796383797883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4898522305263457023461021 1836945864473796383797883)
        ·
          refine ⟨2755418796710694575696825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836945864473796383797883 2755418796710694575696825)
          ·
            refine ⟨2066564097533020931772619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2755418796710694575696825 2066564097533020931772619)
            ·
              refine ⟨3099846146299531397658929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066564097533020931772619 3099846146299531397658929)
              ·
                refine ⟨2324884609724648548244197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099846146299531397658929 2324884609724648548244197)
                ·
                  refine ⟨435915864323371602795787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324884609724648548244197 435915864323371602795787)
                  ·
                    rfl

theorem cell20_955061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_955061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955061 prefixEnd_955061 := by exact prefixLift 955061
  have htrace : WordTrace (prefixWord ++ tailWord_955061) baseStart_955061 baseEnd_955061 := by
    simpa [prefixWord, tailWord_955061, baseEnd_955061] using wordTrace_append hprefix tailTrace_955061
  have hstable : (prefixWord ++ tailWord_955061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955061).length < 2 ^ (prefixWord ++ tailWord_955061).sum := by decide
  have hdescent : baseEnd_955061 < baseStart_955061 := by decide
  rcases family_descends (prefixWord ++ tailWord_955061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955068 : List Nat := [2, 2, 2, 3, 1, 1, 5, 4]
def baseStart_955068 : Nat := 118140960795 + 955068 * 2 ^ 59
def prefixEnd_955068 : Nat := 4983230072969 + 3 ^ 40 * 955068 * 2
def baseEnd_955068 : Nat := 145306353104703563187475

theorem tailTrace_955068 : CollatzResearch.WordTrace tailWord_955068 prefixEnd_955068 145306353104703563187475 := by
  unfold tailWord_955068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17417095851979611736724929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23222794469306148982299905 17417095851979611736724929)
  ·
    refine ⟨13062821888984708802543697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17417095851979611736724929 13062821888984708802543697)
    ·
      refine ⟨9797116416738531601907773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13062821888984708802543697 9797116416738531601907773)
      ·
        refine ⟨3673918656276949350715415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9797116416738531601907773 3673918656276949350715415)
        ·
          refine ⟨5510877984415424026073123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673918656276949350715415 5510877984415424026073123)
          ·
            refine ⟨8266316976623136039109685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510877984415424026073123 8266316976623136039109685)
            ·
              refine ⟨774967216558419003666533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8266316976623136039109685 774967216558419003666533)
              ·
                refine ⟨145306353104703563187475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774967216558419003666533 145306353104703563187475)
                ·
                  rfl

theorem cell20_955068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_955068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955068 prefixEnd_955068 := by exact prefixLift 955068
  have htrace : WordTrace (prefixWord ++ tailWord_955068) baseStart_955068 baseEnd_955068 := by
    simpa [prefixWord, tailWord_955068, baseEnd_955068] using wordTrace_append hprefix tailTrace_955068
  have hstable : (prefixWord ++ tailWord_955068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955068).length < 2 ^ (prefixWord ++ tailWord_955068).sum := by decide
  have hdescent : baseEnd_955068 < baseStart_955068 := by decide
  rcases family_descends (prefixWord ++ tailWord_955068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955085 : List Nat := [1, 6, 2, 1, 2, 1, 7]
def baseStart_955085 : Nat := 118140960795 + 955085 * 2 ^ 59
def prefixEnd_955085 : Nat := 4983230072969 + 3 ^ 40 * 955085 * 2
def baseEnd_955085 : Nat := 48436313175259353999521

theorem tailTrace_955085 : CollatzResearch.WordTrace tailWord_955085 prefixEnd_955085 48436313175259353999521 := by
  unfold tailWord_955085
  simp only [CollatzResearch.WordTrace]
  refine ⟨34834811744897635376818709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23223207829931756917879139 34834811744897635376818709)
  ·
    refine ⟨1632881800542076658288377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34834811744897635376818709 1632881800542076658288377)
    ·
      refine ⟨1224661350406557493716283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1632881800542076658288377 1224661350406557493716283)
      ·
        refine ⟨1836992025609836240574425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224661350406557493716283 1836992025609836240574425)
        ·
          refine ⟨1377744019207377180430819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836992025609836240574425 1377744019207377180430819)
          ·
            refine ⟨2066616028811065770646229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377744019207377180430819 2066616028811065770646229)
            ·
              refine ⟨48436313175259353999521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2066616028811065770646229 48436313175259353999521)
              ·
                rfl

theorem cell20_955085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 7].length) (baseStart_955085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955085 prefixEnd_955085 := by exact prefixLift 955085
  have htrace : WordTrace (prefixWord ++ tailWord_955085) baseStart_955085 baseEnd_955085 := by
    simpa [prefixWord, tailWord_955085, baseEnd_955085] using wordTrace_append hprefix tailTrace_955085
  have hstable : (prefixWord ++ tailWord_955085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955085).length < 2 ^ (prefixWord ++ tailWord_955085).sum := by decide
  have hdescent : baseEnd_955085 < baseStart_955085 := by decide
  rcases family_descends (prefixWord ++ tailWord_955085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955092 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_955092 : Nat := 118140960795 + 955092 * 2 ^ 59
def prefixEnd_955092 : Nat := 4983230072969 + 3 ^ 40 * 955092 * 2
def baseEnd_955092 : Nat := 435930013568073272762327

theorem tailTrace_955092 : CollatzResearch.WordTrace tailWord_955092 prefixEnd_955092 435930013568073272762327 := by
  unfold tailWord_955092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17417533527936137786161765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23223378037248183714882353 17417533527936137786161765)
  ·
    refine ⟨3265787536488025834905331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17417533527936137786161765 3265787536488025834905331)
    ·
      refine ⟨4898681304732038752357997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265787536488025834905331 4898681304732038752357997)
      ·
        refine ⟨1837005489274514532134249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4898681304732038752357997 1837005489274514532134249)
        ·
          refine ⟨1377754116955885899100687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837005489274514532134249 1377754116955885899100687)
          ·
            refine ⟨2066631175433828848651031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377754116955885899100687 2066631175433828848651031)
            ·
              refine ⟨3099946763150743272976547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066631175433828848651031 3099946763150743272976547)
              ·
                refine ⟨4649920144726114909464821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099946763150743272976547 4649920144726114909464821)
                ·
                  refine ⟨435930013568073272762327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4649920144726114909464821 435930013568073272762327)
                  ·
                    rfl

theorem cell20_955092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_955092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955092 prefixEnd_955092 := by exact prefixLift 955092
  have htrace : WordTrace (prefixWord ++ tailWord_955092) baseStart_955092 baseEnd_955092 := by
    simpa [prefixWord, tailWord_955092, baseEnd_955092] using wordTrace_append hprefix tailTrace_955092
  have hstable : (prefixWord ++ tailWord_955092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955092).length < 2 ^ (prefixWord ++ tailWord_955092).sum := by decide
  have hdescent : baseEnd_955092 < baseStart_955092 := by decide
  rcases family_descends (prefixWord ++ tailWord_955092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955141 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_955141 : Nat := 118140960795 + 955141 * 2 ^ 59
def prefixEnd_955141 : Nat := 4983230072969 + 3 ^ 40 * 955141 * 2
def baseEnd_955141 : Nat := 435952378503246880128793

theorem tailTrace_955141 : CollatzResearch.WordTrace tailWord_955141 prefixEnd_955141 435952378503246880128793 := by
  unfold tailWord_955141
  simp only [CollatzResearch.WordTrace]
  refine ⟨34836854232694756940857277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23224569488463171293904851 34836854232694756940857277)
  ·
    refine ⟨13063820337260533852821479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34836854232694756940857277 13063820337260533852821479)
    ·
      refine ⟨19595730505890800779232219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13063820337260533852821479 19595730505890800779232219)
      ·
        refine ⟨29393595758836201168848329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19595730505890800779232219 29393595758836201168848329)
        ·
          refine ⟨22045196819127150876636247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29393595758836201168848329 22045196819127150876636247)
          ·
            refine ⟨33067795228690726314954371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22045196819127150876636247 33067795228690726314954371)
            ·
              refine ⟨49601692843036089472431557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33067795228690726314954371 49601692843036089472431557)
              ·
                refine ⟨9300317408069266776080917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49601692843036089472431557 9300317408069266776080917)
                ·
                  refine ⟨435952378503246880128793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9300317408069266776080917 435952378503246880128793)
                  ·
                    rfl

theorem cell20_955141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_955141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955141 prefixEnd_955141 := by exact prefixLift 955141
  have htrace : WordTrace (prefixWord ++ tailWord_955141) baseStart_955141 baseEnd_955141 := by
    simpa [prefixWord, tailWord_955141, baseEnd_955141] using wordTrace_append hprefix tailTrace_955141
  have hstable : (prefixWord ++ tailWord_955141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955141).length < 2 ^ (prefixWord ++ tailWord_955141).sum := by decide
  have hdescent : baseEnd_955141 < baseStart_955141 := by decide
  rcases family_descends (prefixWord ++ tailWord_955141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955168 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_955168 : Nat := 118140960795 + 955168 * 2 ^ 59
def prefixEnd_955168 : Nat := 4983230072969 + 3 ^ 40 * 955168 * 2
def baseEnd_955168 : Nat := 435964702038954786228683

theorem tailTrace_955168 : CollatzResearch.WordTrace tailWord_955168 prefixEnd_955168 435964702038954786228683 := by
  unfold tailWord_955168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17418919501798470276045079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23225226002397960368060105 17418919501798470276045079)
  ·
    refine ⟨26128379252697705414067619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17418919501798470276045079 26128379252697705414067619)
    ·
      refine ⟨39192568879046558121101429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26128379252697705414067619 39192568879046558121101429)
      ·
        refine ⟨3674303332410614823853259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39192568879046558121101429 3674303332410614823853259)
        ·
          refine ⟨5511454998615922235779889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674303332410614823853259 5511454998615922235779889)
          ·
            refine ⟨4133591248961941676834917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5511454998615922235779889 4133591248961941676834917)
            ·
              refine ⟨775048359180364064406547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4133591248961941676834917 775048359180364064406547)
              ·
                refine ⟨1162572538770546096609821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775048359180364064406547 1162572538770546096609821)
                ·
                  refine ⟨435964702038954786228683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162572538770546096609821 435964702038954786228683)
                  ·
                    rfl

theorem cell20_955168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_955168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955168 prefixEnd_955168 := by exact prefixLift 955168
  have htrace : WordTrace (prefixWord ++ tailWord_955168) baseStart_955168 baseEnd_955168 := by
    simpa [prefixWord, tailWord_955168, baseEnd_955168] using wordTrace_append hprefix tailTrace_955168
  have hstable : (prefixWord ++ tailWord_955168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955168).length < 2 ^ (prefixWord ++ tailWord_955168).sum := by decide
  have hdescent : baseEnd_955168 < baseStart_955168 := by decide
  rcases family_descends (prefixWord ++ tailWord_955168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955182 : List Nat := [4, 1, 3, 2, 1, 1, 2, 6]
def baseStart_955182 : Nat := 118140960795 + 955182 * 2 ^ 59
def prefixEnd_955182 : Nat := 4983230072969 + 3 ^ 40 * 955182 * 2
def baseEnd_955182 : Nat := 145323697340144319920653

theorem tailTrace_955182 : CollatzResearch.WordTrace tailWord_955182 prefixEnd_955182 145323697340144319920653 := by
  unfold tailWord_955182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354793703193277617887475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23225566417030813962066533 4354793703193277617887475)
  ·
    refine ⟨6532190554789916426831213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4354793703193277617887475 6532190554789916426831213)
    ·
      refine ⟨2449571458046218660061705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6532190554789916426831213 2449571458046218660061705)
      ·
        refine ⟨1837178593534663995046279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2449571458046218660061705 1837178593534663995046279)
        ·
          refine ⟨2755767890301995992569419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837178593534663995046279 2755767890301995992569419)
          ·
            refine ⟨4133651835452993988854129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755767890301995992569419 4133651835452993988854129)
            ·
              refine ⟨3100238876589745491640597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4133651835452993988854129 3100238876589745491640597)
              ·
                refine ⟨145323697340144319920653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3100238876589745491640597 145323697340144319920653)
                ·
                  rfl

theorem cell20_955182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_955182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955182 prefixEnd_955182 := by exact prefixLift 955182
  have htrace : WordTrace (prefixWord ++ tailWord_955182) baseStart_955182 baseEnd_955182 := by
    simpa [prefixWord, tailWord_955182, baseEnd_955182] using wordTrace_append hprefix tailTrace_955182
  have hstable : (prefixWord ++ tailWord_955182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955182).length < 2 ^ (prefixWord ++ tailWord_955182).sum := by decide
  have hdescent : baseEnd_955182 < baseStart_955182 := by decide
  rcases family_descends (prefixWord ++ tailWord_955182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955272 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_955272 : Nat := 118140960795 + 955272 * 2 ^ 59
def prefixEnd_955272 : Nat := 4983230072969 + 3 ^ 40 * 955272 * 2
def baseEnd_955272 : Nat := 436012170472792646761591

theorem tailTrace_955272 : CollatzResearch.WordTrace tailWord_955272 prefixEnd_955272 436012170472792646761591 := by
  unfold tailWord_955272
  simp only [CollatzResearch.WordTrace]
  refine ⟨17420816097610083156938035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23227754796813444209250713 17420816097610083156938035)
  ·
    refine ⟨26131224146415124735407053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17420816097610083156938035 26131224146415124735407053)
    ·
      refine ⟨9799209054905671775777645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26131224146415124735407053 9799209054905671775777645)
      ·
        refine ⟨3674703395589626915916617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9799209054905671775777645 3674703395589626915916617)
        ·
          refine ⟨2756027546692220186937463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3674703395589626915916617 2756027546692220186937463)
          ·
            refine ⟨4134041320038330280406195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756027546692220186937463 4134041320038330280406195)
            ·
              refine ⟨6201061980057495420609293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134041320038330280406195 6201061980057495420609293)
              ·
                refine ⟨2325398242521560782728485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6201061980057495420609293 2325398242521560782728485)
                ·
                  refine ⟨436012170472792646761591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325398242521560782728485 436012170472792646761591)
                  ·
                    rfl

theorem cell20_955272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_955272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955272 prefixEnd_955272 := by exact prefixLift 955272
  have htrace : WordTrace (prefixWord ++ tailWord_955272) baseStart_955272 baseEnd_955272 := by
    simpa [prefixWord, tailWord_955272, baseEnd_955272] using wordTrace_append hprefix tailTrace_955272
  have hstable : (prefixWord ++ tailWord_955272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955272).length < 2 ^ (prefixWord ++ tailWord_955272).sum := by decide
  have hdescent : baseEnd_955272 < baseStart_955272 := by decide
  rcases family_descends (prefixWord ++ tailWord_955272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955292 : List Nat := [2, 2, 3, 3, 3, 1, 2, 4]
def baseStart_955292 : Nat := 118140960795 + 955292 * 2 ^ 59
def prefixEnd_955292 : Nat := 4983230072969 + 3 ^ 40 * 955292 * 2
def baseEnd_955292 : Nat := 145340433005920488698281

theorem tailTrace_955292 : CollatzResearch.WordTrace tailWord_955292 prefixEnd_955292 145340433005920488698281 := by
  unfold tailWord_955292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17421180827573854864802065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23228241103431806486402753 17421180827573854864802065)
  ·
    refine ⟨13065885620680391148601549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17421180827573854864802065 13065885620680391148601549)
    ·
      refine ⟨4899707107755146680725581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13065885620680391148601549 4899707107755146680725581)
      ·
        refine ⟨1837390165408180005272093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4899707107755146680725581 1837390165408180005272093)
        ·
          refine ⟨689021312028067501977035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1837390165408180005272093 689021312028067501977035)
          ·
            refine ⟨1033531968042101252965553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689021312028067501977035 1033531968042101252965553)
            ·
              refine ⟨775148976031575939724165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033531968042101252965553 775148976031575939724165)
              ·
                refine ⟨145340433005920488698281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775148976031575939724165 145340433005920488698281)
                ·
                  rfl

theorem cell20_955292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_955292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955292 prefixEnd_955292 := by exact prefixLift 955292
  have htrace : WordTrace (prefixWord ++ tailWord_955292) baseStart_955292 baseEnd_955292 := by
    simpa [prefixWord, tailWord_955292, baseEnd_955292] using wordTrace_append hprefix tailTrace_955292
  have hstable : (prefixWord ++ tailWord_955292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955292).length < 2 ^ (prefixWord ++ tailWord_955292).sum := by decide
  have hdescent : baseEnd_955292 < baseStart_955292 := by decide
  rcases family_descends (prefixWord ++ tailWord_955292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955378 : List Nat := [3, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_955378 : Nat := 118140960795 + 955378 * 2 ^ 59
def prefixEnd_955378 : Nat := 4983230072969 + 3 ^ 40 * 955378 * 2
def baseEnd_955378 : Nat := 436060551761127389227825

theorem tailTrace_955378 : CollatzResearch.WordTrace tailWord_955378 prefixEnd_955378 436060551761127389227825 := by
  unfold tailWord_955378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8711374583209036604308697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23230332221890764278156525 8711374583209036604308697)
  ·
    refine ⟨6533530937406777453231523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8711374583209036604308697 6533530937406777453231523)
    ·
      refine ⟨9800296406110166179847285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533530937406777453231523 9800296406110166179847285)
      ·
        refine ⟨918777788072828079360683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9800296406110166179847285 918777788072828079360683)
        ·
          refine ⟨1378166682109242119041025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918777788072828079360683 1378166682109242119041025)
          ·
            refine ⟨1033625011581931589280769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378166682109242119041025 1033625011581931589280769)
            ·
              refine ⟨775218758686448691960577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033625011581931589280769 775218758686448691960577)
              ·
                refine ⟨581414069014836518970433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775218758686448691960577 581414069014836518970433)
                ·
                  refine ⟨436060551761127389227825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581414069014836518970433 436060551761127389227825)
                  ·
                    rfl

theorem cell20_955378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_955378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955378 prefixEnd_955378 := by exact prefixLift 955378
  have htrace : WordTrace (prefixWord ++ tailWord_955378) baseStart_955378 baseEnd_955378 := by
    simpa [prefixWord, tailWord_955378, baseEnd_955378] using wordTrace_append hprefix tailTrace_955378
  have hstable : (prefixWord ++ tailWord_955378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955378).length < 2 ^ (prefixWord ++ tailWord_955378).sum := by decide
  have hdescent : baseEnd_955378 < baseStart_955378 := by decide
  rcases family_descends (prefixWord ++ tailWord_955378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955382 : List Nat := [5, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_955382 : Nat := 118140960795 + 955382 * 2 ^ 59
def prefixEnd_955382 : Nat := 4983230072969 + 3 ^ 40 * 955382 * 2
def baseEnd_955382 : Nat := 436062377470121153094475

theorem tailTrace_955382 : CollatzResearch.WordTrace tailWord_955382 prefixEnd_955382 436062377470121153094475 := by
  unfold tailWord_955382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177852764051353443773775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23230429483214436733586933 2177852764051353443773775)
  ·
    refine ⟨3266779146077030165660663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177852764051353443773775 3266779146077030165660663)
    ·
      refine ⟨4900168719115545248490995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3266779146077030165660663 4900168719115545248490995)
      ·
        refine ⟨7350253078673317872736493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900168719115545248490995 7350253078673317872736493)
        ·
          refine ⟨2756344904502494202276185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7350253078673317872736493 2756344904502494202276185)
          ·
            refine ⟨2067258678376870651707139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756344904502494202276185 2067258678376870651707139)
            ·
              refine ⟨3100888017565305977560709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067258678376870651707139 3100888017565305977560709)
              ·
                refine ⟨581416503293494870792633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3100888017565305977560709 581416503293494870792633)
                ·
                  refine ⟨436062377470121153094475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581416503293494870792633 436062377470121153094475)
                  ·
                    rfl

theorem cell20_955382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_955382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955382 prefixEnd_955382 := by exact prefixLift 955382
  have htrace : WordTrace (prefixWord ++ tailWord_955382) baseStart_955382 baseEnd_955382 := by
    simpa [prefixWord, tailWord_955382, baseEnd_955382] using wordTrace_append hprefix tailTrace_955382
  have hstable : (prefixWord ++ tailWord_955382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955382).length < 2 ^ (prefixWord ++ tailWord_955382).sum := by decide
  have hdescent : baseEnd_955382 < baseStart_955382 := by decide
  rcases family_descends (prefixWord ++ tailWord_955382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955393 : List Nat := [1, 2, 4, 1, 2, 2, 3, 5]
def baseStart_955393 : Nat := 118140960795 + 955393 * 2 ^ 59
def prefixEnd_955393 : Nat := 4983230072969 + 3 ^ 40 * 955393 * 2
def baseEnd_955393 : Nat := 145355799389951334575921

theorem tailTrace_955393 : CollatzResearch.WordTrace tailWord_955393 prefixEnd_955393 145355799389951334575921 := by
  unfold tailWord_955393
  simp only [CollatzResearch.WordTrace]
  refine ⟨34846045427781803979030833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23230696951854535986020555 34846045427781803979030833)
  ·
    refine ⟨26134534070836352984273125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34846045427781803979030833 26134534070836352984273125)
    ·
      refine ⟨4900225138281816184551211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26134534070836352984273125 4900225138281816184551211)
      ·
        refine ⟨7350337707422724276826817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900225138281816184551211 7350337707422724276826817)
        ·
          refine ⟨5512753280567043207620113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7350337707422724276826817 5512753280567043207620113)
          ·
            refine ⟨4134564960425282405715085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5512753280567043207620113 4134564960425282405715085)
            ·
              refine ⟨1550461860159480902143157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4134564960425282405715085 1550461860159480902143157)
              ·
                refine ⟨145355799389951334575921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1550461860159480902143157 145355799389951334575921)
                ·
                  rfl

theorem cell20_955393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_955393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955393 prefixEnd_955393 := by exact prefixLift 955393
  have htrace : WordTrace (prefixWord ++ tailWord_955393) baseStart_955393 baseEnd_955393 := by
    simpa [prefixWord, tailWord_955393, baseEnd_955393] using wordTrace_append hprefix tailTrace_955393
  have hstable : (prefixWord ++ tailWord_955393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955393).length < 2 ^ (prefixWord ++ tailWord_955393).sum := by decide
  have hdescent : baseEnd_955393 < baseStart_955393 := by decide
  rcases family_descends (prefixWord ++ tailWord_955393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955420 : List Nat := [2, 2, 3, 1, 4, 1, 2, 3, 2]
def baseStart_955420 : Nat := 118140960795 + 955420 * 2 ^ 59
def prefixEnd_955420 : Nat := 4983230072969 + 3 ^ 40 * 955420 * 2
def baseEnd_955420 : Nat := 436079721705561909827653

theorem tailTrace_955420 : CollatzResearch.WordTrace tailWord_955420 prefixEnd_955420 436079721705561909827653 := by
  unfold tailWord_955420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17423515099341993795131857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23231353465789325060175809 17423515099341993795131857)
  ·
    refine ⟨13067636324506495346348893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17423515099341993795131857 13067636324506495346348893)
    ·
      refine ⟨4900363621689935754880835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13067636324506495346348893 4900363621689935754880835)
      ·
        refine ⟨7350545432534903632321253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900363621689935754880835 7350545432534903632321253)
        ·
          refine ⟨1378227268600294431060235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7350545432534903632321253 1378227268600294431060235)
          ·
            refine ⟨2067340902900441646590353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378227268600294431060235 2067340902900441646590353)
            ·
              refine ⟨1550505677175331234942765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2067340902900441646590353 1550505677175331234942765)
              ·
                refine ⟨581439628940749213103537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1550505677175331234942765 581439628940749213103537)
                ·
                  refine ⟨436079721705561909827653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581439628940749213103537 436079721705561909827653)
                  ·
                    rfl

theorem cell20_955420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_955420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955420 prefixEnd_955420 := by exact prefixLift 955420
  have htrace : WordTrace (prefixWord ++ tailWord_955420) baseStart_955420 baseEnd_955420 := by
    simpa [prefixWord, tailWord_955420, baseEnd_955420] using wordTrace_append hprefix tailTrace_955420
  have hstable : (prefixWord ++ tailWord_955420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955420).length < 2 ^ (prefixWord ++ tailWord_955420).sum := by decide
  have hdescent : baseEnd_955420 < baseStart_955420 := by decide
  rcases family_descends (prefixWord ++ tailWord_955420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955476 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_955476 : Nat := 118140960795 + 955476 * 2 ^ 59
def prefixEnd_955476 : Nat := 4983230072969 + 3 ^ 40 * 955476 * 2
def baseEnd_955476 : Nat := 436105281631474603960757

theorem tailTrace_955476 : CollatzResearch.WordTrace tailWord_955476 prefixEnd_955476 436105281631474603960757 := by
  unfold tailWord_955476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424536343240554577151141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23232715124320739436201521 17424536343240554577151141)
  ·
    refine ⟨3267100564357603983215839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17424536343240554577151141 3267100564357603983215839)
    ·
      refine ⟨4900650846536405974823759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267100564357603983215839 4900650846536405974823759)
      ·
        refine ⟨7350976269804608962235639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900650846536405974823759 7350976269804608962235639)
        ·
          refine ⟨11026464404706913443353459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7350976269804608962235639 11026464404706913443353459)
          ·
            refine ⟨16539696607060370165030189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11026464404706913443353459 16539696607060370165030189)
            ·
              refine ⟨6202386227647638811886321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16539696607060370165030189 6202386227647638811886321)
              ·
                refine ⟨4651789670735729108914741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6202386227647638811886321 4651789670735729108914741)
                ·
                  refine ⟨436105281631474603960757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4651789670735729108914741 436105281631474603960757)
                  ·
                    rfl

theorem cell20_955476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_955476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955476 prefixEnd_955476 := by exact prefixLift 955476
  have htrace : WordTrace (prefixWord ++ tailWord_955476) baseStart_955476 baseEnd_955476 := by
    simpa [prefixWord, tailWord_955476, baseEnd_955476] using wordTrace_append hprefix tailTrace_955476
  have hstable : (prefixWord ++ tailWord_955476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955476).length < 2 ^ (prefixWord ++ tailWord_955476).sum := by decide
  have hdescent : baseEnd_955476 < baseStart_955476 := by decide
  rcases family_descends (prefixWord ++ tailWord_955476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955496 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_955496 : Nat := 118140960795 + 955496 * 2 ^ 59
def prefixEnd_955496 : Nat := 4983230072969 + 3 ^ 40 * 955496 * 2
def baseEnd_955496 : Nat := 436114410176443423294009

theorem tailTrace_955496 : CollatzResearch.WordTrace tailWord_955496 prefixEnd_955496 436114410176443423294009 := by
  unfold tailWord_955496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424901073204326285015171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23233201430939101713353561 17424901073204326285015171)
  ·
    refine ⟨26137351609806489427522757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17424901073204326285015171 26137351609806489427522757)
    ·
      refine ⟨4900753426838716767660517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26137351609806489427522757 4900753426838716767660517)
      ·
        refine ⟨918891267532259393936347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4900753426838716767660517 918891267532259393936347)
        ·
          refine ⟨1378336901298389090904521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918891267532259393936347 1378336901298389090904521)
          ·
            refine ⟨1033752675973791818178391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378336901298389090904521 1033752675973791818178391)
            ·
              refine ⟨1550629013960687727267587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033752675973791818178391 1550629013960687727267587)
              ·
                refine ⟨2325943520941031590901381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550629013960687727267587 2325943520941031590901381)
                ·
                  refine ⟨436114410176443423294009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325943520941031590901381 436114410176443423294009)
                  ·
                    rfl

theorem cell20_955496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_955496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955496 prefixEnd_955496 := by exact prefixLift 955496
  have htrace : WordTrace (prefixWord ++ tailWord_955496) baseStart_955496 baseEnd_955496 := by
    simpa [prefixWord, tailWord_955496, baseEnd_955496] using wordTrace_append hprefix tailTrace_955496
  have hstable : (prefixWord ++ tailWord_955496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955496).length < 2 ^ (prefixWord ++ tailWord_955496).sum := by decide
  have hdescent : baseEnd_955496 < baseStart_955496 := by decide
  rcases family_descends (prefixWord ++ tailWord_955496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955551 : List Nat := [1, 1, 2, 6, 2, 2, 2, 2, 2]
def baseStart_955551 : Nat := 118140960795 + 955551 * 2 ^ 59
def prefixEnd_955551 : Nat := 4983230072969 + 3 ^ 40 * 955551 * 2
def baseEnd_955551 : Nat := 436139513675107676460451

theorem tailTrace_955551 : CollatzResearch.WordTrace tailWord_955551 prefixEnd_955551 436139513675107676460451 := by
  unfold tailWord_955551
  simp only [CollatzResearch.WordTrace]
  refine ⟨34851808161209396963282507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23234538774139597975521671 34851808161209396963282507)
  ·
    refine ⟨52277712241814095444923761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34851808161209396963282507 52277712241814095444923761)
    ·
      refine ⟨39208284181360571583692821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52277712241814095444923761 39208284181360571583692821)
      ·
        refine ⟨1837888321001276792985601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39208284181360571583692821 1837888321001276792985601)
        ·
          refine ⟨1378416240750957594739201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837888321001276792985601 1378416240750957594739201)
          ·
            refine ⟨1033812180563218196054401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378416240750957594739201 1033812180563218196054401)
            ·
              refine ⟨775359135422413647040801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033812180563218196054401 775359135422413647040801)
              ·
                refine ⟨581519351566810235280601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775359135422413647040801 581519351566810235280601)
                ·
                  refine ⟨436139513675107676460451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581519351566810235280601 436139513675107676460451)
                  ·
                    rfl

theorem cell20_955551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 2].length) (baseStart_955551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955551 prefixEnd_955551 := by exact prefixLift 955551
  have htrace : WordTrace (prefixWord ++ tailWord_955551) baseStart_955551 baseEnd_955551 := by
    simpa [prefixWord, tailWord_955551, baseEnd_955551] using wordTrace_append hprefix tailTrace_955551
  have hstable : (prefixWord ++ tailWord_955551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955551).length < 2 ^ (prefixWord ++ tailWord_955551).sum := by decide
  have hdescent : baseEnd_955551 < baseStart_955551 := by decide
  rcases family_descends (prefixWord ++ tailWord_955551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955562 : List Nat := [3, 1, 5, 1, 1, 1, 3, 5]
def baseStart_955562 : Nat := 118140960795 + 955562 * 2 ^ 59
def prefixEnd_955562 : Nat := 4983230072969 + 3 ^ 40 * 955562 * 2
def baseEnd_955562 : Nat := 145381511458280175697913

theorem tailTrace_955562 : CollatzResearch.WordTrace tailWord_955562 prefixEnd_955562 145381511458280175697913 := by
  unfold tailWord_955562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713052341042386460483235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23234806242779697227955293 8713052341042386460483235)
  ·
    refine ⟨13069578511563579690724853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8713052341042386460483235 13069578511563579690724853)
    ·
      refine ⟨1225272985459085596005455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13069578511563579690724853 1225272985459085596005455)
      ·
        refine ⟨1837909478188628394008183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225272985459085596005455 1837909478188628394008183)
        ·
          refine ⟨2756864217282942591012275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837909478188628394008183 2756864217282942591012275)
          ·
            refine ⟨4135296325924413886518413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756864217282942591012275 4135296325924413886518413)
            ·
              refine ⟨1550736122221655207444405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4135296325924413886518413 1550736122221655207444405)
              ·
                refine ⟨145381511458280175697913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1550736122221655207444405 145381511458280175697913)
                ·
                  rfl

theorem cell20_955562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_955562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955562 prefixEnd_955562 := by exact prefixLift 955562
  have htrace : WordTrace (prefixWord ++ tailWord_955562) baseStart_955562 baseEnd_955562 := by
    simpa [prefixWord, tailWord_955562, baseEnd_955562] using wordTrace_append hprefix tailTrace_955562
  have hstable : (prefixWord ++ tailWord_955562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955562).length < 2 ^ (prefixWord ++ tailWord_955562).sum := by decide
  have hdescent : baseEnd_955562 < baseStart_955562 := by decide
  rcases family_descends (prefixWord ++ tailWord_955562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955569 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 3]
def baseStart_955569 : Nat := 118140960795 + 955569 * 2 ^ 59
def prefixEnd_955569 : Nat := 4983230072969 + 3 ^ 40 * 955569 * 2
def baseEnd_955569 : Nat := 436147729365579613860377

theorem tailTrace_955569 : CollatzResearch.WordTrace tailWord_955569 prefixEnd_955569 436147729365579613860377 := by
  unfold tailWord_955569
  simp only [CollatzResearch.WordTrace]
  refine ⟨34852464675144186037437761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23234976450096124024958507 34852464675144186037437761)
  ·
    refine ⟨26139348506358139528078321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34852464675144186037437761 26139348506358139528078321)
    ·
      refine ⟨19604511379768604646058741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26139348506358139528078321 19604511379768604646058741)
      ·
        refine ⟨1837922941853306685568007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19604511379768604646058741 1837922941853306685568007)
        ·
          refine ⟨2756884412779960028352011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837922941853306685568007 2756884412779960028352011)
          ·
            refine ⟨4135326619169940042528017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756884412779960028352011 4135326619169940042528017)
            ·
              refine ⟨3101494964377455031896013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135326619169940042528017 3101494964377455031896013)
              ·
                refine ⟨1163060611641545636961005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3101494964377455031896013 1163060611641545636961005)
                ·
                  refine ⟨436147729365579613860377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163060611641545636961005 436147729365579613860377)
                  ·
                    rfl

theorem cell20_955569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_955569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955569 prefixEnd_955569 := by exact prefixLift 955569
  have htrace : WordTrace (prefixWord ++ tailWord_955569) baseStart_955569 baseEnd_955569 := by
    simpa [prefixWord, tailWord_955569, baseEnd_955569] using wordTrace_append hprefix tailTrace_955569
  have hstable : (prefixWord ++ tailWord_955569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955569).length < 2 ^ (prefixWord ++ tailWord_955569).sum := by decide
  have hdescent : baseEnd_955569 < baseStart_955569 := by decide
  rcases family_descends (prefixWord ++ tailWord_955569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955635 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_955635 : Nat := 118140960795 + 955635 * 2 ^ 59
def prefixEnd_955635 : Nat := 4983230072969 + 3 ^ 40 * 955635 * 2
def baseEnd_955635 : Nat := 436177853563976717660107

theorem tailTrace_955635 : CollatzResearch.WordTrace tailWord_955635 prefixEnd_955635 436177853563976717660107 := by
  unfold tailWord_955635
  simp only [CollatzResearch.WordTrace]
  refine ⟨34854871892905079309340359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23236581261936719539560239 34854871892905079309340359)
  ·
    refine ⟨52282307839357618964010539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34854871892905079309340359 52282307839357618964010539)
    ·
      refine ⟨78423461759036428446015809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52282307839357618964010539 78423461759036428446015809)
      ·
        refine ⟨58817596319277321334511857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78423461759036428446015809 58817596319277321334511857)
        ·
          refine ⟨44113197239457991000883893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58817596319277321334511857 44113197239457991000883893)
          ·
            refine ⟨4135612241199186656332865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44113197239457991000883893 4135612241199186656332865)
            ·
              refine ⟨3101709180899389992249649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135612241199186656332865 3101709180899389992249649)
              ·
                refine ⟨2326281885674542494187237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101709180899389992249649 2326281885674542494187237)
                ·
                  refine ⟨436177853563976717660107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326281885674542494187237 436177853563976717660107)
                  ·
                    rfl

theorem cell20_955635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_955635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955635 prefixEnd_955635 := by exact prefixLift 955635
  have htrace : WordTrace (prefixWord ++ tailWord_955635) baseStart_955635 baseEnd_955635 := by
    simpa [prefixWord, tailWord_955635, baseEnd_955635] using wordTrace_append hprefix tailTrace_955635
  have hstable : (prefixWord ++ tailWord_955635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955635).length < 2 ^ (prefixWord ++ tailWord_955635).sum := by decide
  have hdescent : baseEnd_955635 < baseStart_955635 := by decide
  rcases family_descends (prefixWord ++ tailWord_955635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955642 : List Nat := [3, 1, 1, 1, 1, 4, 3, 6]
def baseStart_955642 : Nat := 118140960795 + 955642 * 2 ^ 59
def prefixEnd_955642 : Nat := 4983230072969 + 3 ^ 40 * 955642 * 2
def baseEnd_955642 : Nat := 145393682851571934808915

theorem tailTrace_955642 : CollatzResearch.WordTrace tailWord_955642 prefixEnd_955642 145393682851571934808915 := by
  unfold tailWord_955642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713781800969929876211295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23236751469253146336563453 8713781800969929876211295)
  ·
    refine ⟨13070672701454894814316943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8713781800969929876211295 13070672701454894814316943)
    ·
      refine ⟨19606009052182342221475415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13070672701454894814316943 19606009052182342221475415)
      ·
        refine ⟨29409013578273513332213123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19606009052182342221475415 29409013578273513332213123)
        ·
          refine ⟨44113520367410269998319685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29409013578273513332213123 44113520367410269998319685)
          ·
            refine ⟨8271285068889425624684941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44113520367410269998319685 8271285068889425624684941)
            ·
              refine ⟨3101731900833534609256853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8271285068889425624684941 3101731900833534609256853)
              ·
                refine ⟨145393682851571934808915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3101731900833534609256853 145393682851571934808915)
                ·
                  rfl

theorem cell20_955642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_955642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955642 prefixEnd_955642 := by exact prefixLift 955642
  have htrace : WordTrace (prefixWord ++ tailWord_955642) baseStart_955642 baseEnd_955642 := by
    simpa [prefixWord, tailWord_955642, baseEnd_955642] using wordTrace_append hprefix tailTrace_955642
  have hstable : (prefixWord ++ tailWord_955642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955642).length < 2 ^ (prefixWord ++ tailWord_955642).sum := by decide
  have hdescent : baseEnd_955642 < baseStart_955642 := by decide
  rcases family_descends (prefixWord ++ tailWord_955642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955679 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 3]
def baseStart_955679 : Nat := 118140960795 + 955679 * 2 ^ 59
def prefixEnd_955679 : Nat := 4983230072969 + 3 ^ 40 * 955679 * 2
def baseEnd_955679 : Nat := 436197936362908120193261

theorem tailTrace_955679 : CollatzResearch.WordTrace tailWord_955679 prefixEnd_955679 436197936362908120193261 := by
  unfold tailWord_955679
  simp only [CollatzResearch.WordTrace]
  refine ⟨34856476704745674823942091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23237651136497116549294727 34856476704745674823942091)
  ·
    refine ⟨52284715057118512235913137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34856476704745674823942091 52284715057118512235913137)
    ·
      refine ⟨39213536292838884176934853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52284715057118512235913137 39213536292838884176934853)
      ·
        refine ⟨7352538054907290783175285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39213536292838884176934853 7352538054907290783175285)
        ·
          refine ⟨689300442647558510922683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7352538054907290783175285 689300442647558510922683)
          ·
            refine ⟨1033950663971337766384025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689300442647558510922683 1033950663971337766384025)
            ·
              refine ⟨775462997978503324788019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033950663971337766384025 775462997978503324788019)
              ·
                refine ⟨1163194496967754987182029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775462997978503324788019 1163194496967754987182029)
                ·
                  refine ⟨436197936362908120193261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163194496967754987182029 436197936362908120193261)
                  ·
                    rfl

theorem cell20_955679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 3].length) (baseStart_955679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955679 prefixEnd_955679 := by exact prefixLift 955679
  have htrace : WordTrace (prefixWord ++ tailWord_955679) baseStart_955679 baseEnd_955679 := by
    simpa [prefixWord, tailWord_955679, baseEnd_955679] using wordTrace_append hprefix tailTrace_955679
  have hstable : (prefixWord ++ tailWord_955679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955679).length < 2 ^ (prefixWord ++ tailWord_955679).sum := by decide
  have hdescent : baseEnd_955679 < baseStart_955679 := by decide
  rcases family_descends (prefixWord ++ tailWord_955679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955683 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 3]
def baseStart_955683 : Nat := 118140960795 + 955683 * 2 ^ 59
def prefixEnd_955683 : Nat := 4983230072969 + 3 ^ 40 * 955683 * 2
def baseEnd_955683 : Nat := 436199762071901884059911

theorem tailTrace_955683 : CollatzResearch.WordTrace tailWord_955683 prefixEnd_955683 436199762071901884059911 := by
  unfold tailWord_955683
  simp only [CollatzResearch.WordTrace]
  refine ⟨34856622596731183507087703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23237748397820789004725135 34856622596731183507087703)
  ·
    refine ⟨52284933895096775260631555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34856622596731183507087703 52284933895096775260631555)
    ·
      refine ⟨78427400842645162890947333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52284933895096775260631555 78427400842645162890947333)
      ·
        refine ⟨14705137657995968042052625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78427400842645162890947333 14705137657995968042052625)
        ·
          refine ⟨11028853243496976031539469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14705137657995968042052625 11028853243496976031539469)
          ·
            refine ⟨4135819966311366011827301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11028853243496976031539469 4135819966311366011827301)
            ·
              refine ⟨775466243683381127217619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4135819966311366011827301 775466243683381127217619)
              ·
                refine ⟨1163199365525071690826429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775466243683381127217619 1163199365525071690826429)
                ·
                  refine ⟨436199762071901884059911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163199365525071690826429 436199762071901884059911)
                  ·
                    rfl

theorem cell20_955683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 3].length) (baseStart_955683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955683 prefixEnd_955683 := by exact prefixLift 955683
  have htrace : WordTrace (prefixWord ++ tailWord_955683) baseStart_955683 baseEnd_955683 := by
    simpa [prefixWord, tailWord_955683, baseEnd_955683] using wordTrace_append hprefix tailTrace_955683
  have hstable : (prefixWord ++ tailWord_955683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955683).length < 2 ^ (prefixWord ++ tailWord_955683).sum := by decide
  have hdescent : baseEnd_955683 < baseStart_955683 := by decide
  rcases family_descends (prefixWord ++ tailWord_955683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955724 : List Nat := [2, 2, 1, 3, 2, 4, 2, 2, 2]
def baseStart_955724 : Nat := 118140960795 + 955724 * 2 ^ 59
def prefixEnd_955724 : Nat := 4983230072969 + 3 ^ 40 * 955724 * 2
def baseEnd_955724 : Nat := 436218475589087963693077

theorem tailTrace_955724 : CollatzResearch.WordTrace tailWord_955724 prefixEnd_955724 436218475589087963693077 := by
  unfold tailWord_955724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17429058994791323754665113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23238745326388431672886817 17429058994791323754665113)
  ·
    refine ⟨13071794246093492815998835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17429058994791323754665113 13071794246093492815998835)
    ·
      refine ⟨19607691369140239223998253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13071794246093492815998835 19607691369140239223998253)
      ·
        refine ⟨7352884263427589708999345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19607691369140239223998253 7352884263427589708999345)
        ·
          refine ⟨5514663197570692281749509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7352884263427589708999345 5514663197570692281749509)
          ·
            refine ⟨1033999349544504802828033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5514663197570692281749509 1033999349544504802828033)
            ·
              refine ⟨775499512158378602121025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033999349544504802828033 775499512158378602121025)
              ·
                refine ⟨581624634118783951590769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775499512158378602121025 581624634118783951590769)
                ·
                  refine ⟨436218475589087963693077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581624634118783951590769 436218475589087963693077)
                  ·
                    rfl

theorem cell20_955724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_955724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955724 prefixEnd_955724 := by exact prefixLift 955724
  have htrace : WordTrace (prefixWord ++ tailWord_955724) baseStart_955724 baseEnd_955724 := by
    simpa [prefixWord, tailWord_955724, baseEnd_955724] using wordTrace_append hprefix tailTrace_955724
  have hstable : (prefixWord ++ tailWord_955724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955724).length < 2 ^ (prefixWord ++ tailWord_955724).sum := by decide
  have hdescent : baseEnd_955724 < baseStart_955724 := by decide
  rcases family_descends (prefixWord ++ tailWord_955724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955728 : List Nat := [2, 1, 1, 1, 1, 5, 3, 4, 2]
def baseStart_955728 : Nat := 118140960795 + 955728 * 2 ^ 59
def prefixEnd_955728 : Nat := 4983230072969 + 3 ^ 40 * 955728 * 2
def baseEnd_955728 : Nat := 436220301298081727559727

theorem tailTrace_955728 : CollatzResearch.WordTrace tailWord_955728 prefixEnd_955728 436220301298081727559727 := by
  unfold tailWord_955728
  simp only [CollatzResearch.WordTrace]
  refine ⟨17429131940784078096237919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23238842587712104128317225 17429131940784078096237919)
  ·
    refine ⟨26143697911176117144356879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17429131940784078096237919 26143697911176117144356879)
    ·
      refine ⟨39215546866764175716535319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26143697911176117144356879 39215546866764175716535319)
      ·
        refine ⟨58823320300146263574802979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39215546866764175716535319 58823320300146263574802979)
        ·
          refine ⟨88234980450219395362204469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58823320300146263574802979 88234980450219395362204469)
          ·
            refine ⟨8272029417208068315206669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88234980450219395362204469 8272029417208068315206669)
            ·
              refine ⟨3102011031453025618202501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272029417208068315206669 3102011031453025618202501)
              ·
                refine ⟨581627068397442303412969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3102011031453025618202501 581627068397442303412969)
                ·
                  refine ⟨436220301298081727559727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581627068397442303412969 436220301298081727559727)
                  ·
                    rfl

theorem cell20_955728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_955728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955728 prefixEnd_955728 := by exact prefixLift 955728
  have htrace : WordTrace (prefixWord ++ tailWord_955728) baseStart_955728 baseEnd_955728 := by
    simpa [prefixWord, tailWord_955728, baseEnd_955728] using wordTrace_append hprefix tailTrace_955728
  have hstable : (prefixWord ++ tailWord_955728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955728).length < 2 ^ (prefixWord ++ tailWord_955728).sum := by decide
  have hdescent : baseEnd_955728 < baseStart_955728 := by decide
  rcases family_descends (prefixWord ++ tailWord_955728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955735 : List Nat := [1, 1, 3, 2, 3, 4, 1, 5]
def baseStart_955735 : Nat := 118140960795 + 955735 * 2 ^ 59
def prefixEnd_955735 : Nat := 4983230072969 + 3 ^ 40 * 955735 * 2
def baseEnd_955735 : Nat := 145407832096273604775455

theorem tailTrace_955735 : CollatzResearch.WordTrace tailWord_955735 prefixEnd_955735 145407832096273604775455 := by
  unfold tailWord_955735
  simp only [CollatzResearch.WordTrace]
  refine ⟨34858519192542796387980659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23239012795028530925320439 34858519192542796387980659)
  ·
    refine ⟨52287778788814194581970989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34858519192542796387980659 52287778788814194581970989)
    ·
      refine ⟨19607917045805322968239121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52287778788814194581970989 19607917045805322968239121)
      ·
        refine ⟨14705937784353992226179341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19607917045805322968239121 14705937784353992226179341)
        ·
          refine ⟨5514726669132747084817253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14705937784353992226179341 5514726669132747084817253)
          ·
            refine ⟨1034011250462390078403235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5514726669132747084817253 1034011250462390078403235)
            ·
              refine ⟨1551016875693585117604853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034011250462390078403235 1551016875693585117604853)
              ·
                refine ⟨145407832096273604775455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1551016875693585117604853 145407832096273604775455)
                ·
                  rfl

theorem cell20_955735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_955735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955735 prefixEnd_955735 := by exact prefixLift 955735
  have htrace : WordTrace (prefixWord ++ tailWord_955735) baseStart_955735 baseEnd_955735 := by
    simpa [prefixWord, tailWord_955735, baseEnd_955735] using wordTrace_append hprefix tailTrace_955735
  have hstable : (prefixWord ++ tailWord_955735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955735).length < 2 ^ (prefixWord ++ tailWord_955735).sum := by decide
  have hdescent : baseEnd_955735 < baseStart_955735 := by decide
  rcases family_descends (prefixWord ++ tailWord_955735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955749 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_955749 : Nat := 118140960795 + 955749 * 2 ^ 59
def prefixEnd_955749 : Nat := 4983230072969 + 3 ^ 40 * 955749 * 2
def baseEnd_955749 : Nat := 436229886270298987859641

theorem tailTrace_955749 : CollatzResearch.WordTrace tailWord_955749 prefixEnd_955749 436229886270298987859641 := by
  unfold tailWord_955749
  simp only [CollatzResearch.WordTrace]
  refine ⟨34859029814492076778990301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23239353209661384519326867 34859029814492076778990301)
  ·
    refine ⟨13072136180434528792121363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34859029814492076778990301 13072136180434528792121363)
    ·
      refine ⟨19608204270651793188182045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13072136180434528792121363 19608204270651793188182045)
      ·
        refine ⟨7353076601494422445568267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19608204270651793188182045 7353076601494422445568267)
        ·
          refine ⟨11029614902241633668352401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353076601494422445568267 11029614902241633668352401)
          ·
            refine ⟨8272211176681225251264301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11029614902241633668352401 8272211176681225251264301)
            ·
              refine ⟨3102079191255459469224113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272211176681225251264301 3102079191255459469224113)
              ·
                refine ⟨2326559393441594601918085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102079191255459469224113 2326559393441594601918085)
                ·
                  refine ⟨436229886270298987859641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326559393441594601918085 436229886270298987859641)
                  ·
                    rfl

theorem cell20_955749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_955749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955749 prefixEnd_955749 := by exact prefixLift 955749
  have htrace : WordTrace (prefixWord ++ tailWord_955749) baseStart_955749 baseEnd_955749 := by
    simpa [prefixWord, tailWord_955749, baseEnd_955749] using wordTrace_append hprefix tailTrace_955749
  have hstable : (prefixWord ++ tailWord_955749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955749).length < 2 ^ (prefixWord ++ tailWord_955749).sum := by decide
  have hdescent : baseEnd_955749 < baseStart_955749 := by decide
  rcases family_descends (prefixWord ++ tailWord_955749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955752 : List Nat := [2, 1, 4, 2, 3, 1, 3, 4]
def baseStart_955752 : Nat := 118140960795 + 955752 * 2 ^ 59
def prefixEnd_955752 : Nat := 4983230072969 + 3 ^ 40 * 955752 * 2
def baseEnd_955752 : Nat := 145410418517348103586543

theorem tailTrace_955752 : CollatzResearch.WordTrace tailWord_955752 prefixEnd_955752 145410418517348103586543 := by
  unfold tailWord_955752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17429569616740604145674755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23239426155654138860899673 17429569616740604145674755)
  ·
    refine ⟨26144354425110906218512133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17429569616740604145674755 26144354425110906218512133)
    ·
      refine ⟨4902066454708294915971025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26144354425110906218512133 4902066454708294915971025)
      ·
        refine ⟨3676549841031221186978269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4902066454708294915971025 3676549841031221186978269)
        ·
          refine ⟨1378706190386707945116851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3676549841031221186978269 1378706190386707945116851)
          ·
            refine ⟨2068059285580061917675277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378706190386707945116851 2068059285580061917675277)
            ·
              refine ⟨775522232092523219128229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2068059285580061917675277 775522232092523219128229)
              ·
                refine ⟨145410418517348103586543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775522232092523219128229 145410418517348103586543)
                ·
                  rfl

theorem cell20_955752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_955752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955752 prefixEnd_955752 := by exact prefixLift 955752
  have htrace : WordTrace (prefixWord ++ tailWord_955752) baseStart_955752 baseEnd_955752 := by
    simpa [prefixWord, tailWord_955752, baseEnd_955752] using wordTrace_append hprefix tailTrace_955752
  have hstable : (prefixWord ++ tailWord_955752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955752).length < 2 ^ (prefixWord ++ tailWord_955752).sum := by decide
  have hdescent : baseEnd_955752 < baseStart_955752 := by decide
  rcases family_descends (prefixWord ++ tailWord_955752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955780 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_955780 : Nat := 118140960795 + 955780 * 2 ^ 59
def prefixEnd_955780 : Nat := 4983230072969 + 3 ^ 40 * 955780 * 2
def baseEnd_955780 : Nat := 436244035515000657826181

theorem tailTrace_955780 : CollatzResearch.WordTrace tailWord_955780 prefixEnd_955780 436244035515000657826181 := by
  unfold tailWord_955780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430080238689884536684397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23240106984919846048912529 17430080238689884536684397)
  ·
    refine ⟨6536280089508706701256649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17430080238689884536684397 6536280089508706701256649)
    ·
      refine ⟨4902210067131530025942487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6536280089508706701256649 4902210067131530025942487)
      ·
        refine ⟨7353315100697295038913731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902210067131530025942487 7353315100697295038913731)
        ·
          refine ⟨11029972651045942558370597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353315100697295038913731 11029972651045942558370597)
          ·
            refine ⟨2068119872071114229694487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11029972651045942558370597 2068119872071114229694487)
            ·
              refine ⟨3102179808106671344541731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068119872071114229694487 3102179808106671344541731)
              ·
                refine ⟨4653269712160007016812597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102179808106671344541731 4653269712160007016812597)
                ·
                  refine ⟨436244035515000657826181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4653269712160007016812597 436244035515000657826181)
                  ·
                    rfl

theorem cell20_955780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_955780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955780 prefixEnd_955780 := by exact prefixLift 955780
  have htrace : WordTrace (prefixWord ++ tailWord_955780) baseStart_955780 baseEnd_955780 := by
    simpa [prefixWord, tailWord_955780, baseEnd_955780] using wordTrace_append hprefix tailTrace_955780
  have hstable : (prefixWord ++ tailWord_955780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955780).length < 2 ^ (prefixWord ++ tailWord_955780).sum := by decide
  have hdescent : baseEnd_955780 < baseStart_955780 := by decide
  rcases family_descends (prefixWord ++ tailWord_955780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955787 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_955787 : Nat := 118140960795 + 955787 * 2 ^ 59
def prefixEnd_955787 : Nat := 4983230072969 + 3 ^ 40 * 955787 * 2
def baseEnd_955787 : Nat := 436247230505739744592819

theorem tailTrace_955787 : CollatzResearch.WordTrace tailWord_955787 prefixEnd_955787 436247230505739744592819 := by
  unfold tailWord_955787
  simp only [CollatzResearch.WordTrace]
  refine ⟨34860415788354409268873615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23240277192236272845915743 34860415788354409268873615)
  ·
    refine ⟨52290623682531613903310423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34860415788354409268873615 52290623682531613903310423)
    ·
      refine ⟨78435935523797420854965635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52290623682531613903310423 78435935523797420854965635)
      ·
        refine ⟨117653903285696131282448453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78435935523797420854965635 117653903285696131282448453)
        ·
          refine ⟨22060106866068024615459085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117653903285696131282448453 22060106866068024615459085)
          ·
            refine ⟨8272540074775509230797157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22060106866068024615459085 8272540074775509230797157)
            ·
              refine ⟨1551101264020407980774467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8272540074775509230797157 1551101264020407980774467)
              ·
                refine ⟨2326651896030611971161701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551101264020407980774467 2326651896030611971161701)
                ·
                  refine ⟨436247230505739744592819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326651896030611971161701 436247230505739744592819)
                  ·
                    rfl

theorem cell20_955787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_955787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955787 prefixEnd_955787 := by exact prefixLift 955787
  have htrace : WordTrace (prefixWord ++ tailWord_955787) baseStart_955787 baseEnd_955787 := by
    simpa [prefixWord, tailWord_955787, baseEnd_955787] using wordTrace_append hprefix tailTrace_955787
  have hstable : (prefixWord ++ tailWord_955787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955787).length < 2 ^ (prefixWord ++ tailWord_955787).sum := by decide
  have hdescent : baseEnd_955787 < baseStart_955787 := by decide
  rcases family_descends (prefixWord ++ tailWord_955787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955852 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_955852 : Nat := 118140960795 + 955852 * 2 ^ 59
def prefixEnd_955852 : Nat := 4983230072969 + 3 ^ 40 * 955852 * 2
def baseEnd_955852 : Nat := 436276898276888407425887

theorem tailTrace_955852 : CollatzResearch.WordTrace tailWord_955852 prefixEnd_955852 436276898276888407425887 := by
  unfold tailWord_955852
  simp only [CollatzResearch.WordTrace]
  refine ⟨17431393266559462684994905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23241857688745950246659873 17431393266559462684994905)
  ·
    refine ⟨13073544949919597013746179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17431393266559462684994905 13073544949919597013746179)
    ·
      refine ⟨19610317424879395520619269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13073544949919597013746179 19610317424879395520619269)
      ·
        refine ⟨3676934517164886660116113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19610317424879395520619269 3676934517164886660116113)
        ·
          refine ⟨2757700887873664995087085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3676934517164886660116113 2757700887873664995087085)
          ·
            refine ⟨1034137832952624373157657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2757700887873664995087085 1034137832952624373157657)
            ·
              refine ⟨775603374714468279868243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034137832952624373157657 775603374714468279868243)
              ·
                refine ⟨1163405062071702419802365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775603374714468279868243 1163405062071702419802365)
                ·
                  refine ⟨436276898276888407425887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163405062071702419802365 436276898276888407425887)
                  ·
                    rfl

theorem cell20_955852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_955852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955852 prefixEnd_955852 := by exact prefixLift 955852
  have htrace : WordTrace (prefixWord ++ tailWord_955852) baseStart_955852 baseEnd_955852 := by
    simpa [prefixWord, tailWord_955852, baseEnd_955852] using wordTrace_append hprefix tailTrace_955852
  have hstable : (prefixWord ++ tailWord_955852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955852).length < 2 ^ (prefixWord ++ tailWord_955852).sum := by decide
  have hdescent : baseEnd_955852 < baseStart_955852 := by decide
  rcases family_descends (prefixWord ++ tailWord_955852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955880 : List Nat := [2, 1, 4, 1, 1, 2, 2, 5, 2]
def baseStart_955880 : Nat := 118140960795 + 955880 * 2 ^ 59
def prefixEnd_955880 : Nat := 4983230072969 + 3 ^ 40 * 955880 * 2
def baseEnd_955880 : Nat := 436289678239844754492439

theorem tailTrace_955880 : CollatzResearch.WordTrace tailWord_955880 prefixEnd_955880 436289678239844754492439 := by
  unfold tailWord_955880
  simp only [CollatzResearch.WordTrace]
  refine ⟨17431903888508743076004547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23242538518011657434672729 17431903888508743076004547)
  ·
    refine ⟨26147855832763114614006821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17431903888508743076004547 26147855832763114614006821)
    ·
      refine ⟨4902722968643083990126279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26147855832763114614006821 4902722968643083990126279)
      ·
        refine ⟨7354084452964625985189419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902722968643083990126279 7354084452964625985189419)
        ·
          refine ⟨11031126679446938977784129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354084452964625985189419 11031126679446938977784129)
          ·
            refine ⟨8273345009585204233338097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11031126679446938977784129 8273345009585204233338097)
            ·
              refine ⟨6205008757188903175003573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273345009585204233338097 6205008757188903175003573)
              ·
                refine ⟨581719570986459672656585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6205008757188903175003573 581719570986459672656585)
                ·
                  refine ⟨436289678239844754492439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581719570986459672656585 436289678239844754492439)
                  ·
                    rfl

theorem cell20_955880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_955880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955880 prefixEnd_955880 := by exact prefixLift 955880
  have htrace : WordTrace (prefixWord ++ tailWord_955880) baseStart_955880 baseEnd_955880 := by
    simpa [prefixWord, tailWord_955880, baseEnd_955880] using wordTrace_append hprefix tailTrace_955880
  have hstable : (prefixWord ++ tailWord_955880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955880).length < 2 ^ (prefixWord ++ tailWord_955880).sum := by decide
  have hdescent : baseEnd_955880 < baseStart_955880 := by decide
  rcases family_descends (prefixWord ++ tailWord_955880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955884 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_955884 : Nat := 118140960795 + 955884 * 2 ^ 59
def prefixEnd_955884 : Nat := 4983230072969 + 3 ^ 40 * 955884 * 2
def baseEnd_955884 : Nat := 436291503948838518359089

theorem tailTrace_955884 : CollatzResearch.WordTrace tailWord_955884 prefixEnd_955884 436291503948838518359089 := by
  unfold tailWord_955884
  simp only [CollatzResearch.WordTrace]
  refine ⟨17431976834501497417577353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23242635779335329890103137 17431976834501497417577353)
  ·
    refine ⟨13073982625876123063183015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17431976834501497417577353 13073982625876123063183015)
    ·
      refine ⟨19610973938814184594774523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13073982625876123063183015 19610973938814184594774523)
      ·
        refine ⟨29416460908221276892161785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19610973938814184594774523 29416460908221276892161785)
        ·
          refine ⟨22062345681165957669121339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29416460908221276892161785 22062345681165957669121339)
          ·
            refine ⟨33093518521748936503682009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22062345681165957669121339 33093518521748936503682009)
            ·
              refine ⟨24820138891311702377761507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33093518521748936503682009 24820138891311702377761507)
              ·
                refine ⟨37230208336967553566642261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24820138891311702377761507 37230208336967553566642261)
                ·
                  refine ⟨436291503948838518359089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37230208336967553566642261 436291503948838518359089)
                  ·
                    rfl

theorem cell20_955884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_955884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955884 prefixEnd_955884 := by exact prefixLift 955884
  have htrace : WordTrace (prefixWord ++ tailWord_955884) baseStart_955884 baseEnd_955884 := by
    simpa [prefixWord, tailWord_955884, baseEnd_955884] using wordTrace_append hprefix tailTrace_955884
  have hstable : (prefixWord ++ tailWord_955884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955884).length < 2 ^ (prefixWord ++ tailWord_955884).sum := by decide
  have hdescent : baseEnd_955884 < baseStart_955884 := by decide
  rcases family_descends (prefixWord ++ tailWord_955884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955893 : List Nat := [1, 3, 5, 1, 1, 3, 2, 2, 2]
def baseStart_955893 : Nat := 118140960795 + 955893 * 2 ^ 59
def prefixEnd_955893 : Nat := 4983230072969 + 3 ^ 40 * 955893 * 2
def baseEnd_955893 : Nat := 436295611794074487059053

theorem tailTrace_955893 : CollatzResearch.WordTrace tailWord_955893 prefixEnd_955893 436295611794074487059053 := by
  unfold tailWord_955893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34864281925970389372232333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23242854617313592914821555 34864281925970389372232333)
  ·
    refine ⟨13074105722238896014587125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34864281925970389372232333 13074105722238896014587125)
    ·
      refine ⟨1225697411459896501367543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13074105722238896014587125 1225697411459896501367543)
      ·
        refine ⟨1838546117189844752051315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225697411459896501367543 1838546117189844752051315)
        ·
          refine ⟨2757819175784767128076973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838546117189844752051315 2757819175784767128076973)
          ·
            refine ⟨1034182190919287673028865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2757819175784767128076973 1034182190919287673028865)
            ·
              refine ⟨775636643189465754771649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034182190919287673028865 775636643189465754771649)
              ·
                refine ⟨581727482392099316078737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775636643189465754771649 581727482392099316078737)
                ·
                  refine ⟨436295611794074487059053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581727482392099316078737 436295611794074487059053)
                  ·
                    rfl

theorem cell20_955893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_955893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955893 prefixEnd_955893 := by exact prefixLift 955893
  have htrace : WordTrace (prefixWord ++ tailWord_955893) baseStart_955893 baseEnd_955893 := by
    simpa [prefixWord, tailWord_955893, baseEnd_955893] using wordTrace_append hprefix tailTrace_955893
  have hstable : (prefixWord ++ tailWord_955893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955893).length < 2 ^ (prefixWord ++ tailWord_955893).sum := by decide
  have hdescent : baseEnd_955893 < baseStart_955893 := by decide
  rcases family_descends (prefixWord ++ tailWord_955893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955918 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_955918 : Nat := 118140960795 + 955918 * 2 ^ 59
def prefixEnd_955918 : Nat := 4983230072969 + 3 ^ 40 * 955918 * 2
def baseEnd_955918 : Nat := 436307022475285511225617

theorem tailTrace_955918 : CollatzResearch.WordTrace tailWord_955918 prefixEnd_955918 436307022475285511225617 := by
  unfold tailWord_955918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358149218859977330236551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23243462500586545761261605 4358149218859977330236551)
  ·
    refine ⟨6537223828289965995354827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4358149218859977330236551 6537223828289965995354827)
    ·
      refine ⟨9805835742434948993032241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6537223828289965995354827 9805835742434948993032241)
      ·
        refine ⟨7354376806826211744774181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9805835742434948993032241 7354376806826211744774181)
        ·
          refine ⟨1378945651279914702145159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7354376806826211744774181 1378945651279914702145159)
          ·
            refine ⟨2068418476919872053217739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378945651279914702145159 2068418476919872053217739)
            ·
              refine ⟨3102627715379808079826609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068418476919872053217739 3102627715379808079826609)
              ·
                refine ⟨2326970786534856059869957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102627715379808079826609 2326970786534856059869957)
                ·
                  refine ⟨436307022475285511225617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326970786534856059869957 436307022475285511225617)
                  ·
                    rfl

theorem cell20_955918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_955918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955918 prefixEnd_955918 := by exact prefixLift 955918
  have htrace : WordTrace (prefixWord ++ tailWord_955918) baseStart_955918 baseEnd_955918 := by
    simpa [prefixWord, tailWord_955918, baseEnd_955918] using wordTrace_append hprefix tailTrace_955918
  have hstable : (prefixWord ++ tailWord_955918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955918).length < 2 ^ (prefixWord ++ tailWord_955918).sum := by decide
  have hdescent : baseEnd_955918 < baseStart_955918 := by decide
  rcases family_descends (prefixWord ++ tailWord_955918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955925 : List Nat := [1, 3, 2, 1, 3, 3, 3, 4]
def baseStart_955925 : Nat := 118140960795 + 955925 * 2 ^ 59
def prefixEnd_955925 : Nat := 4983230072969 + 3 ^ 40 * 955925 * 2
def baseEnd_955925 : Nat := 145436739155341532664085

theorem tailTrace_955925 : CollatzResearch.WordTrace tailWord_955925 prefixEnd_955925 145436739155341532664085 := by
  unfold tailWord_955925
  simp only [CollatzResearch.WordTrace]
  refine ⟨34865449061854458837397229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23243632707902972558264819 34865449061854458837397229)
  ·
    refine ⟨13074543398195422064023961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34865449061854458837397229 13074543398195422064023961)
    ·
      refine ⟨9805907548646566548017971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13074543398195422064023961 9805907548646566548017971)
      ·
        refine ⟨14708861322969849822026957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805907548646566548017971 14708861322969849822026957)
        ·
          refine ⟨5515822996113693683260109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14708861322969849822026957 5515822996113693683260109)
          ·
            refine ⟨2068433623542635131222541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5515822996113693683260109 2068433623542635131222541)
            ·
              refine ⟨775662608828488174208453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2068433623542635131222541 775662608828488174208453)
              ·
                refine ⟨145436739155341532664085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775662608828488174208453 145436739155341532664085)
                ·
                  rfl

theorem cell20_955925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_955925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955925 prefixEnd_955925 := by exact prefixLift 955925
  have htrace : WordTrace (prefixWord ++ tailWord_955925) baseStart_955925 baseEnd_955925 := by
    simpa [prefixWord, tailWord_955925, baseEnd_955925] using wordTrace_append hprefix tailTrace_955925
  have hstable : (prefixWord ++ tailWord_955925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955925).length < 2 ^ (prefixWord ++ tailWord_955925).sum := by decide
  have hdescent : baseEnd_955925 < baseStart_955925 := by decide
  rcases family_descends (prefixWord ++ tailWord_955925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955946 : List Nat := [3, 1, 4, 1, 1, 1, 9]
def baseStart_955946 : Nat := 118140960795 + 955946 * 2 ^ 59
def prefixEnd_955946 : Nat := 4983230072969 + 3 ^ 40 * 955946 * 2
def baseEnd_955946 : Nat := 48479978048693539810241

theorem tailTrace_955946 : CollatzResearch.WordTrace tailWord_955946 prefixEnd_955946 48479978048693539810241 := by
  unfold tailWord_955946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8716553748694594855977923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23244143329852252949274461 8716553748694594855977923)
  ·
    refine ⟨13074830623041892283966885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8716553748694594855977923 13074830623041892283966885)
    ·
      refine ⟨2451530741820354803243791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13074830623041892283966885 2451530741820354803243791)
      ·
        refine ⟨3677296112730532204865687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451530741820354803243791 3677296112730532204865687)
        ·
          refine ⟨5515944169095798307298531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677296112730532204865687 5515944169095798307298531)
          ·
            refine ⟨8273916253643697460947797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515944169095798307298531 8273916253643697460947797)
            ·
              refine ⟨48479978048693539810241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8273916253643697460947797 48479978048693539810241)
              ·
                rfl

theorem cell20_955946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 9].length) (baseStart_955946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955946 prefixEnd_955946 := by exact prefixLift 955946
  have htrace : WordTrace (prefixWord ++ tailWord_955946) baseStart_955946 baseEnd_955946 := by
    simpa [prefixWord, tailWord_955946, baseEnd_955946] using wordTrace_append hprefix tailTrace_955946
  have hstable : (prefixWord ++ tailWord_955946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955946).length < 2 ^ (prefixWord ++ tailWord_955946).sum := by decide
  have hdescent : baseEnd_955946 < baseStart_955946 := by decide
  rcases family_descends (prefixWord ++ tailWord_955946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955991 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_955991 : Nat := 118140960795 + 955991 * 2 ^ 59
def prefixEnd_955991 : Nat := 4983230072969 + 3 ^ 40 * 955991 * 2
def baseEnd_955991 : Nat := 436340341664421701791985

theorem tailTrace_955991 : CollatzResearch.WordTrace tailWord_955991 prefixEnd_955991 436340341664421701791985 := by
  unfold tailWord_955991
  simp only [CollatzResearch.WordTrace]
  refine ⟨34867856279615352109299827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23245237519743568072866551 34867856279615352109299827)
  ·
    refine ⟨52301784419423028163949741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34867856279615352109299827 52301784419423028163949741)
    ·
      refine ⟨19613169157283635561481153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52301784419423028163949741 19613169157283635561481153)
      ·
        refine ⟨14709876867962726671110865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19613169157283635561481153 14709876867962726671110865)
        ·
          refine ⟨11032407650972045003333149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14709876867962726671110865 11032407650972045003333149)
          ·
            refine ⟨4137152869114516876249931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11032407650972045003333149 4137152869114516876249931)
            ·
              refine ⟨6205729303671775314374897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137152869114516876249931 6205729303671775314374897)
              ·
                refine ⟨4654296977753831485781173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205729303671775314374897 4654296977753831485781173)
                ·
                  refine ⟨436340341664421701791985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4654296977753831485781173 436340341664421701791985)
                  ·
                    rfl

theorem cell20_955991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_955991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955991 prefixEnd_955991 := by exact prefixLift 955991
  have htrace : WordTrace (prefixWord ++ tailWord_955991) baseStart_955991 baseEnd_955991 := by
    simpa [prefixWord, tailWord_955991, baseEnd_955991] using wordTrace_append hprefix tailTrace_955991
  have hstable : (prefixWord ++ tailWord_955991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955991).length < 2 ^ (prefixWord ++ tailWord_955991).sum := by decide
  have hdescent : baseEnd_955991 < baseStart_955991 := by decide
  rcases family_descends (prefixWord ++ tailWord_955991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955997 : List Nat := [1, 4, 4, 2, 2, 1, 6]
def baseStart_955997 : Nat := 118140960795 + 955997 * 2 ^ 59
def prefixEnd_955997 : Nat := 4983230072969 + 3 ^ 40 * 955997 * 2
def baseEnd_955997 : Nat := 48482564469768038621329

theorem tailTrace_955997 : CollatzResearch.WordTrace tailWord_955997 prefixEnd_955997 48482564469768038621329 := by
  unfold tailWord_955997
  simp only [CollatzResearch.WordTrace]
  refine ⟨34868075117593615134018245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23245383411729076756012163 34868075117593615134018245)
  ·
    refine ⟨6537764084548802837628421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34868075117593615134018245 6537764084548802837628421)
    ·
      refine ⟨1225830765852900532055329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6537764084548802837628421 1225830765852900532055329)
      ·
        refine ⟨919373074389675399041497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1225830765852900532055329 919373074389675399041497)
        ·
          refine ⟨689529805792256549281123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919373074389675399041497 689529805792256549281123)
          ·
            refine ⟨1034294708688384823921685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689529805792256549281123 1034294708688384823921685)
            ·
              refine ⟨48482564469768038621329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1034294708688384823921685 48482564469768038621329)
              ·
                rfl

theorem cell20_955997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 6].length) (baseStart_955997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_955997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_955997 prefixEnd_955997 := by exact prefixLift 955997
  have htrace : WordTrace (prefixWord ++ tailWord_955997) baseStart_955997 baseEnd_955997 := by
    simpa [prefixWord, tailWord_955997, baseEnd_955997] using wordTrace_append hprefix tailTrace_955997
  have hstable : (prefixWord ++ tailWord_955997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955997).length < 2 ^ (prefixWord ++ tailWord_955997).sum := by decide
  have hdescent : baseEnd_955997 < baseStart_955997 := by decide
  rcases family_descends (prefixWord ++ tailWord_955997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956008 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_956008 : Nat := 118140960795 + 956008 * 2 ^ 59
def prefixEnd_956008 : Nat := 4983230072969 + 3 ^ 40 * 956008 * 2
def baseEnd_956008 : Nat := 436348100927645198225249

theorem tailTrace_956008 : CollatzResearch.WordTrace tailWord_956008 prefixEnd_956008 436348100927645198225249 := by
  unfold tailWord_956008
  simp only [CollatzResearch.WordTrace]
  refine ⟨17434238160276882006334339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23245650880369176008445785 17434238160276882006334339)
  ·
    refine ⟨26151357240415323009501509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17434238160276882006334339 26151357240415323009501509)
    ·
      refine ⟨4903379482577873064281533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26151357240415323009501509 4903379482577873064281533)
      ·
        refine ⟨1838767305966702399105575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4903379482577873064281533 1838767305966702399105575)
        ·
          refine ⟨2758150958950053598658363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838767305966702399105575 2758150958950053598658363)
          ·
            refine ⟨4137226438425080397987545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758150958950053598658363 4137226438425080397987545)
            ·
              refine ⟨3102919828818810298490659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137226438425080397987545 3102919828818810298490659)
              ·
                refine ⟨4654379743228215447735989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102919828818810298490659 4654379743228215447735989)
                ·
                  refine ⟨436348100927645198225249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4654379743228215447735989 436348100927645198225249)
                  ·
                    rfl

theorem cell20_956008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_956008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956008 prefixEnd_956008 := by exact prefixLift 956008
  have htrace : WordTrace (prefixWord ++ tailWord_956008) baseStart_956008 baseEnd_956008 := by
    simpa [prefixWord, tailWord_956008, baseEnd_956008] using wordTrace_append hprefix tailTrace_956008
  have hstable : (prefixWord ++ tailWord_956008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956008).length < 2 ^ (prefixWord ++ tailWord_956008).sum := by decide
  have hdescent : baseEnd_956008 < baseStart_956008 := by decide
  rcases family_descends (prefixWord ++ tailWord_956008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956043 : List Nat := [1, 1, 1, 1, 4, 1, 3, 8]
def baseStart_956043 : Nat := 118140960795 + 956043 * 2 ^ 59
def prefixEnd_956043 : Nat := 4983230072969 + 3 ^ 40 * 956043 * 2
def baseEnd_956043 : Nat := 145454691960446877352813

theorem tailTrace_956043 : CollatzResearch.WordTrace tailWord_956043 prefixEnd_956043 145454691960446877352813 := by
  unfold tailWord_956043
  simp only [CollatzResearch.WordTrace]
  refine ⟨34869752875426964990192783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23246501916951309993461855 34869752875426964990192783)
  ·
    refine ⟨52304629313140447485289175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34869752875426964990192783 52304629313140447485289175)
    ·
      refine ⟨78456943969710671227933763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52304629313140447485289175 78456943969710671227933763)
      ·
        refine ⟨117685415954566006841900645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78456943969710671227933763 117685415954566006841900645)
        ·
          refine ⟨22066015491481126282856371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117685415954566006841900645 22066015491481126282856371)
          ·
            refine ⟨33099023237221689424284557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22066015491481126282856371 33099023237221689424284557)
            ·
              refine ⟨12412133713958133534106709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33099023237221689424284557 12412133713958133534106709)
              ·
                refine ⟨145454691960446877352813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12412133713958133534106709 145454691960446877352813)
                ·
                  rfl

theorem cell20_956043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_956043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956043 prefixEnd_956043 := by exact prefixLift 956043
  have htrace : WordTrace (prefixWord ++ tailWord_956043) baseStart_956043 baseEnd_956043 := by
    simpa [prefixWord, tailWord_956043, baseEnd_956043] using wordTrace_append hprefix tailTrace_956043
  have hstable : (prefixWord ++ tailWord_956043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956043).length < 2 ^ (prefixWord ++ tailWord_956043).sum := by decide
  have hdescent : baseEnd_956043 < baseStart_956043 := by decide
  rcases family_descends (prefixWord ++ tailWord_956043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956060 : List Nat := [2, 2, 3, 2, 3, 8]
def baseStart_956060 : Nat := 118140960795 + 956060 * 2 ^ 59
def prefixEnd_956060 : Nat := 4983230072969 + 3 ^ 40 * 956060 * 2
def baseEnd_956060 : Nat := 16161919820169041795989

theorem tailTrace_956060 : CollatzResearch.WordTrace tailWord_956060 prefixEnd_956060 16161919820169041795989 := by
  unfold tailWord_956060
  simp only [CollatzResearch.WordTrace]
  refine ⟨17435186458182688446780817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23246915277576917929041089 17435186458182688446780817)
  ·
    refine ⟨13076389843637016335085613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17435186458182688446780817 13076389843637016335085613)
    ·
      refine ⟨4903646191363881125657105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13076389843637016335085613 4903646191363881125657105)
      ·
        refine ⟨3677734643522910844242829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4903646191363881125657105 3677734643522910844242829)
        ·
          refine ⟨1379150491321091566591061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3677734643522910844242829 1379150491321091566591061)
          ·
            refine ⟨16161919820169041795989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1379150491321091566591061 16161919820169041795989)
            ·
              rfl

theorem cell20_956060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 8].length) (baseStart_956060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956060 prefixEnd_956060 := by exact prefixLift 956060
  have htrace : WordTrace (prefixWord ++ tailWord_956060) baseStart_956060 baseEnd_956060 := by
    simpa [prefixWord, tailWord_956060, baseEnd_956060] using wordTrace_append hprefix tailTrace_956060
  have hstable : (prefixWord ++ tailWord_956060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956060).length < 2 ^ (prefixWord ++ tailWord_956060).sum := by decide
  have hdescent : baseEnd_956060 < baseStart_956060 := by decide
  rcases family_descends (prefixWord ++ tailWord_956060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956066 : List Nat := [3, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_956066 : Nat := 118140960795 + 956066 * 2 ^ 59
def prefixEnd_956066 : Nat := 4983230072969 + 3 ^ 40 * 956066 * 2
def baseEnd_956066 : Nat := 436374573708054774291679

theorem tailTrace_956066 : CollatzResearch.WordTrace tailWord_956066 prefixEnd_956066 436374573708054774291679 := by
  unfold tailWord_956066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717647938585909979570013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23247061169562426612186701 8717647938585909979570013)
  ·
    refine ⟨3269117976969716242338755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8717647938585909979570013 3269117976969716242338755)
    ·
      refine ⟨4903676965454574363508133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269117976969716242338755 4903676965454574363508133)
      ·
        refine ⟨919439431022732693157775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4903676965454574363508133 919439431022732693157775)
        ·
          refine ⟨1379159146534099039736663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919439431022732693157775 1379159146534099039736663)
          ·
            refine ⟨2068738719801148559604995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379159146534099039736663 2068738719801148559604995)
            ·
              refine ⟨3103108079701722839407493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068738719801148559604995 3103108079701722839407493)
              ·
                refine ⟨581832764944073032388905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3103108079701722839407493 581832764944073032388905)
                ·
                  refine ⟨436374573708054774291679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581832764944073032388905 436374573708054774291679)
                  ·
                    rfl

theorem cell20_956066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_956066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956066 prefixEnd_956066 := by exact prefixLift 956066
  have htrace : WordTrace (prefixWord ++ tailWord_956066) baseStart_956066 baseEnd_956066 := by
    simpa [prefixWord, tailWord_956066, baseEnd_956066] using wordTrace_append hprefix tailTrace_956066
  have hstable : (prefixWord ++ tailWord_956066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956066).length < 2 ^ (prefixWord ++ tailWord_956066).sum := by decide
  have hdescent : baseEnd_956066 < baseStart_956066 := by decide
  rcases family_descends (prefixWord ++ tailWord_956066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956118 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_956118 : Nat := 118140960795 + 956118 * 2 ^ 59
def prefixEnd_956118 : Nat := 4983230072969 + 3 ^ 40 * 956118 * 2
def baseEnd_956118 : Nat := 436398307924973704558133

theorem tailTrace_956118 : CollatzResearch.WordTrace tailWord_956118 prefixEnd_956118 436398307924973704558133 := by
  unfold tailWord_956118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179530521884703299948313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23248325566770168532782005 2179530521884703299948313)
  ·
    refine ⟨1634647891413527474961235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2179530521884703299948313 1634647891413527474961235)
    ·
      refine ⟨2451971837120291212441853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634647891413527474961235 2451971837120291212441853)
      ·
        refine ⟨919489438920109204665695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2451971837120291212441853 919489438920109204665695)
        ·
          refine ⟨1379234158380163806998543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919489438920109204665695 1379234158380163806998543)
          ·
            refine ⟨2068851237570245710497815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379234158380163806998543 2068851237570245710497815)
            ·
              refine ⟨3103276856355368565746723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068851237570245710497815 3103276856355368565746723)
              ·
                refine ⟨4654915284533052848620085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103276856355368565746723 4654915284533052848620085)
                ·
                  refine ⟨436398307924973704558133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4654915284533052848620085 436398307924973704558133)
                  ·
                    rfl

theorem cell20_956118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_956118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956118 prefixEnd_956118 := by exact prefixLift 956118
  have htrace : WordTrace (prefixWord ++ tailWord_956118) baseStart_956118 baseEnd_956118 := by
    simpa [prefixWord, tailWord_956118, baseEnd_956118] using wordTrace_append hprefix tailTrace_956118
  have hstable : (prefixWord ++ tailWord_956118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956118).length < 2 ^ (prefixWord ++ tailWord_956118).sum := by decide
  have hdescent : baseEnd_956118 < baseStart_956118 := by decide
  rcases family_descends (prefixWord ++ tailWord_956118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956119 : List Nat := [1, 1, 3, 2, 1, 3, 9]
def baseStart_956119 : Nat := 118140960795 + 956119 * 2 ^ 59
def prefixEnd_956119 : Nat := 4983230072969 + 3 ^ 40 * 956119 * 2
def baseEnd_956119 : Nat := 48488751594691349502755

theorem tailTrace_956119 : CollatzResearch.WordTrace tailWord_956119 prefixEnd_956119 48488751594691349502755 := by
  unfold tailWord_956119
  simp only [CollatzResearch.WordTrace]
  refine ⟨34872524823151629969959411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23248349882101086646639607 34872524823151629969959411)
  ·
    refine ⟨52308787234727444954939117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34872524823151629969959411 52308787234727444954939117)
    ·
      refine ⟨19615795213022791858102169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52308787234727444954939117 19615795213022791858102169)
      ·
        refine ⟨14711846409767093893576627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19615795213022791858102169 14711846409767093893576627)
        ·
          refine ⟨22067769614650640840364941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14711846409767093893576627 22067769614650640840364941)
          ·
            refine ⟨8275413605493990315136853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22067769614650640840364941 8275413605493990315136853)
            ·
              refine ⟨48488751594691349502755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8275413605493990315136853 48488751594691349502755)
              ·
                rfl

theorem cell20_956119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_956119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956119 prefixEnd_956119 := by exact prefixLift 956119
  have htrace : WordTrace (prefixWord ++ tailWord_956119) baseStart_956119 baseEnd_956119 := by
    simpa [prefixWord, tailWord_956119, baseEnd_956119] using wordTrace_append hprefix tailTrace_956119
  have hstable : (prefixWord ++ tailWord_956119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956119).length < 2 ^ (prefixWord ++ tailWord_956119).sum := by decide
  have hdescent : baseEnd_956119 < baseStart_956119 := by decide
  rcases family_descends (prefixWord ++ tailWord_956119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956122 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_956122 : Nat := 118140960795 + 956122 * 2 ^ 59
def prefixEnd_956122 : Nat := 4983230072969 + 3 ^ 40 * 956122 * 2
def baseEnd_956122 : Nat := 436400133633967468424783

theorem tailTrace_956122 : CollatzResearch.WordTrace tailWord_956122 prefixEnd_956122 436400133633967468424783 := by
  unfold tailWord_956122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8718158560535190370579655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23248422828093840988212413 8718158560535190370579655)
  ·
    refine ⟨13077237840802785555869483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8718158560535190370579655 13077237840802785555869483)
    ·
      refine ⟨19615856761204178333804225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13077237840802785555869483 19615856761204178333804225)
      ·
        refine ⟨14711892570903133750353169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19615856761204178333804225 14711892570903133750353169)
        ·
          refine ⟨11033919428177350312764877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14711892570903133750353169 11033919428177350312764877)
          ·
            refine ⟨4137719785566506367286829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11033919428177350312764877 4137719785566506367286829)
            ·
              refine ⟨1551644919587439887732561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4137719785566506367286829 1551644919587439887732561)
              ·
                refine ⟨1163733689690579915799421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551644919587439887732561 1163733689690579915799421)
                ·
                  refine ⟨436400133633967468424783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163733689690579915799421 436400133633967468424783)
                  ·
                    rfl

theorem cell20_956122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_956122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956122 prefixEnd_956122 := by exact prefixLift 956122
  have htrace : WordTrace (prefixWord ++ tailWord_956122) baseStart_956122 baseEnd_956122 := by
    simpa [prefixWord, tailWord_956122, baseEnd_956122] using wordTrace_append hprefix tailTrace_956122
  have hstable : (prefixWord ++ tailWord_956122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956122).length < 2 ^ (prefixWord ++ tailWord_956122).sum := by decide
  have hdescent : baseEnd_956122 < baseStart_956122 := by decide
  rcases family_descends (prefixWord ++ tailWord_956122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956125 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 4]
def baseStart_956125 : Nat := 118140960795 + 956125 * 2 ^ 59
def prefixEnd_956125 : Nat := 4983230072969 + 3 ^ 40 * 956125 * 2
def baseEnd_956125 : Nat := 436401502915712791324771

theorem tailTrace_956125 : CollatzResearch.WordTrace tailWord_956125 prefixEnd_956125 436401502915712791324771 := by
  unfold tailWord_956125
  simp only [CollatzResearch.WordTrace]
  refine ⟨34872743661129892994677829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23248495774086595329785219 34872743661129892994677829)
  ·
    refine ⟨6538639436461854936502093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34872743661129892994677829 6538639436461854936502093)
    ·
      refine ⟨2451989788673195601188285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6538639436461854936502093 2451989788673195601188285)
      ·
        refine ⟨919496170752448350445607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2451989788673195601188285 919496170752448350445607)
        ·
          refine ⟨1379244256128672525668411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919496170752448350445607 1379244256128672525668411)
          ·
            refine ⟨2068866384193008788502617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379244256128672525668411 2068866384193008788502617)
            ·
              refine ⟨1551649788144756591376963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068866384193008788502617 1551649788144756591376963)
              ·
                refine ⟨2327474682217134887065445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551649788144756591376963 2327474682217134887065445)
                ·
                  refine ⟨436401502915712791324771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2327474682217134887065445 436401502915712791324771)
                  ·
                    rfl

theorem cell20_956125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_956125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956125 prefixEnd_956125 := by exact prefixLift 956125
  have htrace : WordTrace (prefixWord ++ tailWord_956125) baseStart_956125 baseEnd_956125 := by
    simpa [prefixWord, tailWord_956125, baseEnd_956125] using wordTrace_append hprefix tailTrace_956125
  have hstable : (prefixWord ++ tailWord_956125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956125).length < 2 ^ (prefixWord ++ tailWord_956125).sum := by decide
  have hdescent : baseEnd_956125 < baseStart_956125 := by decide
  rcases family_descends (prefixWord ++ tailWord_956125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956181 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_956181 : Nat := 118140960795 + 956181 * 2 ^ 59
def prefixEnd_956181 : Nat := 4983230072969 + 3 ^ 40 * 956181 * 2
def baseEnd_956181 : Nat := 436427062841625485457875

theorem tailTrace_956181 : CollatzResearch.WordTrace tailWord_956181 prefixEnd_956181 436427062841625485457875 := by
  unfold tailWord_956181
  simp only [CollatzResearch.WordTrace]
  refine ⟨34874786148927014558716397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23249857432618009705810931 34874786148927014558716397)
  ·
    refine ⟨13078044805847630459518649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34874786148927014558716397 13078044805847630459518649)
    ·
      refine ⟨9808533604385722844638987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13078044805847630459518649 9808533604385722844638987)
      ·
        refine ⟨14712800406578584266958481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9808533604385722844638987 14712800406578584266958481)
        ·
          refine ⟨11034600304933938200218861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14712800406578584266958481 11034600304933938200218861)
          ·
            refine ⟨4137975114350226825082073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11034600304933938200218861 4137975114350226825082073)
            ·
              refine ⟨3103481335762670118811555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137975114350226825082073 3103481335762670118811555)
              ·
                refine ⟨4655222003644005178217333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103481335762670118811555 4655222003644005178217333)
                ·
                  refine ⟨436427062841625485457875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4655222003644005178217333 436427062841625485457875)
                  ·
                    rfl

theorem cell20_956181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_956181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956181 prefixEnd_956181 := by exact prefixLift 956181
  have htrace : WordTrace (prefixWord ++ tailWord_956181) baseStart_956181 baseEnd_956181 := by
    simpa [prefixWord, tailWord_956181, baseEnd_956181] using wordTrace_append hprefix tailTrace_956181
  have hstable : (prefixWord ++ tailWord_956181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956181).length < 2 ^ (prefixWord ++ tailWord_956181).sum := by decide
  have hdescent : baseEnd_956181 < baseStart_956181 := by decide
  rcases family_descends (prefixWord ++ tailWord_956181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956190 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_956190 : Nat := 118140960795 + 956190 * 2 ^ 59
def prefixEnd_956190 : Nat := 4983230072969 + 3 ^ 40 * 956190 * 2
def baseEnd_956190 : Nat := 436431170686861454157839

theorem tailTrace_956190 : CollatzResearch.WordTrace tailWord_956190 prefixEnd_956190 436431170686861454157839 := by
  unfold tailWord_956190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4359389300736801136974253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23250076270596272730529349 4359389300736801136974253)
  ·
    refine ⟨1634770987776300426365345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4359389300736801136974253 1634770987776300426365345)
    ·
      refine ⟨1226078240832225319774009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1634770987776300426365345 1226078240832225319774009)
      ·
        refine ⟨919558680624168989830507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1226078240832225319774009 919558680624168989830507)
        ·
          refine ⟨1379338020936253484745761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919558680624168989830507 1379338020936253484745761)
          ·
            refine ⟨1034503515702190113559321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1379338020936253484745761 1034503515702190113559321)
            ·
              refine ⟨775877636776642585169491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034503515702190113559321 775877636776642585169491)
              ·
                refine ⟨1163816455164963877754237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775877636776642585169491 1163816455164963877754237)
                ·
                  refine ⟨436431170686861454157839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163816455164963877754237 436431170686861454157839)
                  ·
                    rfl

theorem cell20_956190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_956190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956190 prefixEnd_956190 := by exact prefixLift 956190
  have htrace : WordTrace (prefixWord ++ tailWord_956190) baseStart_956190 baseEnd_956190 := by
    simpa [prefixWord, tailWord_956190, baseEnd_956190] using wordTrace_append hprefix tailTrace_956190
  have hstable : (prefixWord ++ tailWord_956190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956190).length < 2 ^ (prefixWord ++ tailWord_956190).sum := by decide
  have hdescent : baseEnd_956190 < baseStart_956190 := by decide
  rcases family_descends (prefixWord ++ tailWord_956190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956195 : List Nat := [1, 1, 1, 4, 2, 1, 3, 7]
def baseStart_956195 : Nat := 118140960795 + 956195 * 2 ^ 59
def prefixEnd_956195 : Nat := 4983230072969 + 3 ^ 40 * 956195 * 2
def baseEnd_956195 : Nat := 145477817607701219663717

theorem tailTrace_956195 : CollatzResearch.WordTrace tailWord_956195 prefixEnd_956195 145477817607701219663717 := by
  unfold tailWord_956195
  simp only [CollatzResearch.WordTrace]
  refine ⟨34875296770876294949726039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23250197847250863299817359 34875296770876294949726039)
  ·
    refine ⟨52312945156314442424589059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34875296770876294949726039 52312945156314442424589059)
    ·
      refine ⟨78469417734471663636883589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52312945156314442424589059 78469417734471663636883589)
      ·
        refine ⟨14713015825213436931915673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78469417734471663636883589 14713015825213436931915673)
        ·
          refine ⟨11034761868910077698936755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14713015825213436931915673 11034761868910077698936755)
          ·
            refine ⟨16552142803365116548405133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11034761868910077698936755 16552142803365116548405133)
            ·
              refine ⟨6207053551261918705651925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16552142803365116548405133 6207053551261918705651925)
              ·
                refine ⟨145477817607701219663717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6207053551261918705651925 145477817607701219663717)
                ·
                  rfl

theorem cell20_956195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_956195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956195 prefixEnd_956195 := by exact prefixLift 956195
  have htrace : WordTrace (prefixWord ++ tailWord_956195) baseStart_956195 baseEnd_956195 := by
    simpa [prefixWord, tailWord_956195, baseEnd_956195] using wordTrace_append hprefix tailTrace_956195
  have hstable : (prefixWord ++ tailWord_956195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956195).length < 2 ^ (prefixWord ++ tailWord_956195).sum := by decide
  have hdescent : baseEnd_956195 < baseStart_956195 := by decide
  rcases family_descends (prefixWord ++ tailWord_956195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956257 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 3]
def baseStart_956257 : Nat := 118140960795 + 956257 * 2 ^ 59
def prefixEnd_956257 : Nat := 4983230072969 + 3 ^ 40 * 956257 * 2
def baseEnd_956257 : Nat := 436461751312506998924231

theorem tailTrace_956257 : CollatzResearch.WordTrace tailWord_956257 prefixEnd_956257 436461751312506998924231 := by
  unfold tailWord_956257
  simp only [CollatzResearch.WordTrace]
  refine ⟨34877558096651679538483025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23251705397767786358988683 34877558096651679538483025)
  ·
    refine ⟨26158168572488759653862269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34877558096651679538483025 26158168572488759653862269)
    ·
      refine ⟨9809313214683284870198351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26158168572488759653862269 9809313214683284870198351)
      ·
        refine ⟨14713969822024927305297527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9809313214683284870198351 14713969822024927305297527)
        ·
          refine ⟨22070954733037390957946291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14713969822024927305297527 22070954733037390957946291)
          ·
            refine ⟨33106432099556086436919437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22070954733037390957946291 33106432099556086436919437)
            ·
              refine ⟨12414912037333532413844789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33106432099556086436919437 12414912037333532413844789)
              ·
                refine ⟨1163898003500018663797949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12414912037333532413844789 1163898003500018663797949)
                ·
                  refine ⟨436461751312506998924231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163898003500018663797949 436461751312506998924231)
                  ·
                    rfl

theorem cell20_956257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_956257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_956257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_956257 prefixEnd_956257 := by exact prefixLift 956257
  have htrace : WordTrace (prefixWord ++ tailWord_956257) baseStart_956257 baseEnd_956257 := by
    simpa [prefixWord, tailWord_956257, baseEnd_956257] using wordTrace_append hprefix tailTrace_956257
  have hstable : (prefixWord ++ tailWord_956257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956257).length < 2 ^ (prefixWord ++ tailWord_956257).sum := by decide
  have hdescent : baseEnd_956257 < baseStart_956257 := by decide
  rcases family_descends (prefixWord ++ tailWord_956257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
