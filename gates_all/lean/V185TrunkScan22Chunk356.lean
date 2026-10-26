import V185TrunkScan22Chunk355

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3176535 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 1, 4]
def baseStart_3176535 : Nat := 118140960795 + 3176535 * 2 ^ 59
def prefixEnd_3176535 : Nat := 4983230072969 + 3 ^ 40 * 3176535 * 2
def baseEnd_3176535 : Nat := 1087392847219889683935925

theorem tailTrace_3176535 : CollatzResearch.WordTrace tailWord_3176535 prefixEnd_3176535 1087392847219889683935925 := by
  unfold tailWord_3176535
  simp only [CollatzResearch.WordTrace]
  refine ⟨115857749546963678831763059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77238499697975785887842039 115857749546963678831763059)
  ·
    refine ⟨173786624320445518247644589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115857749546963678831763059 173786624320445518247644589)
    ·
      refine ⟨65169984120167069342866721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173786624320445518247644589 65169984120167069342866721)
      ·
        refine ⟨48877488090125302007150041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65169984120167069342866721 48877488090125302007150041)
        ·
          refine ⟨36658116067593976505362531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48877488090125302007150041 36658116067593976505362531)
          ·
            refine ⟨54987174101390964758043797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36658116067593976505362531 54987174101390964758043797)
            ·
              refine ⟨2577523786002701473033303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54987174101390964758043797 2577523786002701473033303)
              ·
                refine ⟨3866285679004052209549955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577523786002701473033303 3866285679004052209549955)
                ·
                  refine ⟨5799428518506078314324933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866285679004052209549955 5799428518506078314324933)
                  ·
                    refine ⟨1087392847219889683935925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5799428518506078314324933 1087392847219889683935925)
                    ·
                      rfl

theorem cell22_3176535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_3176535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176535 prefixEnd_3176535 := by exact prefixLift 3176535
  have htrace : WordTrace (prefixWord ++ tailWord_3176535) baseStart_3176535 baseEnd_3176535 := by
    simpa [prefixWord, tailWord_3176535, baseEnd_3176535] using wordTrace_append hprefix tailTrace_3176535
  have hstable : (prefixWord ++ tailWord_3176535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176535).length < 2 ^ (prefixWord ++ tailWord_3176535).sum := by decide
  have hdescent : baseEnd_3176535 < baseStart_3176535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176561 : List Nat := [1, 2, 2, 2, 1, 1, 4, 9]
def baseStart_3176561 : Nat := 118140960795 + 3176561 * 2 ^ 59
def prefixEnd_3176561 : Nat := 4983230072969 + 3 ^ 40 * 3176561 * 2
def baseEnd_3176561 : Nat := 120822416394581586976205

theorem tailTrace_3176561 : CollatzResearch.WordTrace tailWord_3176561 prefixEnd_3176561 120822416394581586976205 := by
  unfold tailWord_3176561
  simp only [CollatzResearch.WordTrace]
  refine ⟨115858697844869485272209537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77239131896579656848139691 115858697844869485272209537)
  ·
    refine ⟨86894023383652113954157153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115858697844869485272209537 86894023383652113954157153)
    ·
      refine ⟨65170517537739085465617865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86894023383652113954157153 65170517537739085465617865)
      ·
        refine ⟨48877888153304314099213399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65170517537739085465617865 48877888153304314099213399)
        ·
          refine ⟨73316832229956471148820099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48877888153304314099213399 73316832229956471148820099)
          ·
            refine ⟨109975248344934706723230149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73316832229956471148820099 109975248344934706723230149)
            ·
              refine ⟨20620359064675257510605653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109975248344934706723230149 20620359064675257510605653)
              ·
                refine ⟨120822416394581586976205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20620359064675257510605653 120822416394581586976205)
                ·
                  rfl

theorem cell22_3176561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 9].length) (baseStart_3176561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176561 prefixEnd_3176561 := by exact prefixLift 3176561
  have htrace : WordTrace (prefixWord ++ tailWord_3176561) baseStart_3176561 baseEnd_3176561 := by
    simpa [prefixWord, tailWord_3176561, baseEnd_3176561] using wordTrace_append hprefix tailTrace_3176561
  have hstable : (prefixWord ++ tailWord_3176561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176561).length < 2 ^ (prefixWord ++ tailWord_3176561).sum := by decide
  have hdescent : baseEnd_3176561 < baseStart_3176561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176576 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_3176576 : Nat := 118140960795 + 3176576 * 2 ^ 59
def prefixEnd_3176576 : Nat := 4983230072969 + 3 ^ 40 * 3176576 * 2
def baseEnd_3176576 : Nat := 1087406882357779243660799

theorem tailTrace_3176576 : CollatzResearch.WordTrace tailWord_3176576 prefixEnd_3176576 1087406882357779243660799 := by
  unfold tailWord_3176576
  simp only [CollatzResearch.WordTrace]
  refine ⟨57929622469907571417002791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77239496626543428556003721 57929622469907571417002791)
  ·
    refine ⟨86894433704861357125504187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57929622469907571417002791 86894433704861357125504187)
    ·
      refine ⟨130341650557292035688256281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86894433704861357125504187 130341650557292035688256281)
      ·
        refine ⟨97756237917969026766192211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130341650557292035688256281 97756237917969026766192211)
        ·
          refine ⟨146634356876953540149288317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97756237917969026766192211 146634356876953540149288317)
          ·
            refine ⟨54987883828857577555983119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146634356876953540149288317 54987883828857577555983119)
            ·
              refine ⟨82481825743286366333974679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54987883828857577555983119 82481825743286366333974679)
              ·
                refine ⟨123722738614929549500962019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82481825743286366333974679 123722738614929549500962019)
                ·
                  refine ⟨185584107922394324251443029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123722738614929549500962019 185584107922394324251443029)
                  ·
                    refine ⟨1087406882357779243660799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 185584107922394324251443029 1087406882357779243660799)
                    ·
                      rfl

theorem cell22_3176576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_3176576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176576 prefixEnd_3176576 := by exact prefixLift 3176576
  have htrace : WordTrace (prefixWord ++ tailWord_3176576) baseStart_3176576 baseEnd_3176576 := by
    simpa [prefixWord, tailWord_3176576, baseEnd_3176576] using wordTrace_append hprefix tailTrace_3176576
  have hstable : (prefixWord ++ tailWord_3176576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176576).length < 2 ^ (prefixWord ++ tailWord_3176576).sum := by decide
  have hdescent : baseEnd_3176576 < baseStart_3176576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176700 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_3176700 : Nat := 118140960795 + 3176700 * 2 ^ 59
def prefixEnd_3176700 : Nat := 4983230072969 + 3 ^ 40 * 3176700 * 2
def baseEnd_3176700 : Nat := 1087449330091884253560419

theorem tailTrace_3176700 : CollatzResearch.WordTrace tailWord_3176700 prefixEnd_3176700 1087449330091884253560419 := by
  unfold tailWord_3176700
  simp only [CollatzResearch.WordTrace]
  refine ⟨57931883795682956005759777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77242511727577274674346369 57931883795682956005759777)
  ·
    refine ⟨43448912846762217004319833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57931883795682956005759777 43448912846762217004319833)
    ·
      refine ⟨32586684635071662753239875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43448912846762217004319833 32586684635071662753239875)
      ·
        refine ⟨48880026952607494129859813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32586684635071662753239875 48880026952607494129859813)
        ·
          refine ⟨9165005053613905149348715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48880026952607494129859813 9165005053613905149348715)
          ·
            refine ⟨13747507580420857724023073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9165005053613905149348715 13747507580420857724023073)
            ·
              refine ⟨10310630685315643293017305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13747507580420857724023073 10310630685315643293017305)
              ·
                refine ⟨7732973013986732469762979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10310630685315643293017305 7732973013986732469762979)
                ·
                  refine ⟨11599459520980098704644469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7732973013986732469762979 11599459520980098704644469)
                  ·
                    refine ⟨1087449330091884253560419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11599459520980098704644469 1087449330091884253560419)
                    ·
                      rfl

theorem cell22_3176700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_3176700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176700 prefixEnd_3176700 := by exact prefixLift 3176700
  have htrace : WordTrace (prefixWord ++ tailWord_3176700) baseStart_3176700 baseEnd_3176700 := by
    simpa [prefixWord, tailWord_3176700, baseEnd_3176700] using wordTrace_append hprefix tailTrace_3176700
  have hstable : (prefixWord ++ tailWord_3176700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176700).length < 2 ^ (prefixWord ++ tailWord_3176700).sum := by decide
  have hdescent : baseEnd_3176700 < baseStart_3176700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176713 : List Nat := [1, 2, 1, 1, 3, 5, 9]
def baseStart_3176713 : Nat := 118140960795 + 3176713 * 2 ^ 59
def prefixEnd_3176713 : Nat := 4983230072969 + 3 ^ 40 * 3176713 * 2
def baseEnd_3176713 : Nat := 40276065935465057517977

theorem tailTrace_3176713 : CollatzResearch.WordTrace tailWord_3176713 prefixEnd_3176713 40276065935465057517977 := by
  unfold tailWord_3176713
  simp only [CollatzResearch.WordTrace]
  refine ⟨115864241740318815231742793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77242827826879210154495195 115864241740318815231742793)
  ·
    refine ⟨86898181305239111423807095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115864241740318815231742793 86898181305239111423807095)
    ·
      refine ⟨130347271957858667135710643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86898181305239111423807095 130347271957858667135710643)
      ·
        refine ⟨195520907936788000703565965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130347271957858667135710643 195520907936788000703565965)
        ·
          refine ⟨73320340476295500263837237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195520907936788000703565965 73320340476295500263837237)
          ·
            refine ⟨6873781919652703149734741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73320340476295500263837237 6873781919652703149734741)
            ·
              refine ⟨40276065935465057517977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6873781919652703149734741 40276065935465057517977)
              ·
                rfl

theorem cell22_3176713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 9].length) (baseStart_3176713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176713 prefixEnd_3176713 := by exact prefixLift 3176713
  have htrace : WordTrace (prefixWord ++ tailWord_3176713) baseStart_3176713 baseEnd_3176713 := by
    simpa [prefixWord, tailWord_3176713, baseEnd_3176713] using wordTrace_append hprefix tailTrace_3176713
  have hstable : (prefixWord ++ tailWord_3176713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176713).length < 2 ^ (prefixWord ++ tailWord_3176713).sum := by decide
  have hdescent : baseEnd_3176713 < baseStart_3176713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176734 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3176734 : Nat := 118140960795 + 3176734 * 2 ^ 59
def prefixEnd_3176734 : Nat := 4983230072969 + 3 ^ 40 * 3176734 * 2
def baseEnd_3176734 : Nat := 1087460968986719498210315

theorem tailTrace_3176734 : CollatzResearch.WordTrace tailWord_3176734 prefixEnd_3176734 1087460968986719498210315 := by
  unfold tailWord_3176734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14483125959155341977282157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77243338448828490545504837 14483125959155341977282157)
  ·
    refine ⟨5431172234683253241480809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14483125959155341977282157 5431172234683253241480809)
    ·
      refine ⟨4073379176012439931110607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5431172234683253241480809 4073379176012439931110607)
      ·
        refine ⟨6110068764018659896665911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073379176012439931110607 6110068764018659896665911)
        ·
          refine ⟨9165103146027989844998867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6110068764018659896665911 9165103146027989844998867)
          ·
            refine ⟨13747654719041984767498301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9165103146027989844998867 13747654719041984767498301)
            ·
              refine ⟨5155370519640744287811863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13747654719041984767498301 5155370519640744287811863)
              ·
                refine ⟨7733055779461116431717795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155370519640744287811863 7733055779461116431717795)
                ·
                  refine ⟨11599583669191674647576693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7733055779461116431717795 11599583669191674647576693)
                  ·
                    refine ⟨1087460968986719498210315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11599583669191674647576693 1087460968986719498210315)
                    ·
                      rfl

theorem cell22_3176734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3176734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176734 prefixEnd_3176734 := by exact prefixLift 3176734
  have htrace : WordTrace (prefixWord ++ tailWord_3176734) baseStart_3176734 baseEnd_3176734 := by
    simpa [prefixWord, tailWord_3176734, baseEnd_3176734] using wordTrace_append hprefix tailTrace_3176734
  have hstable : (prefixWord ++ tailWord_3176734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176734).length < 2 ^ (prefixWord ++ tailWord_3176734).sum := by decide
  have hdescent : baseEnd_3176734 < baseStart_3176734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176775 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 5]
def baseStart_3176775 : Nat := 118140960795 + 3176775 * 2 ^ 59
def prefixEnd_3176775 : Nat := 4983230072969 + 3 ^ 40 * 3176775 * 2
def baseEnd_3176775 : Nat := 362491668041536352645063

theorem tailTrace_3176775 : CollatzResearch.WordTrace tailWord_3176775 prefixEnd_3176775 362491668041536352645063 := by
  unfold tailWord_3176775
  simp only [CollatzResearch.WordTrace]
  refine ⟨115866503066094199820499779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77244335377396133213666519 115866503066094199820499779)
  ·
    refine ⟨173799754599141299730749669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115866503066094199820499779 173799754599141299730749669)
    ·
      refine ⟨32587453987338993699515563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173799754599141299730749669 32587453987338993699515563)
      ·
        refine ⟨48881180981008490549273345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32587453987338993699515563 48881180981008490549273345)
        ·
          refine ⟨36660885735756367911955009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48881180981008490549273345 36660885735756367911955009)
          ·
            refine ⟨27495664301817275933966257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36660885735756367911955009 27495664301817275933966257)
            ·
              refine ⟨20621748226362956950474693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27495664301817275933966257 20621748226362956950474693)
              ·
                refine ⟨3866577792443054428214005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20621748226362956950474693 3866577792443054428214005)
                ·
                  refine ⟨362491668041536352645063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3866577792443054428214005 362491668041536352645063)
                  ·
                    rfl

theorem cell22_3176775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 5].length) (baseStart_3176775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176775 prefixEnd_3176775 := by exact prefixLift 3176775
  have htrace : WordTrace (prefixWord ++ tailWord_3176775) baseStart_3176775 baseEnd_3176775 := by
    simpa [prefixWord, tailWord_3176775, baseEnd_3176775] using wordTrace_append hprefix tailTrace_3176775
  have hstable : (prefixWord ++ tailWord_3176775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176775).length < 2 ^ (prefixWord ++ tailWord_3176775).sum := by decide
  have hdescent : baseEnd_3176775 < baseStart_3176775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176867 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 2, 4]
def baseStart_3176867 : Nat := 118140960795 + 3176867 * 2 ^ 59
def prefixEnd_3176867 : Nat := 4983230072969 + 3 ^ 40 * 3176867 * 2
def baseEnd_3176867 : Nat := 1087506497604751484634907

theorem tailTrace_3176867 : CollatzResearch.WordTrace tailWord_3176867 prefixEnd_3176867 1087506497604751484634907 := by
  unfold tailWord_3176867
  simp only [CollatzResearch.WordTrace]
  refine ⟨115869858581760899532848855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77246572387840599688565903 115869858581760899532848855)
  ·
    refine ⟨173804787872641349299273283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115869858581760899532848855 173804787872641349299273283)
    ·
      refine ⟨260707181808962023948909925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173804787872641349299273283 260707181808962023948909925)
      ·
        refine ⟨48882596589180379490420611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260707181808962023948909925 48882596589180379490420611)
        ·
          refine ⟨73323894883770569235630917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48882596589180379490420611 73323894883770569235630917)
          ·
            refine ⟨13748230290706981731680797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73323894883770569235630917 13748230290706981731680797)
            ·
              refine ⟨5155586359015118149380299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13748230290706981731680797 5155586359015118149380299)
              ·
                refine ⟨7733379538522677224070449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155586359015118149380299 7733379538522677224070449)
                ·
                  refine ⟨5800034653892007918052837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7733379538522677224070449 5800034653892007918052837)
                  ·
                    refine ⟨1087506497604751484634907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5800034653892007918052837 1087506497604751484634907)
                    ·
                      rfl

theorem cell22_3176867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4].length) (baseStart_3176867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176867 prefixEnd_3176867 := by exact prefixLift 3176867
  have htrace : WordTrace (prefixWord ++ tailWord_3176867) baseStart_3176867 baseEnd_3176867 := by
    simpa [prefixWord, tailWord_3176867, baseEnd_3176867] using wordTrace_append hprefix tailTrace_3176867
  have hstable : (prefixWord ++ tailWord_3176867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176867).length < 2 ^ (prefixWord ++ tailWord_3176867).sum := by decide
  have hdescent : baseEnd_3176867 < baseStart_3176867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176957 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_3176957 : Nat := 118140960795 + 3176957 * 2 ^ 59
def prefixEnd_3176957 : Nat := 4983230072969 + 3 ^ 40 * 3176957 * 2
def baseEnd_3176957 : Nat := 1087537306444021249884631

theorem tailTrace_3176957 : CollatzResearch.WordTrace tailWord_3176957 prefixEnd_3176957 1087537306444021249884631 := by
  unfold tailWord_3176957
  simp only [CollatzResearch.WordTrace]
  refine ⟨115873141151434844903625125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77248760767623229935750083 115873141151434844903625125)
  ·
    refine ⟨21726213965894033419429711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115873141151434844903625125 21726213965894033419429711)
    ·
      refine ⟨32589320948841050129144567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21726213965894033419429711 32589320948841050129144567)
      ·
        refine ⟨48883981423261575193716851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32589320948841050129144567 48883981423261575193716851)
        ·
          refine ⟨73325972134892362790575277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48883981423261575193716851 73325972134892362790575277)
          ·
            refine ⟨27497239550584636046465729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73325972134892362790575277 27497239550584636046465729)
            ·
              refine ⟨20622929662938477034849297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27497239550584636046465729 20622929662938477034849297)
              ·
                refine ⟨15467197247203857776136973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20622929662938477034849297 15467197247203857776136973)
                ·
                  refine ⟨5800198967701446666051365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15467197247203857776136973 5800198967701446666051365)
                  ·
                    refine ⟨1087537306444021249884631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5800198967701446666051365 1087537306444021249884631)
                    ·
                      rfl

theorem cell22_3176957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_3176957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176957 prefixEnd_3176957 := by exact prefixLift 3176957
  have htrace : WordTrace (prefixWord ++ tailWord_3176957) baseStart_3176957 baseEnd_3176957 := by
    simpa [prefixWord, tailWord_3176957, baseEnd_3176957] using wordTrace_append hprefix tailTrace_3176957
  have hstable : (prefixWord ++ tailWord_3176957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176957).length < 2 ^ (prefixWord ++ tailWord_3176957).sum := by decide
  have hdescent : baseEnd_3176957 < baseStart_3176957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176961 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 5]
def baseStart_3176961 : Nat := 118140960795 + 3176961 * 2 ^ 59
def prefixEnd_3176961 : Nat := 4983230072969 + 3 ^ 40 * 3176961 * 2
def baseEnd_3176961 : Nat := 362512891908588857594873

theorem tailTrace_3176961 : CollatzResearch.WordTrace tailWord_3176961 prefixEnd_3176961 362512891908588857594873 := by
  unfold tailWord_3176961
  simp only [CollatzResearch.WordTrace]
  refine ⟨115873287043420353586770737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77248858028946902391180491 115873287043420353586770737)
  ·
    refine ⟨86904965282565265190078053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115873287043420353586770737 86904965282565265190078053)
    ·
      refine ⟨16294680990480987223139635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86904965282565265190078053 16294680990480987223139635)
      ·
        refine ⟨24442021485721480834709453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16294680990480987223139635 24442021485721480834709453)
        ·
          refine ⟨9165758057145555313016045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24442021485721480834709453 9165758057145555313016045)
          ·
            refine ⟨3437159271429583242381017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9165758057145555313016045 3437159271429583242381017)
            ·
              refine ⟨2577869453572187431785763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437159271429583242381017 2577869453572187431785763)
              ·
                refine ⟨3866804180358281147678645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577869453572187431785763 3866804180358281147678645)
                ·
                  refine ⟨362512891908588857594873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3866804180358281147678645 362512891908588857594873)
                  ·
                    rfl

theorem cell22_3176961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_3176961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176961 prefixEnd_3176961 := by exact prefixLift 3176961
  have htrace : WordTrace (prefixWord ++ tailWord_3176961) baseStart_3176961 baseEnd_3176961 := by
    simpa [prefixWord, tailWord_3176961, baseEnd_3176961] using wordTrace_append hprefix tailTrace_3176961
  have hstable : (prefixWord ++ tailWord_3176961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176961).length < 2 ^ (prefixWord ++ tailWord_3176961).sum := by decide
  have hdescent : baseEnd_3176961 < baseStart_3176961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176974 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3176974 : Nat := 118140960795 + 3176974 * 2 ^ 59
def prefixEnd_3176974 : Nat := 4983230072969 + 3 ^ 40 * 3176974 * 2
def baseEnd_3176974 : Nat := 1087543125891438872209579

theorem tailTrace_3176974 : CollatzResearch.WordTrace tailWord_3176974 prefixEnd_3176974 1087543125891438872209579 := by
  unfold tailWord_3176974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484220149046657100874247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77249174128248837871329317 14484220149046657100874247)
  ·
    refine ⟨21726330223569985651311371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14484220149046657100874247 21726330223569985651311371)
    ·
      refine ⟨32589495335354978476967057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21726330223569985651311371 32589495335354978476967057)
      ·
        refine ⟨24442121501516233857725293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32589495335354978476967057 24442121501516233857725293)
        ·
          refine ⟨9165795563068587696646985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24442121501516233857725293 9165795563068587696646985)
          ·
            refine ⟨6874346672301440772485239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9165795563068587696646985 6874346672301440772485239)
            ·
              refine ⟨10311520008452161158727859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874346672301440772485239 10311520008452161158727859)
              ·
                refine ⟨15467280012678241738091789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311520008452161158727859 15467280012678241738091789)
                ·
                  refine ⟨5800230004754340651784421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15467280012678241738091789 5800230004754340651784421)
                  ·
                    refine ⟨1087543125891438872209579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5800230004754340651784421 1087543125891438872209579)
                    ·
                      rfl

theorem cell22_3176974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3176974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176974 prefixEnd_3176974 := by exact prefixLift 3176974
  have htrace : WordTrace (prefixWord ++ tailWord_3176974) baseStart_3176974 baseEnd_3176974 := by
    simpa [prefixWord, tailWord_3176974, baseEnd_3176974] using wordTrace_append hprefix tailTrace_3176974
  have hstable : (prefixWord ++ tailWord_3176974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176974).length < 2 ^ (prefixWord ++ tailWord_3176974).sum := by decide
  have hdescent : baseEnd_3176974 < baseStart_3176974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3176999 : List Nat := [1, 1, 7, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3176999 : Nat := 118140960795 + 3176999 * 2 ^ 59
def prefixEnd_3176999 : Nat := 4983230072969 + 3 ^ 40 * 3176999 * 2
def baseEnd_3176999 : Nat := 1087551683902347140334503

theorem tailTrace_3176999 : CollatzResearch.WordTrace tailWord_3176999 prefixEnd_3176999 1087551683902347140334503 := by
  unfold tailWord_3176999
  simp only [CollatzResearch.WordTrace]
  refine ⟨115874673017282686076654051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77249782011521790717769367 115874673017282686076654051)
  ·
    refine ⟨173812009525924029114981077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115874673017282686076654051 173812009525924029114981077)
    ·
      refine ⟨4073718973263844432382369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 173812009525924029114981077 4073718973263844432382369)
      ·
        refine ⟨3055289229947883324286777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4073718973263844432382369 3055289229947883324286777)
        ·
          refine ⟨2291466922460912493215083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055289229947883324286777 2291466922460912493215083)
          ·
            refine ⟨3437200383691368739822625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291466922460912493215083 3437200383691368739822625)
            ·
              refine ⟨2577900287768526554866969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437200383691368739822625 2577900287768526554866969)
              ·
                refine ⟨1933425215826394916150227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577900287768526554866969 1933425215826394916150227)
                ·
                  refine ⟨2900137823739592374225341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933425215826394916150227 2900137823739592374225341)
                  ·
                    refine ⟨1087551683902347140334503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900137823739592374225341 1087551683902347140334503)
                    ·
                      rfl

theorem cell22_3176999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3176999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3176999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3176999 prefixEnd_3176999 := by exact prefixLift 3176999
  have htrace : WordTrace (prefixWord ++ tailWord_3176999) baseStart_3176999 baseEnd_3176999 := by
    simpa [prefixWord, tailWord_3176999, baseEnd_3176999] using wordTrace_append hprefix tailTrace_3176999
  have hstable : (prefixWord ++ tailWord_3176999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3176999).length < 2 ^ (prefixWord ++ tailWord_3176999).sum := by decide
  have hdescent : baseEnd_3176999 < baseStart_3176999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3176999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177021 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_3177021 : Nat := 118140960795 + 3177021 * 2 ^ 59
def prefixEnd_3177021 : Nat := 4983230072969 + 3 ^ 40 * 3177021 * 2
def baseEnd_3177021 : Nat := 1087559214951946416284435

theorem tailTrace_3177021 : CollatzResearch.WordTrace tailWord_3177021 prefixEnd_3177021 1087559214951946416284435 := by
  unfold tailWord_3177021
  simp only [CollatzResearch.WordTrace]
  refine ⟨115875475423202983833954917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77250316948801989222636611 115875475423202983833954917)
  ·
    refine ⟨21726651641850559468866547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115875475423202983833954917 21726651641850559468866547)
    ·
      refine ⟨32589977462775839203299821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21726651641850559468866547 32589977462775839203299821)
      ·
        refine ⟨12221241548540939701237433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32589977462775839203299821 12221241548540939701237433)
        ·
          refine ⟨9165931161405704775928075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12221241548540939701237433 9165931161405704775928075)
          ·
            refine ⟨13748896742108557163892113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9165931161405704775928075 13748896742108557163892113)
            ·
              refine ⟨10311672556581417872919085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13748896742108557163892113 10311672556581417872919085)
              ·
                refine ⟨3866877208718031702344657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10311672556581417872919085 3866877208718031702344657)
                ·
                  refine ⟨2900157906538523776758493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3866877208718031702344657 2900157906538523776758493)
                  ·
                    refine ⟨1087559214951946416284435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900157906538523776758493 1087559214951946416284435)
                    ·
                      rfl

theorem cell22_3177021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_3177021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177021 prefixEnd_3177021 := by exact prefixLift 3177021
  have htrace : WordTrace (prefixWord ++ tailWord_3177021) baseStart_3177021 baseEnd_3177021 := by
    simpa [prefixWord, tailWord_3177021, baseEnd_3177021] using wordTrace_append hprefix tailTrace_3177021
  have hstable : (prefixWord ++ tailWord_3177021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177021).length < 2 ^ (prefixWord ++ tailWord_3177021).sum := by decide
  have hdescent : baseEnd_3177021 < baseStart_3177021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177034 : List Nat := [3, 1, 2, 1, 1, 5, 3, 6]
def baseStart_3177034 : Nat := 118140960795 + 3177034 * 2 ^ 59
def prefixEnd_3177034 : Nat := 4983230072969 + 3 ^ 40 * 3177034 * 2
def baseEnd_3177034 : Nat := 120840407235290968412155

theorem tailTrace_3177034 : CollatzResearch.WordTrace tailWord_3177034 prefixEnd_3177034 120840407235290968412155 := by
  unfold tailWord_3177034
  simp only [CollatzResearch.WordTrace]
  refine ⟨28968987393038971763544539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77250633048103924702785437 28968987393038971763544539)
  ·
    refine ⟨43453481089558457645316809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28968987393038971763544539 43453481089558457645316809)
    ·
      refine ⟨32590110817168843233987607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43453481089558457645316809 32590110817168843233987607)
      ·
        refine ⟨48885166225753264850981411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32590110817168843233987607 48885166225753264850981411)
        ·
          refine ⟨73327749338629897276472117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48885166225753264850981411 73327749338629897276472117)
          ·
            refine ⟨6874476500496552869669261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73327749338629897276472117 6874476500496552869669261)
            ·
              refine ⟨2577928687686207326125973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6874476500496552869669261 2577928687686207326125973)
              ·
                refine ⟨120840407235290968412155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2577928687686207326125973 120840407235290968412155)
                ·
                  rfl

theorem cell22_3177034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_3177034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177034 prefixEnd_3177034 := by exact prefixLift 3177034
  have htrace : WordTrace (prefixWord ++ tailWord_3177034) baseStart_3177034 baseEnd_3177034 := by
    simpa [prefixWord, tailWord_3177034, baseEnd_3177034] using wordTrace_append hprefix tailTrace_3177034
  have hstable : (prefixWord ++ tailWord_3177034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177034).length < 2 ^ (prefixWord ++ tailWord_3177034).sum := by decide
  have hdescent : baseEnd_3177034 < baseStart_3177034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177066 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_3177066 : Nat := 118140960795 + 3177066 * 2 ^ 59
def prefixEnd_3177066 : Nat := 4983230072969 + 3 ^ 40 * 3177066 * 2
def baseEnd_3177066 : Nat := 1087574619371581298909297

theorem tailTrace_3177066 : CollatzResearch.WordTrace tailWord_3177066 prefixEnd_3177066 1087574619371581298909297 := by
  unfold tailWord_3177066
  simp only [CollatzResearch.WordTrace]
  refine ⟨28969279177009989129835763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77251411138693304346228701 28969279177009989129835763)
  ·
    refine ⟨43453918765514983694753645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28969279177009989129835763 43453918765514983694753645)
    ·
      refine ⟨16295219537068118885532617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43453918765514983694753645 16295219537068118885532617)
      ·
        refine ⟨12221414652801089164149463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16295219537068118885532617 12221414652801089164149463)
        ·
          refine ⟨18332121979201633746224195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12221414652801089164149463 18332121979201633746224195)
          ·
            refine ⟨27498182968802450619336293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18332121979201633746224195 27498182968802450619336293)
            ·
              refine ⟨5155909306650459491125555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27498182968802450619336293 5155909306650459491125555)
              ·
                refine ⟨7733863959975689236688333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155909306650459491125555 7733863959975689236688333)
                ·
                  refine ⟨2900198984990883463758125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7733863959975689236688333 2900198984990883463758125)
                  ·
                    refine ⟨1087574619371581298909297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900198984990883463758125 1087574619371581298909297)
                    ·
                      rfl

theorem cell22_3177066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_3177066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177066 prefixEnd_3177066 := by exact prefixLift 3177066
  have htrace : WordTrace (prefixWord ++ tailWord_3177066) baseStart_3177066 baseEnd_3177066 := by
    simpa [prefixWord, tailWord_3177066, baseEnd_3177066] using wordTrace_append hprefix tailTrace_3177066
  have hstable : (prefixWord ++ tailWord_3177066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177066).length < 2 ^ (prefixWord ++ tailWord_3177066).sum := by decide
  have hdescent : baseEnd_3177066 < baseStart_3177066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177143 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 1, 4]
def baseStart_3177143 : Nat := 118140960795 + 3177143 * 2 ^ 59
def prefixEnd_3177143 : Nat := 4983230072969 + 3 ^ 40 * 3177143 * 2
def baseEnd_3177143 : Nat := 1087600978045178764734061

theorem tailTrace_3177143 : CollatzResearch.WordTrace tailWord_3177143 prefixEnd_3177143 1087600978045178764734061 := by
  unfold tailWord_3177143
  simp only [CollatzResearch.WordTrace]
  refine ⟨115879925128760998669896083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77253283419173999113264055 115879925128760998669896083)
  ·
    refine ⟨173819887693141498004844125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115879925128760998669896083 173819887693141498004844125)
    ·
      refine ⟨65182457884928061751816547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173819887693141498004844125 65182457884928061751816547)
      ·
        refine ⟨97773686827392092627724821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65182457884928061751816547 97773686827392092627724821)
        ·
          refine ⟨4583141570034004341924601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97773686827392092627724821 4583141570034004341924601)
          ·
            refine ⟨3437356177525503256443451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583141570034004341924601 3437356177525503256443451)
            ·
              refine ⟨5156034266288254884665177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437356177525503256443451 5156034266288254884665177)
              ·
                refine ⟨3867025699716191163498883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5156034266288254884665177 3867025699716191163498883)
                ·
                  refine ⟨5800538549574286745248325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3867025699716191163498883 5800538549574286745248325)
                  ·
                    refine ⟨1087600978045178764734061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5800538549574286745248325 1087600978045178764734061)
                    ·
                      rfl

theorem cell22_3177143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_3177143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177143 prefixEnd_3177143 := by exact prefixLift 3177143
  have htrace : WordTrace (prefixWord ++ tailWord_3177143) baseStart_3177143 baseEnd_3177143 := by
    simpa [prefixWord, tailWord_3177143, baseEnd_3177143] using wordTrace_append hprefix tailTrace_3177143
  have hstable : (prefixWord ++ tailWord_3177143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177143).length < 2 ^ (prefixWord ++ tailWord_3177143).sum := by decide
  have hdescent : baseEnd_3177143 < baseStart_3177143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177156 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3177156 : Nat := 118140960795 + 3177156 * 2 ^ 59
def prefixEnd_3177156 : Nat := 4983230072969 + 3 ^ 40 * 3177156 * 2
def baseEnd_3177156 : Nat := 1087605428210851064159021

theorem tailTrace_3177156 : CollatzResearch.WordTrace tailWord_3177156 prefixEnd_3177156 1087605428210851064159021 := by
  unfold tailWord_3177156
  simp only [CollatzResearch.WordTrace]
  refine ⟨57940199638856950945059661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77253599518475934593412881 57940199638856950945059661)
  ·
    refine ⟨21727574864571356604397373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57940199638856950945059661 21727574864571356604397373)
    ·
      refine ⟨8147840574214258726649015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21727574864571356604397373 8147840574214258726649015)
      ·
        refine ⟨12221760861321388089973523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8147840574214258726649015 12221760861321388089973523)
        ·
          refine ⟨18332641291982082134960285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12221760861321388089973523 18332641291982082134960285)
          ·
            refine ⟨6874740484493280800610107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18332641291982082134960285 6874740484493280800610107)
            ·
              refine ⟨10312110726739921200915161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874740484493280800610107 10312110726739921200915161)
              ·
                refine ⟨7734083045054940900686371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10312110726739921200915161 7734083045054940900686371)
                ·
                  refine ⟨11601124567582411351029557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7734083045054940900686371 11601124567582411351029557)
                  ·
                    refine ⟨1087605428210851064159021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11601124567582411351029557 1087605428210851064159021)
                    ·
                      rfl

theorem cell22_3177156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3177156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177156 prefixEnd_3177156 := by exact prefixLift 3177156
  have htrace : WordTrace (prefixWord ++ tailWord_3177156) baseStart_3177156 baseEnd_3177156 := by
    simpa [prefixWord, tailWord_3177156, baseEnd_3177156] using wordTrace_append hprefix tailTrace_3177156
  have hstable : (prefixWord ++ tailWord_3177156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177156).length < 2 ^ (prefixWord ++ tailWord_3177156).sum := by decide
  have hdescent : baseEnd_3177156 < baseStart_3177156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177201 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 3, 3]
def baseStart_3177201 : Nat := 118140960795 + 3177201 * 2 ^ 59
def prefixEnd_3177201 : Nat := 4983230072969 + 3 ^ 40 * 3177201 * 2
def baseEnd_3177201 : Nat := 1087620832630485946783883

theorem tailTrace_3177201 : CollatzResearch.WordTrace tailWord_3177201 prefixEnd_3177201 1087620832630485946783883 := by
  unfold tailWord_3177201
  simp only [CollatzResearch.WordTrace]
  refine ⟨115882040562550874575507457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77254693708367249717004971 115882040562550874575507457)
  ·
    refine ⟨86911530421913155931630593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115882040562550874575507457 86911530421913155931630593)
    ·
      refine ⟨65183647816434866948722945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86911530421913155931630593 65183647816434866948722945)
      ·
        refine ⟨48887735862326150211542209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65183647816434866948722945 48887735862326150211542209)
        ·
          refine ⟨36665801896744612658656657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48887735862326150211542209 36665801896744612658656657)
          ·
            refine ⟨27499351422558459493992493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36665801896744612658656657 27499351422558459493992493)
            ·
              refine ⟨10312256783459422310247185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27499351422558459493992493 10312256783459422310247185)
              ·
                refine ⟨7734192587594566732685389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10312256783459422310247185 7734192587594566732685389)
                ·
                  refine ⟨2900322220347962524757021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7734192587594566732685389 2900322220347962524757021)
                  ·
                    refine ⟨1087620832630485946783883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900322220347962524757021 1087620832630485946783883)
                    ·
                      rfl

theorem cell22_3177201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_3177201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177201 prefixEnd_3177201 := by exact prefixLift 3177201
  have htrace : WordTrace (prefixWord ++ tailWord_3177201) baseStart_3177201 baseEnd_3177201 := by
    simpa [prefixWord, tailWord_3177201, baseEnd_3177201] using wordTrace_append hprefix tailTrace_3177201
  have hstable : (prefixWord ++ tailWord_3177201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177201).length < 2 ^ (prefixWord ++ tailWord_3177201).sum := by decide
  have hdescent : baseEnd_3177201 < baseStart_3177201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177205 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3177205 : Nat := 118140960795 + 3177205 * 2 ^ 59
def prefixEnd_3177205 : Nat := 4983230072969 + 3 ^ 40 * 3177205 * 2
def baseEnd_3177205 : Nat := 1087622201912231269683871

theorem tailTrace_3177205 : CollatzResearch.WordTrace tailWord_3177205 prefixEnd_3177205 1087622201912231269683871 := by
  unfold tailWord_3177205
  simp only [CollatzResearch.WordTrace]
  refine ⟨115882186454536383258653069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77254790969690922172435379 115882186454536383258653069)
  ·
    refine ⟨43455819920451143721994901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115882186454536383258653069 43455819920451143721994901)
    ·
      refine ⟨2036991558771147361968511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43455819920451143721994901 2036991558771147361968511)
      ·
        refine ⟨3055487338156721042952767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036991558771147361968511 3055487338156721042952767)
        ·
          refine ⟨4583231007235081564429151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055487338156721042952767 4583231007235081564429151)
          ·
            refine ⟨6874846510852622346643727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583231007235081564429151 6874846510852622346643727)
            ·
              refine ⟨10312269766278933519965591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874846510852622346643727 10312269766278933519965591)
              ·
                refine ⟨15468404649418400279948387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10312269766278933519965591 15468404649418400279948387)
                ·
                  refine ⟨23202606974127600419922581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15468404649418400279948387 23202606974127600419922581)
                  ·
                    refine ⟨1087622201912231269683871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23202606974127600419922581 1087622201912231269683871)
                    ·
                      rfl

theorem cell22_3177205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3177205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177205 prefixEnd_3177205 := by exact prefixLift 3177205
  have htrace : WordTrace (prefixWord ++ tailWord_3177205) baseStart_3177205 baseEnd_3177205 := by
    simpa [prefixWord, tailWord_3177205, baseEnd_3177205] using wordTrace_append hprefix tailTrace_3177205
  have hstable : (prefixWord ++ tailWord_3177205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177205).length < 2 ^ (prefixWord ++ tailWord_3177205).sum := by decide
  have hdescent : baseEnd_3177205 < baseStart_3177205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177248 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 5]
def baseStart_3177248 : Nat := 118140960795 + 3177248 * 2 ^ 59
def prefixEnd_3177248 : Nat := 4983230072969 + 3 ^ 40 * 3177248 * 2
def baseEnd_3177248 : Nat := 362545640563664496952913

theorem tailTrace_3177248 : CollatzResearch.WordTrace tailWord_3177248 prefixEnd_3177248 362545640563664496952913 := by
  unfold tailWord_3177248
  simp only [CollatzResearch.WordTrace]
  refine ⟨57941877396690300801234199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77255836528920401068312265 57941877396690300801234199)
  ·
    refine ⟨86912816095035451201851299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57941877396690300801234199 86912816095035451201851299)
    ·
      refine ⟨130369224142553176802776949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86912816095035451201851299 130369224142553176802776949)
      ·
        refine ⟨12222114763364360325260339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130369224142553176802776949 12222114763364360325260339)
        ·
          refine ⟨18333172145046540487890509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12222114763364360325260339 18333172145046540487890509)
          ·
            refine ⟨6874939554392452682958941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18333172145046540487890509 6874939554392452682958941)
            ·
              refine ⟨2578102332897169756109603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6874939554392452682958941 2578102332897169756109603)
              ·
                refine ⟨3867153499345754634164405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578102332897169756109603 3867153499345754634164405)
                ·
                  refine ⟨362545640563664496952913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3867153499345754634164405 362545640563664496952913)
                  ·
                    rfl

theorem cell22_3177248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_3177248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177248 prefixEnd_3177248 := by exact prefixLift 3177248
  have htrace : WordTrace (prefixWord ++ tailWord_3177248) baseStart_3177248 baseEnd_3177248 := by
    simpa [prefixWord, tailWord_3177248, baseEnd_3177248] using wordTrace_append hprefix tailTrace_3177248
  have hstable : (prefixWord ++ tailWord_3177248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177248).length < 2 ^ (prefixWord ++ tailWord_3177248).sum := by decide
  have hdescent : baseEnd_3177248 < baseStart_3177248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177286 : List Nat := [6, 1, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3177286 : Nat := 118140960795 + 3177286 * 2 ^ 59
def prefixEnd_3177286 : Nat := 4983230072969 + 3 ^ 40 * 3177286 * 2
def baseEnd_3177286 : Nat := 1087649929867574058408623

theorem tailTrace_3177286 : CollatzResearch.WordTrace tailWord_3177286 prefixEnd_3177286 1087649929867574058408623 := by
  unfold tailWord_3177286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621410648976341690385991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77256760511495289394901141 3621410648976341690385991)
  ·
    refine ⟨5432115973464512535578987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3621410648976341690385991 5432115973464512535578987)
    ·
      refine ⟨8148173960196768803368481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5432115973464512535578987 8148173960196768803368481)
      ·
        refine ⟨6111130470147576602526361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8148173960196768803368481 6111130470147576602526361)
        ·
          refine ⟨4583347852610682451894771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111130470147576602526361 4583347852610682451894771)
          ·
            refine ⟨6875021778916023677842157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583347852610682451894771 6875021778916023677842157)
            ·
              refine ⟨2578133167093508879190809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6875021778916023677842157 2578133167093508879190809)
              ·
                refine ⟨1933599875320131659393107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2578133167093508879190809 1933599875320131659393107)
                ·
                  refine ⟨2900399812980197489089661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933599875320131659393107 2900399812980197489089661)
                  ·
                    refine ⟨1087649929867574058408623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900399812980197489089661 1087649929867574058408623)
                    ·
                      rfl

theorem cell22_3177286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3177286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177286 prefixEnd_3177286 := by exact prefixLift 3177286
  have htrace : WordTrace (prefixWord ++ tailWord_3177286) baseStart_3177286 baseEnd_3177286 := by
    simpa [prefixWord, tailWord_3177286, baseEnd_3177286] using wordTrace_append hprefix tailTrace_3177286
  have hstable : (prefixWord ++ tailWord_3177286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177286).length < 2 ^ (prefixWord ++ tailWord_3177286).sum := by decide
  have hdescent : baseEnd_3177286 < baseStart_3177286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177336 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 7, 3]
def baseStart_3177336 : Nat := 118140960795 + 3177336 * 2 ^ 59
def prefixEnd_3177336 : Nat := 4983230072969 + 3 ^ 40 * 3177336 * 2
def baseEnd_3177336 : Nat := 1087667045889390594658469

theorem tailTrace_3177336 : CollatzResearch.WordTrace tailWord_3177336 prefixEnd_3177336 1087667045889390594658469 := by
  unfold tailWord_3177336
  simp only [CollatzResearch.WordTrace]
  refine ⟨57943482208530896315835931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77257976278041195087781241 57943482208530896315835931)
  ·
    refine ⟨86915223312796344473753897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57943482208530896315835931 86915223312796344473753897)
    ·
      refine ⟨65186417484597258355315423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86915223312796344473753897 65186417484597258355315423)
      ·
        refine ⟨97779626226895887532973135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65186417484597258355315423 97779626226895887532973135)
        ·
          refine ⟨146669439340343831299459703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97779626226895887532973135 146669439340343831299459703)
          ·
            refine ⟨220004159010515746949189555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146669439340343831299459703 220004159010515746949189555)
            ·
              refine ⟨330006238515773620423784333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220004159010515746949189555 330006238515773620423784333)
              ·
                refine ⟨123752339443415107658919125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330006238515773620423784333 123752339443415107658919125)
                ·
                  refine ⟨2900445455705041585755917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123752339443415107658919125 2900445455705041585755917)
                  ·
                    refine ⟨1087667045889390594658469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900445455705041585755917 1087667045889390594658469)
                    ·
                      rfl

theorem cell22_3177336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_3177336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177336 prefixEnd_3177336 := by exact prefixLift 3177336
  have htrace : WordTrace (prefixWord ++ tailWord_3177336) baseStart_3177336 baseEnd_3177336 := by
    simpa [prefixWord, tailWord_3177336, baseEnd_3177336] using wordTrace_append hprefix tailTrace_3177336
  have hstable : (prefixWord ++ tailWord_3177336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177336).length < 2 ^ (prefixWord ++ tailWord_3177336).sum := by decide
  have hdescent : baseEnd_3177336 < baseStart_3177336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177351 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3177351 : Nat := 118140960795 + 3177351 * 2 ^ 59
def prefixEnd_3177351 : Nat := 4983230072969 + 3 ^ 40 * 3177351 * 2
def baseEnd_3177351 : Nat := 1087672180695935555533423

theorem tailTrace_3177351 : CollatzResearch.WordTrace tailWord_3177351 prefixEnd_3177351 1087672180695935555533423 := by
  unfold tailWord_3177351
  simp only [CollatzResearch.WordTrace]
  refine ⟨115887511512007450193467907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77258341008004966795645271 115887511512007450193467907)
  ·
    refine ⟨173831267268011175290201861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115887511512007450193467907 173831267268011175290201861)
    ·
      refine ⟨32593362612752095366912849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173831267268011175290201861 32593362612752095366912849)
      ·
        refine ⟨24445021959564071525184637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32593362612752095366912849 24445021959564071525184637)
        ·
          refine ⟨9166883234836526821944239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24445021959564071525184637 9166883234836526821944239)
          ·
            refine ⟨13750324852254790232916359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9166883234836526821944239 13750324852254790232916359)
            ·
              refine ⟨20625487278382185349374539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13750324852254790232916359 20625487278382185349374539)
              ·
                refine ⟨30938230917573278024061809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20625487278382185349374539 30938230917573278024061809)
                ·
                  refine ⟨23203673188179958518046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30938230917573278024061809 23203673188179958518046357)
                  ·
                    refine ⟨1087672180695935555533423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23203673188179958518046357 1087672180695935555533423)
                    ·
                      rfl

theorem cell22_3177351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3177351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177351 prefixEnd_3177351 := by exact prefixLift 3177351
  have htrace : WordTrace (prefixWord ++ tailWord_3177351) baseStart_3177351 baseEnd_3177351 := by
    simpa [prefixWord, tailWord_3177351, baseEnd_3177351] using wordTrace_append hprefix tailTrace_3177351
  have hstable : (prefixWord ++ tailWord_3177351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177351).length < 2 ^ (prefixWord ++ tailWord_3177351).sum := by decide
  have hdescent : baseEnd_3177351 < baseStart_3177351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177370 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_3177370 : Nat := 118140960795 + 3177370 * 2 ^ 59
def prefixEnd_3177370 : Nat := 4983230072969 + 3 ^ 40 * 3177370 * 2
def baseEnd_3177370 : Nat := 1087678684784225839308365

theorem tailTrace_3177370 : CollatzResearch.WordTrace tailWord_3177370 prefixEnd_3177370 1087678684784225839308365 := by
  unfold tailWord_3177370
  simp only [CollatzResearch.WordTrace]
  refine ⟨28972051124734654109602391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77258802999292410958939709 28972051124734654109602391)
  ·
    refine ⟨43458076687101981164403587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28972051124734654109602391 43458076687101981164403587)
    ·
      refine ⟨65187115030652971746605381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43458076687101981164403587 65187115030652971746605381)
      ·
        refine ⟨12222584068247432202488509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65187115030652971746605381 12222584068247432202488509)
        ·
          refine ⟨4583469025592787075933191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12222584068247432202488509 4583469025592787075933191)
          ·
            refine ⟨6875203538389180613899787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583469025592787075933191 6875203538389180613899787)
            ·
              refine ⟨10312805307583770920849681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875203538389180613899787 10312805307583770920849681)
              ·
                refine ⟨7734603980687828190637261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10312805307583770920849681 7734603980687828190637261)
                ·
                  refine ⟨2900476492757935571488973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7734603980687828190637261 2900476492757935571488973)
                  ·
                    refine ⟨1087678684784225839308365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900476492757935571488973 1087678684784225839308365)
                    ·
                      rfl

theorem cell22_3177370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_3177370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177370 prefixEnd_3177370 := by exact prefixLift 3177370
  have htrace : WordTrace (prefixWord ++ tailWord_3177370) baseStart_3177370 baseEnd_3177370 := by
    simpa [prefixWord, tailWord_3177370, baseEnd_3177370] using wordTrace_append hprefix tailTrace_3177370
  have hstable : (prefixWord ++ tailWord_3177370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177370).length < 2 ^ (prefixWord ++ tailWord_3177370).sum := by decide
  have hdescent : baseEnd_3177370 < baseStart_3177370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177428 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 6]
def baseStart_3177428 : Nat := 118140960795 + 3177428 * 2 ^ 59
def prefixEnd_3177428 : Nat := 4983230072969 + 3 ^ 40 * 3177428 * 2
def baseEnd_3177428 : Nat := 362566179789844340452729

theorem tailTrace_3177428 : CollatzResearch.WordTrace tailWord_3177428 prefixEnd_3177428 362566179789844340452729 := by
  unfold tailWord_3177428
  simp only [CollatzResearch.WordTrace]
  refine ⟨57945159966364246172010469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77260213288485661562680625 57945159966364246172010469)
  ·
    refine ⟨10864717493693296157251963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57945159966364246172010469 10864717493693296157251963)
    ·
      refine ⟨16297076240539944235877945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10864717493693296157251963 16297076240539944235877945)
      ·
        refine ⟨12222807180404958176908459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16297076240539944235877945 12222807180404958176908459)
        ·
          refine ⟨18334210770607437265362689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12222807180404958176908459 18334210770607437265362689)
          ·
            refine ⟨13750658077955577949022017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18334210770607437265362689 13750658077955577949022017)
            ·
              refine ⟨10312993558466683461766513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13750658077955577949022017 10312993558466683461766513)
              ·
                refine ⟨7734745168850012596324885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10312993558466683461766513 7734745168850012596324885)
                ·
                  refine ⟨362566179789844340452729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7734745168850012596324885 362566179789844340452729)
                  ·
                    rfl

theorem cell22_3177428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_3177428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177428 prefixEnd_3177428 := by exact prefixLift 3177428
  have htrace : WordTrace (prefixWord ++ tailWord_3177428) baseStart_3177428 baseEnd_3177428 := by
    simpa [prefixWord, tailWord_3177428, baseEnd_3177428] using wordTrace_append hprefix tailTrace_3177428
  have hstable : (prefixWord ++ tailWord_3177428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177428).length < 2 ^ (prefixWord ++ tailWord_3177428).sum := by decide
  have hdescent : baseEnd_3177428 < baseStart_3177428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177443 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 6, 3]
def baseStart_3177443 : Nat := 118140960795 + 3177443 * 2 ^ 59
def prefixEnd_3177443 : Nat := 4983230072969 + 3 ^ 40 * 3177443 * 2
def baseEnd_3177443 : Nat := 1087703674176077982233141

theorem tailTrace_3177443 : CollatzResearch.WordTrace tailWord_3177443 prefixEnd_3177443 1087703674176077982233141 := by
  unfold tailWord_3177443
  simp only [CollatzResearch.WordTrace]
  refine ⟨115890867027674149905816983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77260578018449433270544655 115890867027674149905816983)
  ·
    refine ⟨173836300541511224858725475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115890867027674149905816983 173836300541511224858725475)
    ·
      refine ⟨260754450812266837288088213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173836300541511224858725475 260754450812266837288088213)
      ·
        refine ⟨12222864881825007997879135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 260754450812266837288088213 12222864881825007997879135)
        ·
          refine ⟨18334297322737511996818703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12222864881825007997879135 18334297322737511996818703)
          ·
            refine ⟨27501445984106267995228055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18334297322737511996818703 27501445984106267995228055)
            ·
              refine ⟨41252168976159401992842083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27501445984106267995228055 41252168976159401992842083)
              ·
                refine ⟨61878253464239102989263125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41252168976159401992842083 61878253464239102989263125)
                ·
                  refine ⟨2900543131136207952621709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61878253464239102989263125 2900543131136207952621709)
                  ·
                    refine ⟨1087703674176077982233141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900543131136207952621709 1087703674176077982233141)
                    ·
                      rfl

theorem cell22_3177443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 3].length) (baseStart_3177443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177443 prefixEnd_3177443 := by exact prefixLift 3177443
  have htrace : WordTrace (prefixWord ++ tailWord_3177443) baseStart_3177443 baseEnd_3177443 := by
    simpa [prefixWord, tailWord_3177443, baseEnd_3177443] using wordTrace_append hprefix tailTrace_3177443
  have hstable : (prefixWord ++ tailWord_3177443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177443).length < 2 ^ (prefixWord ++ tailWord_3177443).sum := by decide
  have hdescent : baseEnd_3177443 < baseStart_3177443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177473 : List Nat := [1, 2, 4, 1, 2, 3, 2, 7]
def baseStart_3177473 : Nat := 118140960795 + 3177473 * 2 ^ 59
def prefixEnd_3177473 : Nat := 4983230072969 + 3 ^ 40 * 3177473 * 2
def baseEnd_3177473 : Nat := 120857104865463100442561

theorem tailTrace_3177473 : CollatzResearch.WordTrace tailWord_3177473 prefixEnd_3177473 120857104865463100442561 := by
  unfold tailWord_3177473
  simp only [CollatzResearch.WordTrace]
  refine ⟨115891961217565465029409073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77261307478376976686272715 115891961217565465029409073)
  ·
    refine ⟨86918970913174098772056805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115891961217565465029409073 86918970913174098772056805)
    ·
      refine ⟨16297307046220143519760651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86918970913174098772056805 16297307046220143519760651)
      ·
        refine ⟨24445960569330215279640977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16297307046220143519760651 24445960569330215279640977)
        ·
          refine ⟨18334470426997661459730733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24445960569330215279640977 18334470426997661459730733)
          ·
            refine ⟨6875426410124123047399025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18334470426997661459730733 6875426410124123047399025)
            ·
              refine ⟨5156569807593092285549269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6875426410124123047399025 5156569807593092285549269)
              ·
                refine ⟨120857104865463100442561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5156569807593092285549269 120857104865463100442561)
                ·
                  rfl

theorem cell22_3177473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 7].length) (baseStart_3177473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177473 prefixEnd_3177473 := by exact prefixLift 3177473
  have htrace : WordTrace (prefixWord ++ tailWord_3177473) baseStart_3177473 baseEnd_3177473 := by
    simpa [prefixWord, tailWord_3177473, baseEnd_3177473] using wordTrace_append hprefix tailTrace_3177473
  have hstable : (prefixWord ++ tailWord_3177473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177473).length < 2 ^ (prefixWord ++ tailWord_3177473).sum := by decide
  have hdescent : baseEnd_3177473 < baseStart_3177473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177522 : List Nat := [3, 2, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_3177522 : Nat := 118140960795 + 3177522 * 2 ^ 59
def prefixEnd_3177522 : Nat := 4983230072969 + 3 ^ 40 * 3177522 * 2
def baseEnd_3177522 : Nat := 1087730717490548109507899

theorem tailTrace_3177522 : CollatzResearch.WordTrace tailWord_3177522 prefixEnd_3177522 1087730717490548109507899 := by
  unfold tailWord_3177522
  simp only [CollatzResearch.WordTrace]
  refine ⟨28973437098596986599485705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77262498929591964265295213 28973437098596986599485705)
  ·
    refine ⟨21730077823947739949614279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28973437098596986599485705 21730077823947739949614279)
    ·
      refine ⟨32595116735921609924421419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21730077823947739949614279 32595116735921609924421419)
      ·
        refine ⟨48892675103882414886632129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32595116735921609924421419 48892675103882414886632129)
        ·
          refine ⟨36669506327911811164974097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48892675103882414886632129 36669506327911811164974097)
          ·
            refine ⟨27502129745933858373730573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36669506327911811164974097 27502129745933858373730573)
            ·
              refine ⟨10313298654725196890148965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27502129745933858373730573 10313298654725196890148965)
              ·
                refine ⟨1933743497760974416902931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10313298654725196890148965 1933743497760974416902931)
                ·
                  refine ⟨2900615246641461625354397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933743497760974416902931 2900615246641461625354397)
                  ·
                    refine ⟨1087730717490548109507899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900615246641461625354397 1087730717490548109507899)
                    ·
                      rfl

theorem cell22_3177522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_3177522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177522 prefixEnd_3177522 := by exact prefixLift 3177522
  have htrace : WordTrace (prefixWord ++ tailWord_3177522) baseStart_3177522 baseEnd_3177522 := by
    simpa [prefixWord, tailWord_3177522, baseEnd_3177522] using wordTrace_append hprefix tailTrace_3177522
  have hstable : (prefixWord ++ tailWord_3177522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177522).length < 2 ^ (prefixWord ++ tailWord_3177522).sum := by decide
  have hdescent : baseEnd_3177522 < baseStart_3177522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177531 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 10]
def baseStart_3177531 : Nat := 118140960795 + 3177531 * 2 ^ 59
def prefixEnd_3177531 : Nat := 4983230072969 + 3 ^ 40 * 3177531 * 2
def baseEnd_3177531 : Nat := 1087733798374475086032871

theorem tailTrace_3177531 : CollatzResearch.WordTrace tailWord_3177531 prefixEnd_3177531 1087733798374475086032871 := by
  unfold tailWord_3177531
  simp only [CollatzResearch.WordTrace]
  refine ⟨115894076651355340935020447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77262717767570227290013631 115894076651355340935020447)
  ·
    refine ⟨173841114977033011402530671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115894076651355340935020447 173841114977033011402530671)
    ·
      refine ⟨260761672465549517103796007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173841114977033011402530671 260761672465549517103796007)
      ·
        refine ⟨391142508698324275655694011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260761672465549517103796007 391142508698324275655694011)
        ·
          refine ⟨586713763047486413483541017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391142508698324275655694011 586713763047486413483541017)
          ·
            refine ⟨440035322285614810112655763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586713763047486413483541017 440035322285614810112655763)
            ·
              refine ⟨660052983428422215168983645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440035322285614810112655763 660052983428422215168983645)
              ·
                refine ⟨247519868785658330688368867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660052983428422215168983645 247519868785658330688368867)
                ·
                  refine ⟨371279803178487496032553301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247519868785658330688368867 371279803178487496032553301)
                  ·
                    refine ⟨1087733798374475086032871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 371279803178487496032553301 1087733798374475086032871)
                    ·
                      rfl

theorem cell22_3177531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_3177531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177531 prefixEnd_3177531 := by exact prefixLift 3177531
  have htrace : WordTrace (prefixWord ++ tailWord_3177531) baseStart_3177531 baseEnd_3177531 := by
    simpa [prefixWord, tailWord_3177531, baseEnd_3177531] using wordTrace_append hprefix tailTrace_3177531
  have hstable : (prefixWord ++ tailWord_3177531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177531).length < 2 ^ (prefixWord ++ tailWord_3177531).sum := by decide
  have hdescent : baseEnd_3177531 < baseStart_3177531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177533 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_3177533 : Nat := 118140960795 + 3177533 * 2 ^ 59
def prefixEnd_3177533 : Nat := 4983230072969 + 3 ^ 40 * 3177533 * 2
def baseEnd_3177533 : Nat := 1087734483015347747482865

theorem tailTrace_3177533 : CollatzResearch.WordTrace tailWord_3177533 prefixEnd_3177533 1087734483015347747482865 := by
  unfold tailWord_3177533
  simp only [CollatzResearch.WordTrace]
  refine ⟨115894149597348095276593253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77262766398232063517728835 115894149597348095276593253)
  ·
    refine ⟨21730153049502767864361235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115894149597348095276593253 21730153049502767864361235)
    ·
      refine ⟨32595229574254151796541853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21730153049502767864361235 32595229574254151796541853)
      ·
        refine ⟨12223211090345306923703195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32595229574254151796541853 12223211090345306923703195)
        ·
          refine ⟨18334816635517960385554793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12223211090345306923703195 18334816635517960385554793)
          ·
            refine ⟨13751112476638470289166095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18334816635517960385554793 13751112476638470289166095)
            ·
              refine ⟨20626668714957705433749143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13751112476638470289166095 20626668714957705433749143)
              ·
                refine ⟨30940003072436558150623715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20626668714957705433749143 30940003072436558150623715)
                ·
                  refine ⟨46410004608654837225935573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30940003072436558150623715 46410004608654837225935573)
                  ·
                    refine ⟨1087734483015347747482865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46410004608654837225935573 1087734483015347747482865)
                    ·
                      rfl

theorem cell22_3177533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_3177533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177533 prefixEnd_3177533 := by exact prefixLift 3177533
  have htrace : WordTrace (prefixWord ++ tailWord_3177533) baseStart_3177533 baseEnd_3177533 := by
    simpa [prefixWord, tailWord_3177533, baseEnd_3177533] using wordTrace_append hprefix tailTrace_3177533
  have hstable : (prefixWord ++ tailWord_3177533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177533).length < 2 ^ (prefixWord ++ tailWord_3177533).sum := by decide
  have hdescent : baseEnd_3177533 < baseStart_3177533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177580 : List Nat := [2, 2, 1, 1, 3, 2, 1, 6, 4]
def baseStart_3177580 : Nat := 118140960795 + 3177580 * 2 ^ 59
def prefixEnd_3177580 : Nat := 4983230072969 + 3 ^ 40 * 3177580 * 2
def baseEnd_3177580 : Nat := 362583524025285097185907

theorem tailTrace_3177580 : CollatzResearch.WordTrace tailWord_3177580 prefixEnd_3177580 362583524025285097185907 := by
  unfold tailWord_3177580
  simp only [CollatzResearch.WordTrace]
  refine ⟨57947931914088911151777097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77263909218785214869036129 57947931914088911151777097)
  ·
    refine ⟨43460948935566683363832823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57947931914088911151777097 43460948935566683363832823)
    ·
      refine ⟨65191423403350025045749235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43460948935566683363832823 65191423403350025045749235)
      ·
        refine ⟨97787135105025037568623853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65191423403350025045749235 97787135105025037568623853)
        ·
          refine ⟨36670175664384389088233945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97787135105025037568623853 36670175664384389088233945)
          ·
            refine ⟨27502631748288291816175459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36670175664384389088233945 27502631748288291816175459)
            ·
              refine ⟨41253947622432437724263189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27502631748288291816175459 41253947622432437724263189)
              ·
                refine ⟨1933778794801520518324837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41253947622432437724263189 1933778794801520518324837)
                ·
                  refine ⟨362583524025285097185907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1933778794801520518324837 362583524025285097185907)
                  ·
                    rfl

theorem cell22_3177580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_3177580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177580 prefixEnd_3177580 := by exact prefixLift 3177580
  have htrace : WordTrace (prefixWord ++ tailWord_3177580) baseStart_3177580 baseEnd_3177580 := by
    simpa [prefixWord, tailWord_3177580, baseEnd_3177580] using wordTrace_append hprefix tailTrace_3177580
  have hstable : (prefixWord ++ tailWord_3177580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177580).length < 2 ^ (prefixWord ++ tailWord_3177580).sum := by decide
  have hdescent : baseEnd_3177580 < baseStart_3177580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177595 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 2, 3]
def baseStart_3177595 : Nat := 118140960795 + 3177595 * 2 ^ 59
def prefixEnd_3177595 : Nat := 4983230072969 + 3 ^ 40 * 3177595 * 2
def baseEnd_3177595 : Nat := 1087755706882400252432675

theorem tailTrace_3177595 : CollatzResearch.WordTrace tailWord_3177595 prefixEnd_3177595 1087755706882400252432675 := by
  unfold tailWord_3177595
  simp only [CollatzResearch.WordTrace]
  refine ⟨115896410923123479865350239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77264273948748986576900159 115896410923123479865350239)
  ·
    refine ⟨173844616384685219798025359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115896410923123479865350239 173844616384685219798025359)
    ·
      refine ⟨260766924577027829697038039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173844616384685219798025359 260766924577027829697038039)
      ·
        refine ⟨391150386865541744545557059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260766924577027829697038039 391150386865541744545557059)
        ·
          refine ⟨586725580298312616818335589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391150386865541744545557059 586725580298312616818335589)
          ·
            refine ⟨110011046305933615653437923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 586725580298312616818335589 110011046305933615653437923)
            ·
              refine ⟨165016569458900423480156885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110011046305933615653437923 165016569458900423480156885)
              ·
                refine ⟨3867575846692978675316177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165016569458900423480156885 3867575846692978675316177)
                ·
                  refine ⟨2900681885019734006487133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3867575846692978675316177 2900681885019734006487133)
                  ·
                    refine ⟨1087755706882400252432675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900681885019734006487133 1087755706882400252432675)
                    ·
                      rfl

theorem cell22_3177595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 3].length) (baseStart_3177595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177595 prefixEnd_3177595 := by exact prefixLift 3177595
  have htrace : WordTrace (prefixWord ++ tailWord_3177595) baseStart_3177595 baseEnd_3177595 := by
    simpa [prefixWord, tailWord_3177595, baseEnd_3177595] using wordTrace_append hprefix tailTrace_3177595
  have hstable : (prefixWord ++ tailWord_3177595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177595).length < 2 ^ (prefixWord ++ tailWord_3177595).sum := by decide
  have hdescent : baseEnd_3177595 < baseStart_3177595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177610 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_3177610 : Nat := 118140960795 + 3177610 * 2 ^ 59
def prefixEnd_3177610 : Nat := 4983230072969 + 3 ^ 40 * 3177610 * 2
def baseEnd_3177610 : Nat := 1087760841688945213307629

theorem tailTrace_3177610 : CollatzResearch.WordTrace tailWord_3177610 prefixEnd_3177610 1087760841688945213307629 := by
  unfold tailWord_3177610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28974239504517284356786571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77264638678712758284764189 28974239504517284356786571)
  ·
    refine ⟨43461359256775926535179857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28974239504517284356786571 43461359256775926535179857)
    ·
      refine ⟨32596019442581944901384893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43461359256775926535179857 32596019442581944901384893)
      ·
        refine ⟨12223507290968229338019335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32596019442581944901384893 12223507290968229338019335)
        ·
          refine ⟨18335260936452344007029003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12223507290968229338019335 18335260936452344007029003)
          ·
            refine ⟨27502891404678516010543505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18335260936452344007029003 27502891404678516010543505)
            ·
              refine ⟨20627168553508887007907629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27502891404678516010543505 20627168553508887007907629)
              ·
                refine ⟨7735188207565832627965361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20627168553508887007907629 7735188207565832627965361)
                ·
                  refine ⟨5801391155674374470974021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7735188207565832627965361 5801391155674374470974021)
                  ·
                    refine ⟨1087760841688945213307629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5801391155674374470974021 1087760841688945213307629)
                    ·
                      rfl

theorem cell22_3177610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_3177610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177610 prefixEnd_3177610 := by exact prefixLift 3177610
  have htrace : WordTrace (prefixWord ++ tailWord_3177610) baseStart_3177610 baseEnd_3177610 := by
    simpa [prefixWord, tailWord_3177610, baseEnd_3177610] using wordTrace_append hprefix tailTrace_3177610
  have hstable : (prefixWord ++ tailWord_3177610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177610).length < 2 ^ (prefixWord ++ tailWord_3177610).sum := by decide
  have hdescent : baseEnd_3177610 < baseStart_3177610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177614 : List Nat := [4, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_3177614 : Nat := 118140960795 + 3177614 * 2 ^ 59
def prefixEnd_3177614 : Nat := 4983230072969 + 3 ^ 40 * 3177614 * 2
def baseEnd_3177614 : Nat := 362587403656896845402539

theorem tailTrace_3177614 : CollatzResearch.WordTrace tailWord_3177614 prefixEnd_3177614 362587403656896845402539 := by
  unfold tailWord_3177614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14487137988756830763786487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77264735940036430740194597 14487137988756830763786487)
  ·
    refine ⟨21730706983135246145679731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14487137988756830763786487 21730706983135246145679731)
    ·
      refine ⟨32596060474702869218519597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21730706983135246145679731 32596060474702869218519597)
      ·
        refine ⟨12223522678013575956944849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32596060474702869218519597 12223522678013575956944849)
        ·
          refine ⟨9167642008510181967708637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12223522678013575956944849 9167642008510181967708637)
          ·
            refine ⟨3437865753191318237890739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9167642008510181967708637 3437865753191318237890739)
            ·
              refine ⟨5156798629786977356836109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437865753191318237890739 5156798629786977356836109)
              ·
                refine ⟨1933799486170116508813541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5156798629786977356836109 1933799486170116508813541)
                ·
                  refine ⟨362587403656896845402539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1933799486170116508813541 362587403656896845402539)
                  ·
                    rfl

theorem cell22_3177614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_3177614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177614 prefixEnd_3177614 := by exact prefixLift 3177614
  have htrace : WordTrace (prefixWord ++ tailWord_3177614) baseStart_3177614 baseEnd_3177614 := by
    simpa [prefixWord, tailWord_3177614, baseEnd_3177614] using wordTrace_append hprefix tailTrace_3177614
  have hstable : (prefixWord ++ tailWord_3177614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177614).length < 2 ^ (prefixWord ++ tailWord_3177614).sum := by decide
  have hdescent : baseEnd_3177614 < baseStart_3177614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177642 : List Nat := [3, 1, 5, 1, 1, 2, 2, 7]
def baseStart_3177642 : Nat := 118140960795 + 3177642 * 2 ^ 59
def prefixEnd_3177642 : Nat := 4983230072969 + 3 ^ 40 * 3177642 * 2
def baseEnd_3177642 : Nat := 120863532882545310723059

theorem tailTrace_3177642 : CollatzResearch.WordTrace tailWord_3177642 prefixEnd_3177642 120863532882545310723059 := by
  unfold tailWord_3177642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28974531288488301723077795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77265416769302137928207453 28974531288488301723077795)
  ·
    refine ⟨43461796932732452584616693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28974531288488301723077795 43461796932732452584616693)
    ·
      refine ⟨4074543462443667429807815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43461796932732452584616693 4074543462443667429807815)
      ·
        refine ⟨6111815193665501144711723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074543462443667429807815 6111815193665501144711723)
        ·
          refine ⟨9167722790498251717067585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111815193665501144711723 9167722790498251717067585)
          ·
            refine ⟨6875792092873688787800689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9167722790498251717067585 6875792092873688787800689)
            ·
              refine ⟨5156844069655266590850517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6875792092873688787800689 5156844069655266590850517)
              ·
                refine ⟨120863532882545310723059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5156844069655266590850517 120863532882545310723059)
                ·
                  rfl

theorem cell22_3177642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_3177642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177642 prefixEnd_3177642 := by exact prefixLift 3177642
  have htrace : WordTrace (prefixWord ++ tailWord_3177642) baseStart_3177642 baseEnd_3177642 := by
    simpa [prefixWord, tailWord_3177642, baseEnd_3177642] using wordTrace_append hprefix tailTrace_3177642
  have hstable : (prefixWord ++ tailWord_3177642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177642).length < 2 ^ (prefixWord ++ tailWord_3177642).sum := by decide
  have hdescent : baseEnd_3177642 < baseStart_3177642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177700 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3177700 : Nat := 118140960795 + 3177700 * 2 ^ 59
def prefixEnd_3177700 : Nat := 4983230072969 + 3 ^ 40 * 3177700 * 2
def baseEnd_3177700 : Nat := 1087791650528214978557353

theorem tailTrace_3177700 : CollatzResearch.WordTrace tailWord_3177700 prefixEnd_3177700 1087791650528214978557353 := by
  unfold tailWord_3177700
  simp only [CollatzResearch.WordTrace]
  refine ⟨57950120293871541398961277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77266827058495388531948369 57950120293871541398961277)
  ·
    refine ⟨21731295110201828024610479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57950120293871541398961277 21731295110201828024610479)
    ·
      refine ⟨32596942665302742036915719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21731295110201828024610479 32596942665302742036915719)
      ·
        refine ⟨48895413997954113055373579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32596942665302742036915719 48895413997954113055373579)
        ·
          refine ⟨73343120996931169583060369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48895413997954113055373579 73343120996931169583060369)
          ·
            refine ⟨55007340747698377187295277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73343120996931169583060369 55007340747698377187295277)
            ·
              refine ⟨20627752780386891445235729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55007340747698377187295277 20627752780386891445235729)
              ·
                refine ⟨15470814585290168583926797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20627752780386891445235729 15470814585290168583926797)
                ·
                  refine ⟨5801555469483813218972549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15470814585290168583926797 5801555469483813218972549)
                  ·
                    refine ⟨1087791650528214978557353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5801555469483813218972549 1087791650528214978557353)
                    ·
                      rfl

theorem cell22_3177700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3177700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177700 prefixEnd_3177700 := by exact prefixLift 3177700
  have htrace : WordTrace (prefixWord ++ tailWord_3177700) baseStart_3177700 baseEnd_3177700 := by
    simpa [prefixWord, tailWord_3177700, baseEnd_3177700] using wordTrace_append hprefix tailTrace_3177700
  have hstable : (prefixWord ++ tailWord_3177700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177700).length < 2 ^ (prefixWord ++ tailWord_3177700).sum := by decide
  have hdescent : baseEnd_3177700 < baseStart_3177700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177715 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 6]
def baseStart_3177715 : Nat := 118140960795 + 3177715 * 2 ^ 59
def prefixEnd_3177715 : Nat := 4983230072969 + 3 ^ 40 * 3177715 * 2
def baseEnd_3177715 : Nat := 362598928444919979810769

theorem tailTrace_3177715 : CollatzResearch.WordTrace tailWord_3177715 prefixEnd_3177715 362598928444919979810769 := by
  unfold tailWord_3177715
  simp only [CollatzResearch.WordTrace]
  refine ⟨115900787682688740359718599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77267191788459160239812399 115900787682688740359718599)
  ·
    refine ⟨173851181524033110539577899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115900787682688740359718599 173851181524033110539577899)
    ·
      refine ⟨260776772286049665809366849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173851181524033110539577899 260776772286049665809366849)
      ·
        refine ⟨195582579214537249357025137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260776772286049665809366849 195582579214537249357025137)
        ·
          refine ⟨146686934410902937017768853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195582579214537249357025137 146686934410902937017768853)
          ·
            refine ⟨6875950050511075172707915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146686934410902937017768853 6875950050511075172707915)
            ·
              refine ⟨10313925075766612759061873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875950050511075172707915 10313925075766612759061873)
              ·
                refine ⟨7735443806824959569296405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10313925075766612759061873 7735443806824959569296405)
                ·
                  refine ⟨362598928444919979810769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7735443806824959569296405 362598928444919979810769)
                  ·
                    rfl

theorem cell22_3177715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 6].length) (baseStart_3177715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177715 prefixEnd_3177715 := by exact prefixLift 3177715
  have htrace : WordTrace (prefixWord ++ tailWord_3177715) baseStart_3177715 baseEnd_3177715 := by
    simpa [prefixWord, tailWord_3177715, baseEnd_3177715] using wordTrace_append hprefix tailTrace_3177715
  have hstable : (prefixWord ++ tailWord_3177715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177715).length < 2 ^ (prefixWord ++ tailWord_3177715).sum := by decide
  have hdescent : baseEnd_3177715 < baseStart_3177715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177745 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_3177745 : Nat := 118140960795 + 3177745 * 2 ^ 59
def prefixEnd_3177745 : Nat := 4983230072969 + 3 ^ 40 * 3177745 * 2
def baseEnd_3177745 : Nat := 1087807054947849861182215

theorem tailTrace_3177745 : CollatzResearch.WordTrace tailWord_3177745 prefixEnd_3177745 1087807054947849861182215 := by
  unfold tailWord_3177745
  simp only [CollatzResearch.WordTrace]
  refine ⟨115901881872580055483310689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77267921248386703655540459 115901881872580055483310689)
  ·
    refine ⟨86926411404435041612483017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115901881872580055483310689 86926411404435041612483017)
    ·
      refine ⟨65194808553326281209362263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86926411404435041612483017 65194808553326281209362263)
      ·
        refine ⟨97792212829989421814043395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65194808553326281209362263 97792212829989421814043395)
        ·
          refine ⟨146688319244984132721065093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97792212829989421814043395 146688319244984132721065093)
          ·
            refine ⟨27504059858434524885199705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146688319244984132721065093 27504059858434524885199705)
            ·
              refine ⟨20628044893825893663899779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27504059858434524885199705 20628044893825893663899779)
              ·
                refine ⟨30942067340738840495849669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20628044893825893663899779 30942067340738840495849669)
                ·
                  refine ⟨5801637626388532592971813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30942067340738840495849669 5801637626388532592971813)
                  ·
                    refine ⟨1087807054947849861182215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5801637626388532592971813 1087807054947849861182215)
                    ·
                      rfl

theorem cell22_3177745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_3177745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177745 prefixEnd_3177745 := by exact prefixLift 3177745
  have htrace : WordTrace (prefixWord ++ tailWord_3177745) baseStart_3177745 baseEnd_3177745 := by
    simpa [prefixWord, tailWord_3177745, baseEnd_3177745] using wordTrace_append hprefix tailTrace_3177745
  have hstable : (prefixWord ++ tailWord_3177745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177745).length < 2 ^ (prefixWord ++ tailWord_3177745).sum := by decide
  have hdescent : baseEnd_3177745 < baseStart_3177745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177777 : List Nat := [1, 2, 2, 3, 3, 1, 4, 6]
def baseStart_3177777 : Nat := 118140960795 + 3177777 * 2 ^ 59
def prefixEnd_3177777 : Nat := 4983230072969 + 3 ^ 40 * 3177777 * 2
def baseEnd_3177777 : Nat := 120868667689090271598013

theorem tailTrace_3177777 : CollatzResearch.WordTrace tailWord_3177777 prefixEnd_3177777 120868667689090271598013 := by
  unfold tailWord_3177777
  simp only [CollatzResearch.WordTrace]
  refine ⟨115903049008464124948475585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77268699338976083298983723 115903049008464124948475585)
  ·
    refine ⟨86927286756348093711356689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115903049008464124948475585 86927286756348093711356689)
    ·
      refine ⟨65195465067261070283517517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86927286756348093711356689 65195465067261070283517517)
      ·
        refine ⟨24448299400222901356319069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65195465067261070283517517 24448299400222901356319069)
        ·
          refine ⟨9168112275083588008619651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24448299400222901356319069 9168112275083588008619651)
          ·
            refine ⟨13752168412625382012929477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168112275083588008619651 13752168412625382012929477)
            ·
              refine ⟨2578531577367259127424277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13752168412625382012929477 2578531577367259127424277)
              ·
                refine ⟨120868667689090271598013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2578531577367259127424277 120868667689090271598013)
                ·
                  rfl

theorem cell22_3177777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 6].length) (baseStart_3177777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177777 prefixEnd_3177777 := by exact prefixLift 3177777
  have htrace : WordTrace (prefixWord ++ tailWord_3177777) baseStart_3177777 baseEnd_3177777 := by
    simpa [prefixWord, tailWord_3177777, baseEnd_3177777] using wordTrace_append hprefix tailTrace_3177777
  have hstable : (prefixWord ++ tailWord_3177777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177777).length < 2 ^ (prefixWord ++ tailWord_3177777).sum := by decide
  have hdescent : baseEnd_3177777 < baseStart_3177777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177850 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_3177850 : Nat := 118140960795 + 3177850 * 2 ^ 59
def prefixEnd_3177850 : Nat := 4983230072969 + 3 ^ 40 * 3177850 * 2
def baseEnd_3177850 : Nat := 362614332864554862435631

theorem tailTrace_3177850 : CollatzResearch.WordTrace tailWord_3177850 prefixEnd_3177850 362614332864554862435631 := by
  unfold tailWord_3177850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28976427884299914603970751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77270474358133105610588669 28976427884299914603970751)
  ·
    refine ⟨43464641826449871905956127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28976427884299914603970751 43464641826449871905956127)
    ·
      refine ⟨65196962739674807858934191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43464641826449871905956127 65196962739674807858934191)
      ·
        refine ⟨97795444109512211788401287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65196962739674807858934191 97795444109512211788401287)
        ·
          refine ⟨146693166164268317682601931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97795444109512211788401287 146693166164268317682601931)
          ·
            refine ⟨220039749246402476523902897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146693166164268317682601931 220039749246402476523902897)
            ·
              refine ⟨165029811934801857392927173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220039749246402476523902897 165029811934801857392927173)
              ·
                refine ⟨30943089737775348261173845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165029811934801857392927173 30943089737775348261173845)
                ·
                  refine ⟨362614332864554862435631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30943089737775348261173845 362614332864554862435631)
                  ·
                    rfl

theorem cell22_3177850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_3177850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177850 prefixEnd_3177850 := by exact prefixLift 3177850
  have htrace : WordTrace (prefixWord ++ tailWord_3177850) baseStart_3177850 baseEnd_3177850 := by
    simpa [prefixWord, tailWord_3177850, baseEnd_3177850] using wordTrace_append hprefix tailTrace_3177850
  have hstable : (prefixWord ++ tailWord_3177850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177850).length < 2 ^ (prefixWord ++ tailWord_3177850).sum := by decide
  have hdescent : baseEnd_3177850 < baseStart_3177850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177901 : List Nat := [1, 5, 2, 2, 1, 1, 1, 5, 4]
def baseStart_3177901 : Nat := 118140960795 + 3177901 * 2 ^ 59
def prefixEnd_3177901 : Nat := 4983230072969 + 3 ^ 40 * 3177901 * 2
def baseEnd_3177901 : Nat := 362620152311972484760579

theorem tailTrace_3177901 : CollatzResearch.WordTrace tailWord_3177901 prefixEnd_3177901 362620152311972484760579 := by
  unfold tailWord_3177901
  simp only [CollatzResearch.WordTrace]
  refine ⟨115907571660014894125989557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77271714440009929417326371 115907571660014894125989557)
  ·
    refine ⟨10866334843126396324311521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115907571660014894125989557 10866334843126396324311521)
    ·
      refine ⟨8149751132344797243233641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10866334843126396324311521 8149751132344797243233641)
      ·
        refine ⟨6112313349258597932425231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8149751132344797243233641 6112313349258597932425231)
        ·
          refine ⟨9168470023887896898637847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112313349258597932425231 9168470023887896898637847)
          ·
            refine ⟨13752705035831845347956771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168470023887896898637847 13752705035831845347956771)
            ·
              refine ⟨20629057553747768021935157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13752705035831845347956771 20629057553747768021935157)
              ·
                refine ⟨1933974145663853252056421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20629057553747768021935157 1933974145663853252056421)
                ·
                  refine ⟨362620152311972484760579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1933974145663853252056421 362620152311972484760579)
                  ·
                    rfl

theorem cell22_3177901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_3177901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177901 prefixEnd_3177901 := by exact prefixLift 3177901
  have htrace : WordTrace (prefixWord ++ tailWord_3177901) baseStart_3177901 baseEnd_3177901 := by
    simpa [prefixWord, tailWord_3177901, baseEnd_3177901] using wordTrace_append hprefix tailTrace_3177901
  have hstable : (prefixWord ++ tailWord_3177901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177901).length < 2 ^ (prefixWord ++ tailWord_3177901).sum := by decide
  have hdescent : baseEnd_3177901 < baseStart_3177901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177916 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_3177916 : Nat := 118140960795 + 3177916 * 2 ^ 59
def prefixEnd_3177916 : Nat := 4983230072969 + 3 ^ 40 * 3177916 * 2
def baseEnd_3177916 : Nat := 1087865591742462415156691

theorem tailTrace_3177916 : CollatzResearch.WordTrace tailWord_3177916 prefixEnd_3177916 1087865591742462415156691 := by
  unfold tailWord_3177916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57954059377480275843892801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77272079169973701125190401 57954059377480275843892801)
  ·
    refine ⟨43465544533110206882919601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57954059377480275843892801 43465544533110206882919601)
    ·
      refine ⟨32599158399832655162189701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43465544533110206882919601 32599158399832655162189701)
      ·
        refine ⟨6112342199968622842910569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32599158399832655162189701 6112342199968622842910569)
        ·
          refine ⟨4584256649976467132182927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6112342199968622842910569 4584256649976467132182927)
          ·
            refine ⟨6876384974964700698274391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584256649976467132182927 6876384974964700698274391)
            ·
              refine ⟨10314577462447051047411587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6876384974964700698274391 10314577462447051047411587)
              ·
                refine ⟨15471866193670576571117381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10314577462447051047411587 15471866193670576571117381)
                ·
                  refine ⟨2900974911313233107084509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15471866193670576571117381 2900974911313233107084509)
                  ·
                    refine ⟨1087865591742462415156691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2900974911313233107084509 1087865591742462415156691)
                    ·
                      rfl

theorem cell22_3177916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_3177916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177916 prefixEnd_3177916 := by exact prefixLift 3177916
  have htrace : WordTrace (prefixWord ++ tailWord_3177916) baseStart_3177916 baseEnd_3177916 := by
    simpa [prefixWord, tailWord_3177916, baseEnd_3177916] using wordTrace_append hprefix tailTrace_3177916
  have hstable : (prefixWord ++ tailWord_3177916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177916).length < 2 ^ (prefixWord ++ tailWord_3177916).sum := by decide
  have hdescent : baseEnd_3177916 < baseStart_3177916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177944 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 3, 3]
def baseStart_3177944 : Nat := 118140960795 + 3177944 * 2 ^ 59
def prefixEnd_3177944 : Nat := 4983230072969 + 3 ^ 40 * 3177944 * 2
def baseEnd_3177944 : Nat := 1087875176714679675456605

theorem tailTrace_3177944 : CollatzResearch.WordTrace tailWord_3177944 prefixEnd_3177944 1087875176714679675456605 := by
  unfold tailWord_3177944
  simp only [CollatzResearch.WordTrace]
  refine ⟨57954569999429556234902443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77272759999239408313203257 57954569999429556234902443)
  ·
    refine ⟨86931854999144334352353665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57954569999429556234902443 86931854999144334352353665)
    ·
      refine ⟨65198891249358250764265249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86931854999144334352353665 65198891249358250764265249)
      ·
        refine ⟨48899168437018688073198937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65198891249358250764265249 48899168437018688073198937)
        ·
          refine ⟨36674376327764016054899203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48899168437018688073198937 36674376327764016054899203)
          ·
            refine ⟨55011564491646024082348805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36674376327764016054899203 55011564491646024082348805)
            ·
              refine ⟨10314668342183629515440401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55011564491646024082348805 10314668342183629515440401)
              ·
                refine ⟨7736001256637722136580301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10314668342183629515440401 7736001256637722136580301)
                ·
                  refine ⟨2901000471239145801217613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7736001256637722136580301 2901000471239145801217613)
                  ·
                    refine ⟨1087875176714679675456605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901000471239145801217613 1087875176714679675456605)
                    ·
                      rfl

theorem cell22_3177944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_3177944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177944 prefixEnd_3177944 := by exact prefixLift 3177944
  have htrace : WordTrace (prefixWord ++ tailWord_3177944) baseStart_3177944 baseEnd_3177944 := by
    simpa [prefixWord, tailWord_3177944, baseEnd_3177944] using wordTrace_append hprefix tailTrace_3177944
  have hstable : (prefixWord ++ tailWord_3177944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177944).length < 2 ^ (prefixWord ++ tailWord_3177944).sum := by decide
  have hdescent : baseEnd_3177944 < baseStart_3177944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177974 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3177974 : Nat := 118140960795 + 3177974 * 2 ^ 59
def prefixEnd_3177974 : Nat := 4983230072969 + 3 ^ 40 * 3177974 * 2
def baseEnd_3177974 : Nat := 362628482109256532402171

theorem tailTrace_3177974 : CollatzResearch.WordTrace tailWord_3177974 prefixEnd_3177974 362628482109256532402171 := by
  unfold tailWord_3177974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244389636796901724587311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77273489459166951728931317 7244389636796901724587311)
  ·
    refine ⟨10866584455195352586880967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7244389636796901724587311 10866584455195352586880967)
    ·
      refine ⟨16299876682793028880321451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10866584455195352586880967 16299876682793028880321451)
      ·
        refine ⟨24449815024189543320482177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16299876682793028880321451 24449815024189543320482177)
        ·
          refine ⟨18337361268142157490361633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24449815024189543320482177 18337361268142157490361633)
          ·
            refine ⟨13753020951106618117771225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18337361268142157490361633 13753020951106618117771225)
            ·
              refine ⟨10314765713329963588328419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13753020951106618117771225 10314765713329963588328419)
              ·
                refine ⟨15472148569994945382492629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10314765713329963588328419 15472148569994945382492629)
                ·
                  refine ⟨362628482109256532402171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15472148569994945382492629 362628482109256532402171)
                  ·
                    rfl

theorem cell22_3177974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3177974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177974 prefixEnd_3177974 := by exact prefixLift 3177974
  have htrace : WordTrace (prefixWord ++ tailWord_3177974) baseStart_3177974 baseEnd_3177974 := by
    simpa [prefixWord, tailWord_3177974, baseEnd_3177974] using wordTrace_append hprefix tailTrace_3177974
  have hstable : (prefixWord ++ tailWord_3177974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177974).length < 2 ^ (prefixWord ++ tailWord_3177974).sum := by decide
  have hdescent : baseEnd_3177974 < baseStart_3177974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177978 : List Nat := [3, 1, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_3177978 : Nat := 118140960795 + 3177978 * 2 ^ 59
def prefixEnd_3177978 : Nat := 4983230072969 + 3 ^ 40 * 3177978 * 2
def baseEnd_3177978 : Nat := 1087886815609514920106501

theorem tailTrace_3177978 : CollatzResearch.WordTrace tailWord_3177978 prefixEnd_3177978 1087886815609514920106501 := by
  unfold tailWord_3177978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28977595020183984069135647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77273586720490624184361725 28977595020183984069135647)
  ·
    refine ⟨43466392530275976103703471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28977595020183984069135647 43466392530275976103703471)
    ·
      refine ⟨65199588795413964155555207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43466392530275976103703471 65199588795413964155555207)
      ·
        refine ⟨97799383193120946233332811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65199588795413964155555207 97799383193120946233332811)
        ·
          refine ⟨146699074789681419349999217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97799383193120946233332811 146699074789681419349999217)
          ·
            refine ⟨110024306092261064512499413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146699074789681419349999217 110024306092261064512499413)
            ·
              refine ⟨2578694674037368699511705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110024306092261064512499413 2578694674037368699511705)
              ·
                refine ⟨1934021005528026524633779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2578694674037368699511705 1934021005528026524633779)
                ·
                  refine ⟨2901031508292039786950669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934021005528026524633779 2901031508292039786950669)
                  ·
                    refine ⟨1087886815609514920106501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901031508292039786950669 1087886815609514920106501)
                    ·
                      rfl

theorem cell22_3177978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_3177978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177978 prefixEnd_3177978 := by exact prefixLift 3177978
  have htrace : WordTrace (prefixWord ++ tailWord_3177978) baseStart_3177978 baseEnd_3177978 := by
    simpa [prefixWord, tailWord_3177978, baseEnd_3177978] using wordTrace_append hprefix tailTrace_3177978
  have hstable : (prefixWord ++ tailWord_3177978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177978).length < 2 ^ (prefixWord ++ tailWord_3177978).sum := by decide
  have hdescent : baseEnd_3177978 < baseStart_3177978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3177991 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 5]
def baseStart_3177991 : Nat := 118140960795 + 3177991 * 2 ^ 59
def prefixEnd_3177991 : Nat := 4983230072969 + 3 ^ 40 * 3177991 * 2
def baseEnd_3177991 : Nat := 362630421925062406510487

theorem tailTrace_3177991 : CollatzResearch.WordTrace tailWord_3177991 prefixEnd_3177991 362630421925062406510487 := by
  unfold tailWord_3177991
  simp only [CollatzResearch.WordTrace]
  refine ⟨115910854229688839496765827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77273902819792559664510551 115910854229688839496765827)
  ·
    refine ⟨173866281344533259245148741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115910854229688839496765827 173866281344533259245148741)
    ·
      refine ⟨32599927752099986108465389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173866281344533259245148741 32599927752099986108465389)
      ·
        refine ⟨12224972907037494790674521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32599927752099986108465389 12224972907037494790674521)
        ·
          refine ⟨9168729680278121093005891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12224972907037494790674521 9168729680278121093005891)
          ·
            refine ⟨13753094520417181639508837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168729680278121093005891 13753094520417181639508837)
            ·
              refine ⟨2578705222578221557407907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13753094520417181639508837 2578705222578221557407907)
              ·
                refine ⟨3868057833867332336111861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578705222578221557407907 3868057833867332336111861)
                ·
                  refine ⟨362630421925062406510487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3868057833867332336111861 362630421925062406510487)
                  ·
                    rfl

theorem cell22_3177991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 5].length) (baseStart_3177991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3177991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3177991 prefixEnd_3177991 := by exact prefixLift 3177991
  have htrace : WordTrace (prefixWord ++ tailWord_3177991) baseStart_3177991 baseEnd_3177991 := by
    simpa [prefixWord, tailWord_3177991, baseEnd_3177991] using wordTrace_append hprefix tailTrace_3177991
  have hstable : (prefixWord ++ tailWord_3177991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3177991).length < 2 ^ (prefixWord ++ tailWord_3177991).sum := by decide
  have hdescent : baseEnd_3177991 < baseStart_3177991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3177991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178032 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_3178032 : Nat := 118140960795 + 3178032 * 2 ^ 59
def prefixEnd_3178032 : Nat := 4983230072969 + 3 ^ 40 * 3178032 * 2
def baseEnd_3178032 : Nat := 1087905300913076779256335

theorem tailTrace_3178032 : CollatzResearch.WordTrace tailWord_3178032 prefixEnd_3178032 1087905300913076779256335 := by
  unfold tailWord_3178032
  simp only [CollatzResearch.WordTrace]
  refine ⟨57956174811270151749504175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77274899748360202332672233 57956174811270151749504175)
  ·
    refine ⟨86934262216905227624256263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57956174811270151749504175 86934262216905227624256263)
    ·
      refine ⟨130401393325357841436384395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86934262216905227624256263 130401393325357841436384395)
      ·
        refine ⟨195602089988036762154576593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130401393325357841436384395 195602089988036762154576593)
        ·
          refine ⟨146701567491027571615932445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195602089988036762154576593 146701567491027571615932445)
          ·
            refine ⟨55013087809135339355974667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146701567491027571615932445 55013087809135339355974667)
            ·
              refine ⟨82519631713703009033962001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55013087809135339355974667 82519631713703009033962001)
              ·
                refine ⟨61889723785277256775471501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82519631713703009033962001 61889723785277256775471501)
                ·
                  refine ⟨23208646419478971290801813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61889723785277256775471501 23208646419478971290801813)
                  ·
                    refine ⟨1087905300913076779256335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23208646419478971290801813 1087905300913076779256335)
                    ·
                      rfl

theorem cell22_3178032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_3178032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178032 prefixEnd_3178032 := by exact prefixLift 3178032
  have htrace : WordTrace (prefixWord ++ tailWord_3178032) baseStart_3178032 baseEnd_3178032 := by
    simpa [prefixWord, tailWord_3178032, baseEnd_3178032] using wordTrace_append hprefix tailTrace_3178032
  have hstable : (prefixWord ++ tailWord_3178032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178032).length < 2 ^ (prefixWord ++ tailWord_3178032).sum := by decide
  have hdescent : baseEnd_3178032 < baseStart_3178032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178049 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3178049 : Nat := 118140960795 + 3178049 * 2 ^ 59
def prefixEnd_3178049 : Nat := 4983230072969 + 3 ^ 40 * 3178049 * 2
def baseEnd_3178049 : Nat := 1087911120360494401581283

theorem tailTrace_3178049 : CollatzResearch.WordTrace tailWord_3178049 prefixEnd_3178049 1087911120360494401581283 := by
  unfold tailWord_3178049
  simp only [CollatzResearch.WordTrace]
  refine ⟨115912969663478715402377201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77275313108985810268251467 115912969663478715402377201)
  ·
    refine ⟨86934727247609036551782901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115912969663478715402377201 86934727247609036551782901)
    ·
      refine ⟨8150130679463347176729647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86934727247609036551782901 8150130679463347176729647)
      ·
        refine ⟨12225196019195020765094471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8150130679463347176729647 12225196019195020765094471)
        ·
          refine ⟨18337794028792531147641707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12225196019195020765094471 18337794028792531147641707)
          ·
            refine ⟨27506691043188796721462561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18337794028792531147641707 27506691043188796721462561)
            ·
              refine ⟨20630018282391597541096921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27506691043188796721462561 20630018282391597541096921)
              ·
                refine ⟨15472513711793698155822691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20630018282391597541096921 15472513711793698155822691)
                ·
                  refine ⟨23208770567690547233734037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15472513711793698155822691 23208770567690547233734037)
                  ·
                    refine ⟨1087911120360494401581283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23208770567690547233734037 1087911120360494401581283)
                    ·
                      rfl

theorem cell22_3178049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3178049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178049 prefixEnd_3178049 := by exact prefixLift 3178049
  have htrace : WordTrace (prefixWord ++ tailWord_3178049) baseStart_3178049 baseEnd_3178049 := by
    simpa [prefixWord, tailWord_3178049, baseEnd_3178049] using wordTrace_append hprefix tailTrace_3178049
  have hstable : (prefixWord ++ tailWord_3178049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178049).length < 2 ^ (prefixWord ++ tailWord_3178049).sum := by decide
  have hdescent : baseEnd_3178049 < baseStart_3178049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178064 : List Nat := [2, 1, 1, 1, 1, 3, 7, 6]
def baseStart_3178064 : Nat := 118140960795 + 3178064 * 2 ^ 59
def prefixEnd_3178064 : Nat := 4983230072969 + 3 ^ 40 * 3178064 * 2
def baseEnd_3178064 : Nat := 120879583907448818050693

theorem tailTrace_3178064 : CollatzResearch.WordTrace tailWord_3178064 prefixEnd_3178064 120879583907448818050693 := by
  unfold tailWord_3178064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57956758379212186482086623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77275677838949581976115497 57956758379212186482086623)
  ·
    refine ⟨86935137568818279723129935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57956758379212186482086623 86935137568818279723129935)
    ·
      refine ⟨130402706353227419584694903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86935137568818279723129935 130402706353227419584694903)
      ·
        refine ⟨195604059529841129377042355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130402706353227419584694903 195604059529841129377042355)
        ·
          refine ⟨293406089294761694065563533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195604059529841129377042355 293406089294761694065563533)
          ·
            refine ⟨110027283485535635274586325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293406089294761694065563533 110027283485535635274586325)
            ·
              refine ⟨2578764456692241451748117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110027283485535635274586325 2578764456692241451748117)
              ·
                refine ⟨120879583907448818050693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2578764456692241451748117 120879583907448818050693)
                ·
                  rfl

theorem cell22_3178064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 6].length) (baseStart_3178064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178064 prefixEnd_3178064 := by exact prefixLift 3178064
  have htrace : WordTrace (prefixWord ++ tailWord_3178064) baseStart_3178064 baseEnd_3178064 := by
    simpa [prefixWord, tailWord_3178064, baseEnd_3178064] using wordTrace_append hprefix tailTrace_3178064
  have hstable : (prefixWord ++ tailWord_3178064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178064).length < 2 ^ (prefixWord ++ tailWord_3178064).sum := by decide
  have hdescent : baseEnd_3178064 < baseStart_3178064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178066 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3178066 : Nat := 118140960795 + 3178066 * 2 ^ 59
def prefixEnd_3178066 : Nat := 4983230072969 + 3 ^ 40 * 3178066 * 2
def baseEnd_3178066 : Nat := 1087916939807912023906231

theorem tailTrace_3178066 : CollatzResearch.WordTrace tailWord_3178066 prefixEnd_3178066 1087916939807912023906231 := by
  unfold tailWord_3178066
  simp only [CollatzResearch.WordTrace]
  refine ⟨28978397426104281826436513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77275726469611418203830701 28978397426104281826436513)
  ·
    refine ⟨21733798069578211369827385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28978397426104281826436513 21733798069578211369827385)
    ·
      refine ⟨16300348552183658527370539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21733798069578211369827385 16300348552183658527370539)
      ·
        refine ⟨24450522828275487791055809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16300348552183658527370539 24450522828275487791055809)
        ·
          refine ⟨18337892121206615843291857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24450522828275487791055809 18337892121206615843291857)
          ·
            refine ⟨13753419090904961882468893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18337892121206615843291857 13753419090904961882468893)
            ·
              refine ⟨5157532159089360705925835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13753419090904961882468893 5157532159089360705925835)
              ·
                refine ⟨7736298238634041058888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157532159089360705925835 7736298238634041058888753)
                ·
                  refine ⟨5802223678975530794166565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736298238634041058888753 5802223678975530794166565)
                  ·
                    refine ⟨1087916939807912023906231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5802223678975530794166565 1087916939807912023906231)
                    ·
                      rfl

theorem cell22_3178066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3178066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178066 prefixEnd_3178066 := by exact prefixLift 3178066
  have htrace : WordTrace (prefixWord ++ tailWord_3178066) baseStart_3178066 baseEnd_3178066 := by
    simpa [prefixWord, tailWord_3178066, baseEnd_3178066] using wordTrace_append hprefix tailTrace_3178066
  have hstable : (prefixWord ++ tailWord_3178066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178066).length < 2 ^ (prefixWord ++ tailWord_3178066).sum := by decide
  have hdescent : baseEnd_3178066 < baseStart_3178066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178096 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 3, 3]
def baseStart_3178096 : Nat := 118140960795 + 3178096 * 2 ^ 59
def prefixEnd_3178096 : Nat := 4983230072969 + 3 ^ 40 * 3178096 * 2
def baseEnd_3178096 : Nat := 1087927209421001945656139

theorem tailTrace_3178096 : CollatzResearch.WordTrace tailWord_3178096 prefixEnd_3178096 1087927209421001945656139 := by
  unfold tailWord_3178096
  simp only [CollatzResearch.WordTrace]
  refine ⟨57957341947154221214669071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77276455929538961619558761 57957341947154221214669071)
  ·
    refine ⟨86936012920731331822003607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57957341947154221214669071 86936012920731331822003607)
    ·
      refine ⟨130404019381096997733005411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86936012920731331822003607 130404019381096997733005411)
      ·
        refine ⟨195606029071645496599508117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130404019381096997733005411 195606029071645496599508117)
        ·
          refine ⟨9169032612733382653101943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195606029071645496599508117 9169032612733382653101943)
          ·
            refine ⟨13753548919100073979652915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169032612733382653101943 13753548919100073979652915)
            ·
              refine ⟨20630323378650110969479373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13753548919100073979652915 20630323378650110969479373)
              ·
                refine ⟨7736371266993791613554765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20630323378650110969479373 7736371266993791613554765)
                ·
                  refine ⟨2901139225122671855083037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7736371266993791613554765 2901139225122671855083037)
                  ·
                    refine ⟨1087927209421001945656139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901139225122671855083037 1087927209421001945656139)
                    ·
                      rfl

theorem cell22_3178096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_3178096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178096 prefixEnd_3178096 := by exact prefixLift 3178096
  have htrace : WordTrace (prefixWord ++ tailWord_3178096) baseStart_3178096 baseEnd_3178096 := by
    simpa [prefixWord, tailWord_3178096, baseEnd_3178096] using wordTrace_append hprefix tailTrace_3178096
  have hstable : (prefixWord ++ tailWord_3178096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178096).length < 2 ^ (prefixWord ++ tailWord_3178096).sum := by decide
  have hdescent : baseEnd_3178096 < baseStart_3178096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178198 : List Nat := [5, 2, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3178198 : Nat := 118140960795 + 3178198 * 2 ^ 59
def prefixEnd_3178198 : Nat := 4983230072969 + 3 ^ 40 * 3178198 * 2
def baseEnd_3178198 : Nat := 1087962126105507679605827

theorem tailTrace_3178198 : CollatzResearch.WordTrace tailWord_3178198 prefixEnd_3178198 1087962126105507679605827 := by
  unfold tailWord_3178198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244900258746182115596953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77278936093292609233034165 7244900258746182115596953)
  ·
    refine ⟨5433675194059636586697715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7244900258746182115596953 5433675194059636586697715)
    ·
      refine ⟨8150512791089454880046573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5433675194059636586697715 8150512791089454880046573)
      ·
        refine ⟨3056442296658545580017465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8150512791089454880046573 3056442296658545580017465)
        ·
          refine ⟨2292331722493909185013099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3056442296658545580017465 2292331722493909185013099)
          ·
            refine ⟨3438497583740863777519649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292331722493909185013099 3438497583740863777519649)
            ·
              refine ⟨2578873187805647833139737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3438497583740863777519649 2578873187805647833139737)
              ·
                refine ⟨1934154890854235874854803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2578873187805647833139737 1934154890854235874854803)
                ·
                  refine ⟨2901232336281353812282205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934154890854235874854803 2901232336281353812282205)
                  ·
                    refine ⟨1087962126105507679605827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901232336281353812282205 1087962126105507679605827)
                    ·
                      rfl

theorem cell22_3178198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3178198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178198 prefixEnd_3178198 := by exact prefixLift 3178198
  have htrace : WordTrace (prefixWord ++ tailWord_3178198) baseStart_3178198 baseEnd_3178198 := by
    simpa [prefixWord, tailWord_3178198, baseEnd_3178198] using wordTrace_append hprefix tailTrace_3178198
  have hstable : (prefixWord ++ tailWord_3178198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178198).length < 2 ^ (prefixWord ++ tailWord_3178198).sum := by decide
  have hdescent : baseEnd_3178198 < baseStart_3178198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178201 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_3178201 : Nat := 118140960795 + 3178201 * 2 ^ 59
def prefixEnd_3178201 : Nat := 4983230072969 + 3 ^ 40 * 3178201 * 2
def baseEnd_3178201 : Nat := 1087963153066816671780817

theorem tailTrace_3178201 : CollatzResearch.WordTrace tailWord_3178201 prefixEnd_3178201 1087963153066816671780817 := by
  unfold tailWord_3178201
  simp only [CollatzResearch.WordTrace]
  refine ⟨115918513558928045361910457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77279009039285363574606971 115918513558928045361910457)
  ·
    refine ⟨86938885169196034021432843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115918513558928045361910457 86938885169196034021432843)
    ·
      refine ⟨130408327753794051032149265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86938885169196034021432843 130408327753794051032149265)
      ·
        refine ⟨97806245815345538274111949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130408327753794051032149265 97806245815345538274111949)
        ·
          refine ⟨36677342180754576852791981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97806245815345538274111949 36677342180754576852791981)
          ·
            refine ⟨13754003317782966319796993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36677342180754576852791981 13754003317782966319796993)
            ·
              refine ⟨10315502488337224739847745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13754003317782966319796993 10315502488337224739847745)
              ·
                refine ⟨7736626866252918554885809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10315502488337224739847745 7736626866252918554885809)
                ·
                  refine ⟨5802470149689688916164357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736626866252918554885809 5802470149689688916164357)
                  ·
                    refine ⟨1087963153066816671780817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5802470149689688916164357 1087963153066816671780817)
                    ·
                      rfl

theorem cell22_3178201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_3178201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178201 prefixEnd_3178201 := by exact prefixLift 3178201
  have htrace : WordTrace (prefixWord ++ tailWord_3178201) baseStart_3178201 baseEnd_3178201 := by
    simpa [prefixWord, tailWord_3178201, baseEnd_3178201] using wordTrace_append hprefix tailTrace_3178201
  have hstable : (prefixWord ++ tailWord_3178201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178201).length < 2 ^ (prefixWord ++ tailWord_3178201).sum := by decide
  have hdescent : baseEnd_3178201 < baseStart_3178201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178216 : List Nat := [2, 1, 4, 1, 3, 1, 3, 7]
def baseStart_3178216 : Nat := 118140960795 + 3178216 * 2 ^ 59
def prefixEnd_3178216 : Nat := 4983230072969 + 3 ^ 40 * 3178216 * 2
def baseEnd_3178216 : Nat := 120885365319262403628419

theorem tailTrace_3178216 : CollatzResearch.WordTrace tailWord_3178216 prefixEnd_3178216 120885365319262403628419 := by
  unfold tailWord_3178216
  simp only [CollatzResearch.WordTrace]
  refine ⟨57959530326936851461853251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77279373769249135282471001 57959530326936851461853251)
  ·
    refine ⟨86939295490405277192779877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57959530326936851461853251 86939295490405277192779877)
    ·
      refine ⟨16301117904450989473646227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86939295490405277192779877 16301117904450989473646227)
      ·
        refine ⟨24451676856676484210469341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16301117904450989473646227 24451676856676484210469341)
        ·
          refine ⟨9169378821253681578926003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24451676856676484210469341 9169378821253681578926003)
          ·
            refine ⟨13754068231880522368389005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169378821253681578926003 13754068231880522368389005)
            ·
              refine ⟨5157775586955195888145877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13754068231880522368389005 5157775586955195888145877)
              ·
                refine ⟨120885365319262403628419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5157775586955195888145877 120885365319262403628419)
                ·
                  rfl

theorem cell22_3178216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_3178216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178216 prefixEnd_3178216 := by exact prefixLift 3178216
  have htrace : WordTrace (prefixWord ++ tailWord_3178216) baseStart_3178216 baseEnd_3178216 := by
    simpa [prefixWord, tailWord_3178216, baseEnd_3178216] using wordTrace_append hprefix tailTrace_3178216
  have hstable : (prefixWord ++ tailWord_3178216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178216).length < 2 ^ (prefixWord ++ tailWord_3178216).sum := by decide
  have hdescent : baseEnd_3178216 < baseStart_3178216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178231 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 5, 3]
def baseStart_3178231 : Nat := 118140960795 + 3178231 * 2 ^ 59
def prefixEnd_3178231 : Nat := 4983230072969 + 3 ^ 40 * 3178231 * 2
def baseEnd_3178231 : Nat := 1087973422679906593530725

theorem tailTrace_3178231 : CollatzResearch.WordTrace tailWord_3178231 prefixEnd_3178231 1087973422679906593530725 := by
  unfold tailWord_3178231
  simp only [CollatzResearch.WordTrace]
  refine ⟨115919607748819360485502547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77279738499212906990335031 115919607748819360485502547)
  ·
    refine ⟨173879411623229040728253821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115919607748819360485502547 173879411623229040728253821)
    ·
      refine ⟨65204779358710890273095183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173879411623229040728253821 65204779358710890273095183)
      ·
        refine ⟨97807169038066335409642775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65204779358710890273095183 97807169038066335409642775)
        ·
          refine ⟨146710753557099503114464163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97807169038066335409642775 146710753557099503114464163)
          ·
            refine ⟨220066130335649254671696245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146710753557099503114464163 220066130335649254671696245)
            ·
              refine ⟨20631199718967117625471523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220066130335649254671696245 20631199718967117625471523)
              ·
                refine ⟨30946799578450676438207285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20631199718967117625471523 30946799578450676438207285)
                ·
                  refine ⟨2901262460479750916081933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30946799578450676438207285 2901262460479750916081933)
                  ·
                    refine ⟨1087973422679906593530725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901262460479750916081933 1087973422679906593530725)
                    ·
                      rfl

theorem cell22_3178231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_3178231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178231 prefixEnd_3178231 := by exact prefixLift 3178231
  have htrace : WordTrace (prefixWord ++ tailWord_3178231) baseStart_3178231 baseEnd_3178231 := by
    simpa [prefixWord, tailWord_3178231, baseEnd_3178231] using wordTrace_append hprefix tailTrace_3178231
  have hstable : (prefixWord ++ tailWord_3178231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178231).length < 2 ^ (prefixWord ++ tailWord_3178231).sum := by decide
  have hdescent : baseEnd_3178231 < baseStart_3178231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178261 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 7]
def baseStart_3178261 : Nat := 118140960795 + 3178261 * 2 ^ 59
def prefixEnd_3178261 : Nat := 4983230072969 + 3 ^ 40 * 3178261 * 2
def baseEnd_3178261 : Nat := 362661230764332171760211

theorem tailTrace_3178261 : CollatzResearch.WordTrace tailWord_3178261 prefixEnd_3178261 362661230764332171760211 := by
  unfold tailWord_3178261
  simp only [CollatzResearch.WordTrace]
  refine ⟨115920701938710675609094637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77280467959140450406063091 115920701938710675609094637)
  ·
    refine ⟨43470263227016503353410489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115920701938710675609094637 43470263227016503353410489)
    ·
      refine ⟨32602697420262377515057867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43470263227016503353410489 32602697420262377515057867)
      ·
        refine ⟨48904046130393566272586801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32602697420262377515057867 48904046130393566272586801)
        ·
          refine ⟨36678034597795174704440101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48904046130393566272586801 36678034597795174704440101)
          ·
            refine ⟨6877131487086595257082519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36678034597795174704440101 6877131487086595257082519)
            ·
              refine ⟨10315697230629892885623779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877131487086595257082519 10315697230629892885623779)
              ·
                refine ⟨15473545845944839328435669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10315697230629892885623779 15473545845944839328435669)
                ·
                  refine ⟨362661230764332171760211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15473545845944839328435669 362661230764332171760211)
                  ·
                    rfl

theorem cell22_3178261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_3178261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178261 prefixEnd_3178261 := by exact prefixLift 3178261
  have htrace : WordTrace (prefixWord ++ tailWord_3178261) baseStart_3178261 baseEnd_3178261 := by
    simpa [prefixWord, tailWord_3178261, baseEnd_3178261] using wordTrace_append hprefix tailTrace_3178261
  have hstable : (prefixWord ++ tailWord_3178261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178261).length < 2 ^ (prefixWord ++ tailWord_3178261).sum := by decide
  have hdescent : baseEnd_3178261 < baseStart_3178261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178353 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_3178353 : Nat := 118140960795 + 3178353 * 2 ^ 59
def prefixEnd_3178353 : Nat := 4983230072969 + 3 ^ 40 * 3178353 * 2
def baseEnd_3178353 : Nat := 1088015185773138941980351

theorem tailTrace_3178353 : CollatzResearch.WordTrace tailWord_3178353 prefixEnd_3178353 1088015185773138941980351 := by
  unfold tailWord_3178353
  simp only [CollatzResearch.WordTrace]
  refine ⟨115924057454377375321443713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77282704969584916880962475 115924057454377375321443713)
  ·
    refine ⟨86943043090783031491082785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115924057454377375321443713 86943043090783031491082785)
    ·
      refine ⟨65207282318087273618312089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86943043090783031491082785 65207282318087273618312089)
      ·
        refine ⟨48905461738565455213734067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65207282318087273618312089 48905461738565455213734067)
        ·
          refine ⟨73358192607848182820601101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48905461738565455213734067 73358192607848182820601101)
          ·
            refine ⟨27509322227943068557725413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73358192607848182820601101 27509322227943068557725413)
            ·
              refine ⟨5157997917739325354573515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27509322227943068557725413 5157997917739325354573515)
              ·
                refine ⟨7736996876608988031860273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157997917739325354573515 7736996876608988031860273)
                ·
                  refine ⟨5802747657456741023895205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736996876608988031860273 5802747657456741023895205)
                  ·
                    refine ⟨1088015185773138941980351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5802747657456741023895205 1088015185773138941980351)
                    ·
                      rfl

theorem cell22_3178353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_3178353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178353 prefixEnd_3178353 := by exact prefixLift 3178353
  have htrace : WordTrace (prefixWord ++ tailWord_3178353) baseStart_3178353 baseEnd_3178353 := by
    simpa [prefixWord, tailWord_3178353, baseEnd_3178353] using wordTrace_append hprefix tailTrace_3178353
  have hstable : (prefixWord ++ tailWord_3178353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178353).length < 2 ^ (prefixWord ++ tailWord_3178353).sum := by decide
  have hdescent : baseEnd_3178353 < baseStart_3178353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178411 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 6, 5]
def baseStart_3178411 : Nat := 118140960795 + 3178411 * 2 ^ 59
def prefixEnd_3178411 : Nat := 4983230072969 + 3 ^ 40 * 3178411 * 2
def baseEnd_3178411 : Nat := 1088035040358446124030173

theorem tailTrace_3178411 : CollatzResearch.WordTrace tailWord_3178411 prefixEnd_3178411 1088035040358446124030173 := by
  unfold tailWord_3178411
  simp only [CollatzResearch.WordTrace]
  refine ⟨115926172888167251227055087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77284115258778167484703391 115926172888167251227055087)
  ·
    refine ⟨173889259332250876840582631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115926172888167251227055087 173889259332250876840582631)
    ·
      refine ⟨260833888998376315260873947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173889259332250876840582631 260833888998376315260873947)
      ·
        refine ⟨391250833497564472891310921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260833888998376315260873947 391250833497564472891310921)
        ·
          refine ⟨293438125123173354668483191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391250833497564472891310921 293438125123173354668483191)
          ·
            refine ⟨440157187684760032002724787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293438125123173354668483191 440157187684760032002724787)
            ·
              refine ⟨660235781527140048004087181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440157187684760032002724787 660235781527140048004087181)
              ·
                refine ⟨247588418072677518001532693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660235781527140048004087181 247588418072677518001532693)
                ·
                  refine ⟨11605707097156758656321845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247588418072677518001532693 11605707097156758656321845)
                  ·
                    refine ⟨1088035040358446124030173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11605707097156758656321845 1088035040358446124030173)
                    ·
                      rfl

theorem cell22_3178411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_3178411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178411 prefixEnd_3178411 := by exact prefixLift 3178411
  have htrace : WordTrace (prefixWord ++ tailWord_3178411) baseStart_3178411 baseEnd_3178411 := by
    simpa [prefixWord, tailWord_3178411, baseEnd_3178411] using wordTrace_append hprefix tailTrace_3178411
  have hstable : (prefixWord ++ tailWord_3178411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178411).length < 2 ^ (prefixWord ++ tailWord_3178411).sum := by decide
  have hdescent : baseEnd_3178411 < baseStart_3178411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178417 : List Nat := [1, 2, 2, 4, 2, 1, 1, 5, 1, 3]
def baseStart_3178417 : Nat := 118140960795 + 3178417 * 2 ^ 59
def prefixEnd_3178417 : Nat := 4983230072969 + 3 ^ 40 * 3178417 * 2
def baseEnd_3178417 : Nat := 1088037094281064108380155

theorem tailTrace_3178417 : CollatzResearch.WordTrace tailWord_3178417 prefixEnd_3178417 1088037094281064108380155 := by
  unfold tailWord_3178417
  simp only [CollatzResearch.WordTrace]
  refine ⟨115926391726145514251773505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77284261150763676167849003 115926391726145514251773505)
  ·
    refine ⟨86944793794609135688830129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115926391726145514251773505 86944793794609135688830129)
    ·
      refine ⟨65208595345956851766622597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86944793794609135688830129 65208595345956851766622597)
      ·
        refine ⟨12226611627366909706241737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65208595345956851766622597 12226611627366909706241737)
        ·
          refine ⟨9169958720525182279681303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12226611627366909706241737 9169958720525182279681303)
          ·
            refine ⟨13754938080787773419521955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169958720525182279681303 13754938080787773419521955)
            ·
              refine ⟨20632407121181660129282933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13754938080787773419521955 20632407121181660129282933)
              ·
                refine ⟨1934288167610780637120275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20632407121181660129282933 1934288167610780637120275)
                ·
                  refine ⟨2901432251416170955680413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934288167610780637120275 2901432251416170955680413)
                  ·
                    refine ⟨1088037094281064108380155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901432251416170955680413 1088037094281064108380155)
                    ·
                      rfl

theorem cell22_3178417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_3178417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178417 prefixEnd_3178417 := by exact prefixLift 3178417
  have htrace : WordTrace (prefixWord ++ tailWord_3178417) baseStart_3178417 baseEnd_3178417 := by
    simpa [prefixWord, tailWord_3178417, baseEnd_3178417] using wordTrace_append hprefix tailTrace_3178417
  have hstable : (prefixWord ++ tailWord_3178417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178417).length < 2 ^ (prefixWord ++ tailWord_3178417).sum := by decide
  have hdescent : baseEnd_3178417 < baseStart_3178417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178430 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_3178430 : Nat := 118140960795 + 3178430 * 2 ^ 59
def prefixEnd_3178430 : Nat := 4983230072969 + 3 ^ 40 * 3178430 * 2
def baseEnd_3178430 : Nat := 362680514815578802601705

theorem tailTrace_3178430 : CollatzResearch.WordTrace tailWord_3178430 prefixEnd_3178430 362680514815578802601705 := by
  unfold tailWord_3178430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14490858234387302183999593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77284577250065611647997829 14490858234387302183999593)
  ·
    refine ⟨10868143675790476637999695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14490858234387302183999593 10868143675790476637999695)
    ·
      refine ⟨16302215513685714956999543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10868143675790476637999695 16302215513685714956999543)
      ·
        refine ⟨24453323270528572435499315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16302215513685714956999543 24453323270528572435499315)
        ·
          refine ⟨36679984905792858653248973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24453323270528572435499315 36679984905792858653248973)
          ·
            refine ⟨13754994339672321994968365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36679984905792858653248973 13754994339672321994968365)
            ·
              refine ⟨5158122877377120748113137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13754994339672321994968365 5158122877377120748113137)
              ·
                refine ⟨3868592158032840561084853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5158122877377120748113137 3868592158032840561084853)
                ·
                  refine ⟨362680514815578802601705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3868592158032840561084853 362680514815578802601705)
                  ·
                    rfl

theorem cell22_3178430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_3178430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178430 prefixEnd_3178430 := by exact prefixLift 3178430
  have htrace : WordTrace (prefixWord ++ tailWord_3178430) baseStart_3178430 baseEnd_3178430 := by
    simpa [prefixWord, tailWord_3178430, baseEnd_3178430] using wordTrace_append hprefix tailTrace_3178430
  have hstable : (prefixWord ++ tailWord_3178430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178430).length < 2 ^ (prefixWord ++ tailWord_3178430).sum := by decide
  have hdescent : baseEnd_3178430 < baseStart_3178430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178441 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 10]
def baseStart_3178441 : Nat := 118140960795 + 3178441 * 2 ^ 59
def prefixEnd_3178441 : Nat := 4983230072969 + 3 ^ 40 * 3178441 * 2
def baseEnd_3178441 : Nat := 362681769990512015260027

theorem tailTrace_3178441 : CollatzResearch.WordTrace tailWord_3178441 prefixEnd_3178441 362681769990512015260027 := by
  unfold tailWord_3178441
  simp only [CollatzResearch.WordTrace]
  refine ⟨115927267078058566350647177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77284844718705710900431451 115927267078058566350647177)
  ·
    refine ⟨86945450308543924762985383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115927267078058566350647177 86945450308543924762985383)
    ·
      refine ⟨130418175462815887144478075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86945450308543924762985383 130418175462815887144478075)
      ·
        refine ⟨195627263194223830716717113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130418175462815887144478075 195627263194223830716717113)
        ·
          refine ⟨146720447395667873037537835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195627263194223830716717113 146720447395667873037537835)
          ·
            refine ⟨220080671093501809556306753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146720447395667873037537835 220080671093501809556306753)
            ·
              refine ⟨165060503320126357167230065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220080671093501809556306753 165060503320126357167230065)
              ·
                refine ⟨123795377490094767875422549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165060503320126357167230065 123795377490094767875422549)
                ·
                  refine ⟨362681769990512015260027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123795377490094767875422549 362681769990512015260027)
                  ·
                    rfl

theorem cell22_3178441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_3178441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178441 prefixEnd_3178441 := by exact prefixLift 3178441
  have htrace : WordTrace (prefixWord ++ tailWord_3178441) baseStart_3178441 baseEnd_3178441 := by
    simpa [prefixWord, tailWord_3178441, baseEnd_3178441] using wordTrace_append hprefix tailTrace_3178441
  have hstable : (prefixWord ++ tailWord_3178441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178441).length < 2 ^ (prefixWord ++ tailWord_3178441).sum := by decide
  have hdescent : baseEnd_3178441 < baseStart_3178441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178488 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_3178488 : Nat := 118140960795 + 3178488 * 2 ^ 59
def prefixEnd_3178488 : Nat := 4983230072969 + 3 ^ 40 * 3178488 * 2
def baseEnd_3178488 : Nat := 1088061399032043589854937

theorem tailTrace_3178488 : CollatzResearch.WordTrace tailWord_3178488 prefixEnd_3178488 1088061399032043589854937 := by
  unfold tailWord_3178488
  simp only [CollatzResearch.WordTrace]
  refine ⟨57964490654444146688804059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77285987539258862251738745 57964490654444146688804059)
  ·
    refine ⟨86946735981666220033206089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57964490654444146688804059 86946735981666220033206089)
    ·
      refine ⟨65210051986249665024904567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86946735981666220033206089 65210051986249665024904567)
      ·
        refine ⟨97815077979374497537356851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65210051986249665024904567 97815077979374497537356851)
        ·
          refine ⟨146722616969061746306035277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97815077979374497537356851 146722616969061746306035277)
          ·
            refine ⟨55020981363398154864763229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146722616969061746306035277 55020981363398154864763229)
            ·
              refine ⟨20632868011274308074286211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55020981363398154864763229 20632868011274308074286211)
              ·
                refine ⟨30949302016911462111429317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20632868011274308074286211 30949302016911462111429317)
                ·
                  refine ⟨5802994128170899145892997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30949302016911462111429317 5802994128170899145892997)
                  ·
                    refine ⟨1088061399032043589854937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5802994128170899145892997 1088061399032043589854937)
                    ·
                      rfl

theorem cell22_3178488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_3178488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178488 prefixEnd_3178488 := by exact prefixLift 3178488
  have htrace : WordTrace (prefixWord ++ tailWord_3178488) baseStart_3178488 baseEnd_3178488 := by
    simpa [prefixWord, tailWord_3178488, baseEnd_3178488] using wordTrace_append hprefix tailTrace_3178488
  have hstable : (prefixWord ++ tailWord_3178488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178488).length < 2 ^ (prefixWord ++ tailWord_3178488).sum := by decide
  have hdescent : baseEnd_3178488 < baseStart_3178488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178492 : List Nat := [2, 2, 2, 1, 2, 2, 5, 2, 4]
def baseStart_3178492 : Nat := 118140960795 + 3178492 * 2 ^ 59
def prefixEnd_3178492 : Nat := 4983230072969 + 3 ^ 40 * 3178492 * 2
def baseEnd_3178492 : Nat := 362687589437929637584975

theorem tailTrace_3178492 : CollatzResearch.WordTrace tailWord_3178492 prefixEnd_3178492 362687589437929637584975 := by
  unfold tailWord_3178492
  simp only [CollatzResearch.WordTrace]
  refine ⟨57964563600436901030376865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77286084800582534707169153 57964563600436901030376865)
  ·
    refine ⟨43473422700327675772782649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57964563600436901030376865 43473422700327675772782649)
    ·
      refine ⟨32605067025245756829586987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43473422700327675772782649 32605067025245756829586987)
      ·
        refine ⟨48907600537868635244380481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32605067025245756829586987 48907600537868635244380481)
        ·
          refine ⟨36680700403401476433285361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48907600537868635244380481 36680700403401476433285361)
          ·
            refine ⟨27510525302551107324964021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36680700403401476433285361 27510525302551107324964021)
            ·
              refine ⟨2579111747114166311715377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27510525302551107324964021 2579111747114166311715377)
              ·
                refine ⟨1934333810335624733786533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2579111747114166311715377 1934333810335624733786533)
                ·
                  refine ⟨362687589437929637584975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934333810335624733786533 362687589437929637584975)
                  ·
                    rfl

theorem cell22_3178492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_3178492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178492 prefixEnd_3178492 := by exact prefixLift 3178492
  have htrace : WordTrace (prefixWord ++ tailWord_3178492) baseStart_3178492 baseEnd_3178492 := by
    simpa [prefixWord, tailWord_3178492, baseEnd_3178492] using wordTrace_append hprefix tailTrace_3178492
  have hstable : (prefixWord ++ tailWord_3178492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178492).length < 2 ^ (prefixWord ++ tailWord_3178492).sum := by decide
  have hdescent : baseEnd_3178492 < baseStart_3178492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178503 : List Nat := [1, 1, 4, 3, 1, 2, 1, 9]
def baseStart_3178503 : Nat := 118140960795 + 3178503 * 2 ^ 59
def prefixEnd_3178503 : Nat := 4983230072969 + 3 ^ 40 * 3178503 * 2
def baseEnd_3178503 : Nat := 120896281537620950081099

theorem tailTrace_3178503 : CollatzResearch.WordTrace tailWord_3178503 prefixEnd_3178503 120896281537620950081099 := by
  unfold tailWord_3178503
  simp only [CollatzResearch.WordTrace]
  refine ⟨115929528403833950939404163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77286352269222633959602775 115929528403833950939404163)
  ·
    refine ⟨173894292605750926409106245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115929528403833950939404163 173894292605750926409106245)
    ·
      refine ⟨32605179863578298701707421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173894292605750926409106245 32605179863578298701707421)
      ·
        refine ⟨12226942448841862013140283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32605179863578298701707421 12226942448841862013140283)
        ·
          refine ⟨18340413673262793019710425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12226942448841862013140283 18340413673262793019710425)
          ·
            refine ⟨13755310254947094764782819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18340413673262793019710425 13755310254947094764782819)
            ·
              refine ⟨20632965382420642147174229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13755310254947094764782819 20632965382420642147174229)
              ·
                refine ⟨120896281537620950081099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20632965382420642147174229 120896281537620950081099)
                ·
                  rfl

theorem cell22_3178503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 9].length) (baseStart_3178503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178503 prefixEnd_3178503 := by exact prefixLift 3178503
  have htrace : WordTrace (prefixWord ++ tailWord_3178503) baseStart_3178503 baseEnd_3178503 := by
    simpa [prefixWord, tailWord_3178503, baseEnd_3178503] using wordTrace_append hprefix tailTrace_3178503
  have hstable : (prefixWord ++ tailWord_3178503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178503).length < 2 ^ (prefixWord ++ tailWord_3178503).sum := by decide
  have hdescent : baseEnd_3178503 < baseStart_3178503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178550 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3178550 : Nat := 118140960795 + 3178550 * 2 ^ 59
def prefixEnd_3178550 : Nat := 4983230072969 + 3 ^ 40 * 3178550 * 2
def baseEnd_3178550 : Nat := 1088082622899096094804747

theorem tailTrace_3178550 : CollatzResearch.WordTrace tailWord_3178550 prefixEnd_3178550 1088082622899096094804747 := by
  unfold tailWord_3178550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245702664666479872897819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77287495089775785310910069 7245702664666479872897819)
  ·
    refine ⟨10868553996999719809346729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7245702664666479872897819 10868553996999719809346729)
    ·
      refine ⟨8151415497749789857010047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10868553996999719809346729 8151415497749789857010047)
      ·
        refine ⟨12227123246624684785515071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8151415497749789857010047 12227123246624684785515071)
        ·
          refine ⟨18340684869937027178272607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12227123246624684785515071 18340684869937027178272607)
          ·
            refine ⟨27511027304905540767408911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18340684869937027178272607 27511027304905540767408911)
            ·
              refine ⟨41266540957358311151113367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27511027304905540767408911 41266540957358311151113367)
              ·
                refine ⟨61899811436037466726670051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41266540957358311151113367 61899811436037466726670051)
                ·
                  refine ⟨92849717154056200090005077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61899811436037466726670051 92849717154056200090005077)
                  ·
                    refine ⟨1088082622899096094804747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92849717154056200090005077 1088082622899096094804747)
                    ·
                      rfl

theorem cell22_3178550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3178550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178550 prefixEnd_3178550 := by exact prefixLift 3178550
  have htrace : WordTrace (prefixWord ++ tailWord_3178550) baseStart_3178550 baseEnd_3178550 := by
    simpa [prefixWord, tailWord_3178550, baseEnd_3178550] using wordTrace_append hprefix tailTrace_3178550
  have hstable : (prefixWord ++ tailWord_3178550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178550).length < 2 ^ (prefixWord ++ tailWord_3178550).sum := by decide
  have hdescent : baseEnd_3178550 < baseStart_3178550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178593 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 10]
def baseStart_3178593 : Nat := 118140960795 + 3178593 * 2 ^ 59
def prefixEnd_3178593 : Nat := 4983230072969 + 3 ^ 40 * 3178593 * 2
def baseEnd_3178593 : Nat := 362699114225952771993205

theorem tailTrace_3178593 : CollatzResearch.WordTrace tailWord_3178593 prefixEnd_3178593 362699114225952771993205 := by
  unfold tailWord_3178593
  simp only [CollatzResearch.WordTrace]
  refine ⟨115932810973507896310180433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77288540649005264206786955 115932810973507896310180433)
  ·
    refine ⟨86949608230130922232635325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115932810973507896310180433 86949608230130922232635325)
    ·
      refine ⟨32606103086299095837238247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86949608230130922232635325 32606103086299095837238247)
      ·
        refine ⟨48909154629448643755857371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32606103086299095837238247 48909154629448643755857371)
        ·
          refine ⟨73363731944172965633786057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48909154629448643755857371 73363731944172965633786057)
          ·
            refine ⟨55022798958129724225339543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73363731944172965633786057 55022798958129724225339543)
            ·
              refine ⟨82534198437194586338009315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55022798958129724225339543 82534198437194586338009315)
              ·
                refine ⟨123801297655791879507013973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82534198437194586338009315 123801297655791879507013973)
                ·
                  refine ⟨362699114225952771993205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123801297655791879507013973 362699114225952771993205)
                  ·
                    rfl

theorem cell22_3178593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_3178593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178593 prefixEnd_3178593 := by exact prefixLift 3178593
  have htrace : WordTrace (prefixWord ++ tailWord_3178593) baseStart_3178593 baseEnd_3178593 := by
    simpa [prefixWord, tailWord_3178593, baseEnd_3178593] using wordTrace_append hprefix tailTrace_3178593
  have hstable : (prefixWord ++ tailWord_3178593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178593).length < 2 ^ (prefixWord ++ tailWord_3178593).sum := by decide
  have hdescent : baseEnd_3178593 < baseStart_3178593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178610 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_3178610 : Nat := 118140960795 + 3178610 * 2 ^ 59
def prefixEnd_3178610 : Nat := 4983230072969 + 3 ^ 40 * 3178610 * 2
def baseEnd_3178610 : Nat := 362701054041758646101521

theorem tailTrace_3178610 : CollatzResearch.WordTrace tailWord_3178610 prefixEnd_3178610 362701054041758646101521 := by
  unfold tailWord_3178610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28983357753611577053387321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77288954009630872142366189 28983357753611577053387321)
  ·
    refine ⟨21737518315208682790040491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28983357753611577053387321 21737518315208682790040491)
    ·
      refine ⟨32606277472813024185060737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21737518315208682790040491 32606277472813024185060737)
      ·
        refine ⟨24454708104609768138795553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32606277472813024185060737 24454708104609768138795553)
        ·
          refine ⟨18341031078457326104096665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24454708104609768138795553 18341031078457326104096665)
          ·
            refine ⟨13755773308842994578072499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18341031078457326104096665 13755773308842994578072499)
            ·
              refine ⟨20633659963264491867108749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13755773308842994578072499 20633659963264491867108749)
              ·
                refine ⟨7737622486224184450165781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20633659963264491867108749 7737622486224184450165781)
                ·
                  refine ⟨362701054041758646101521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7737622486224184450165781 362701054041758646101521)
                  ·
                    rfl

theorem cell22_3178610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_3178610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178610 prefixEnd_3178610 := by exact prefixLift 3178610
  have htrace : WordTrace (prefixWord ++ tailWord_3178610) baseStart_3178610 baseEnd_3178610 := by
    simpa [prefixWord, tailWord_3178610, baseEnd_3178610] using wordTrace_append hprefix tailTrace_3178610
  have hstable : (prefixWord ++ tailWord_3178610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178610).length < 2 ^ (prefixWord ++ tailWord_3178610).sum := by decide
  have hdescent : baseEnd_3178610 < baseStart_3178610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178640 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_3178640 : Nat := 118140960795 + 3178640 * 2 ^ 59
def prefixEnd_3178640 : Nat := 4983230072969 + 3 ^ 40 * 3178640 * 2
def baseEnd_3178640 : Nat := 1088113431738365860054471

theorem tailTrace_3178640 : CollatzResearch.WordTrace tailWord_3178640 prefixEnd_3178640 1088113431738365860054471 := by
  unfold tailWord_3178640
  simp only [CollatzResearch.WordTrace]
  refine ⟨57967262602168811668570687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77289683469558415558094249 57967262602168811668570687)
  ·
    refine ⟨86950893903253217502856031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57967262602168811668570687 86950893903253217502856031)
    ·
      refine ⟨130426340854879826254284047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86950893903253217502856031 130426340854879826254284047)
      ·
        refine ⟨195639511282319739381426071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130426340854879826254284047 195639511282319739381426071)
        ·
          refine ⟨293459266923479609072139107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195639511282319739381426071 293459266923479609072139107)
          ·
            refine ⟨440188900385219413608208661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293459266923479609072139107 440188900385219413608208661)
            ·
              refine ⟨20633854705557160012884781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 440188900385219413608208661 20633854705557160012884781)
              ·
                refine ⟨7737695514583935004831793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20633854705557160012884781 7737695514583935004831793)
                ·
                  refine ⟨5803271635937951253623845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7737695514583935004831793 5803271635937951253623845)
                  ·
                    refine ⟨1088113431738365860054471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803271635937951253623845 1088113431738365860054471)
                    ·
                      rfl

theorem cell22_3178640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_3178640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178640 prefixEnd_3178640 := by exact prefixLift 3178640
  have htrace : WordTrace (prefixWord ++ tailWord_3178640) baseStart_3178640 baseEnd_3178640 := by
    simpa [prefixWord, tailWord_3178640, baseEnd_3178640] using wordTrace_append hprefix tailTrace_3178640
  have hstable : (prefixWord ++ tailWord_3178640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178640).length < 2 ^ (prefixWord ++ tailWord_3178640).sum := by decide
  have hdescent : baseEnd_3178640 < baseStart_3178640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178642 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3178642 : Nat := 118140960795 + 3178642 * 2 ^ 59
def prefixEnd_3178642 : Nat := 4983230072969 + 3 ^ 40 * 3178642 * 2
def baseEnd_3178642 : Nat := 1088114116379238521504465

theorem tailTrace_3178642 : CollatzResearch.WordTrace tailWord_3178642 prefixEnd_3178642 1088114116379238521504465 := by
  unfold tailWord_3178642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28983649537582594419678545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77289732100220251785809453 28983649537582594419678545)
  ·
    refine ⟨21737737153186945814758909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28983649537582594419678545 21737737153186945814758909)
    ·
      refine ⟨8151651432445104680534591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21737737153186945814758909 8151651432445104680534591)
      ·
        refine ⟨12227477148667657020801887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8151651432445104680534591 12227477148667657020801887)
        ·
          refine ⟨18341215723001485531202831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12227477148667657020801887 18341215723001485531202831)
          ·
            refine ⟨27511823584502228296804247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18341215723001485531202831 27511823584502228296804247)
            ·
              refine ⟨41267735376753342445206371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27511823584502228296804247 41267735376753342445206371)
              ·
                refine ⟨61901603065130013667809557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41267735376753342445206371 61901603065130013667809557)
                ·
                  refine ⟨2901637643677969390678573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61901603065130013667809557 2901637643677969390678573)
                  ·
                    refine ⟨1088114116379238521504465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901637643677969390678573 1088114116379238521504465)
                    ·
                      rfl

theorem cell22_3178642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3178642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178642 prefixEnd_3178642 := by exact prefixLift 3178642
  have htrace : WordTrace (prefixWord ++ tailWord_3178642) baseStart_3178642 baseEnd_3178642 := by
    simpa [prefixWord, tailWord_3178642, baseEnd_3178642] using wordTrace_append hprefix tailTrace_3178642
  have hstable : (prefixWord ++ tailWord_3178642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178642).length < 2 ^ (prefixWord ++ tailWord_3178642).sum := by decide
  have hdescent : baseEnd_3178642 < baseStart_3178642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178655 : List Nat := [1, 1, 2, 6, 1, 1, 10]
def baseStart_3178655 : Nat := 118140960795 + 3178655 * 2 ^ 59
def prefixEnd_3178655 : Nat := 4983230072969 + 3 ^ 40 * 3178655 * 2
def baseEnd_3178655 : Nat := 40300687649811511886275

theorem tailTrace_3178655 : CollatzResearch.WordTrace tailWord_3178655 prefixEnd_3178655 40300687649811511886275 := by
  unfold tailWord_3178655
  simp only [CollatzResearch.WordTrace]
  refine ⟨115935072299283280898937419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77290048199522187265958279 115935072299283280898937419)
  ·
    refine ⟨173902608448924921348406129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115935072299283280898937419 173902608448924921348406129)
    ·
      refine ⟨130426956336693691011304597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173902608448924921348406129 130426956336693691011304597)
      ·
        refine ⟨6113763578282516766154903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130426956336693691011304597 6113763578282516766154903)
        ·
          refine ⟨9170645367423775149232355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6113763578282516766154903 9170645367423775149232355)
          ·
            refine ⟨13755968051135662723848533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9170645367423775149232355 13755968051135662723848533)
            ·
              refine ⟨40300687649811511886275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13755968051135662723848533 40300687649811511886275)
              ·
                rfl

theorem cell22_3178655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 10].length) (baseStart_3178655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178655 prefixEnd_3178655 := by exact prefixLift 3178655
  have htrace : WordTrace (prefixWord ++ tailWord_3178655) baseStart_3178655 baseEnd_3178655 := by
    simpa [prefixWord, tailWord_3178655, baseEnd_3178655] using wordTrace_append hprefix tailTrace_3178655
  have hstable : (prefixWord ++ tailWord_3178655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178655).length < 2 ^ (prefixWord ++ tailWord_3178655).sum := by decide
  have hdescent : baseEnd_3178655 < baseStart_3178655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178657 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3178657 : Nat := 118140960795 + 3178657 * 2 ^ 59
def prefixEnd_3178657 : Nat := 4983230072969 + 3 ^ 40 * 3178657 * 2
def baseEnd_3178657 : Nat := 1088119251185783482379419

theorem tailTrace_3178657 : CollatzResearch.WordTrace tailWord_3178657 prefixEnd_3178657 1088119251185783482379419 := by
  unfold tailWord_3178657
  simp only [CollatzResearch.WordTrace]
  refine ⟨115935145245276035240510225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77290096830184023493673483 115935145245276035240510225)
  ·
    refine ⟨86951358933957026430382669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115935145245276035240510225 86951358933957026430382669)
    ·
      refine ⟨32606759600233884911393501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86951358933957026430382669 32606759600233884911393501)
      ·
        refine ⟨12227534850087706841772563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32606759600233884911393501 12227534850087706841772563)
        ·
          refine ⟨18341302275131560262658845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12227534850087706841772563 18341302275131560262658845)
          ·
            refine ⟨6877988353174335098497067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18341302275131560262658845 6877988353174335098497067)
            ·
              refine ⟨10316982529761502647745601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877988353174335098497067 10316982529761502647745601)
              ·
                refine ⟨7737736897321126985809201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10316982529761502647745601 7737736897321126985809201)
                ·
                  refine ⟨5803302672990845239356901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7737736897321126985809201 5803302672990845239356901)
                  ·
                    refine ⟨1088119251185783482379419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803302672990845239356901 1088119251185783482379419)
                    ·
                      rfl

theorem cell22_3178657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3178657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178657 prefixEnd_3178657 := by exact prefixLift 3178657
  have htrace : WordTrace (prefixWord ++ tailWord_3178657) baseStart_3178657 baseEnd_3178657 := by
    simpa [prefixWord, tailWord_3178657, baseEnd_3178657] using wordTrace_append hprefix tailTrace_3178657
  have hstable : (prefixWord ++ tailWord_3178657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178657).length < 2 ^ (prefixWord ++ tailWord_3178657).sum := by decide
  have hdescent : baseEnd_3178657 < baseStart_3178657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178798 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3178798 : Nat := 118140960795 + 3178798 * 2 ^ 59
def prefixEnd_3178798 : Nat := 4983230072969 + 3 ^ 40 * 3178798 * 2
def baseEnd_3178798 : Nat := 1088167518367306114603987

theorem tailTrace_3178798 : CollatzResearch.WordTrace tailWord_3178798 prefixEnd_3178798 1088167518367306114603987 := by
  unfold tailWord_3178798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492535992220652040174131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77293525291843477547595365 14492535992220652040174131)
  ·
    refine ⟨21738803988330978060261197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14492535992220652040174131 21738803988330978060261197)
    ·
      refine ⟨8152051495624116772597949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21738803988330978060261197 8152051495624116772597949)
      ·
        refine ⟨3057019310859043789724231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8152051495624116772597949 3057019310859043789724231)
        ·
          refine ⟨4585528966288565684586347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057019310859043789724231 4585528966288565684586347)
          ·
            refine ⟨6878293449432848526879521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585528966288565684586347 6878293449432848526879521)
            ·
              refine ⟨5158720087074636395159641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6878293449432848526879521 5158720087074636395159641)
              ·
                refine ⟨3869040065305977296369731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5158720087074636395159641 3869040065305977296369731)
                ·
                  refine ⟨5803560097958965944554597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869040065305977296369731 5803560097958965944554597)
                  ·
                    refine ⟨1088167518367306114603987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803560097958965944554597 1088167518367306114603987)
                    ·
                      rfl

theorem cell22_3178798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3178798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178798 prefixEnd_3178798 := by exact prefixLift 3178798
  have htrace : WordTrace (prefixWord ++ tailWord_3178798) baseStart_3178798 baseEnd_3178798 := by
    simpa [prefixWord, tailWord_3178798, baseEnd_3178798] using wordTrace_append hprefix tailTrace_3178798
  have hstable : (prefixWord ++ tailWord_3178798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178798).length < 2 ^ (prefixWord ++ tailWord_3178798).sum := by decide
  have hdescent : baseEnd_3178798 < baseStart_3178798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178890 : List Nat := [3, 1, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_3178890 : Nat := 118140960795 + 3178890 * 2 ^ 59
def prefixEnd_3178890 : Nat := 4983230072969 + 3 ^ 40 * 3178890 * 2
def baseEnd_3178890 : Nat := 1088199011847448541303705

theorem tailTrace_3178890 : CollatzResearch.WordTrace tailWord_3178890 prefixEnd_3178890 1088199011847448541303705 := by
  unfold tailWord_3178890
  simp only [CollatzResearch.WordTrace]
  refine ⟨28985910863357979008435531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77295762302287944022494749 28985910863357979008435531)
  ·
    refine ⟨43478866295036968512653297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28985910863357979008435531 43478866295036968512653297)
    ·
      refine ⟨32609149721277726384489973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43478866295036968512653297 32609149721277726384489973)
      ·
        refine ⟨3057107786369786848545935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32609149721277726384489973 3057107786369786848545935)
        ·
          refine ⟨4585661679554680272818903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057107786369786848545935 4585661679554680272818903)
          ·
            refine ⟨6878492519332020409228355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585661679554680272818903 6878492519332020409228355)
            ·
              refine ⟨10317738778998030613842533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6878492519332020409228355 10317738778998030613842533)
              ·
                refine ⟨1934576021062130740095475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10317738778998030613842533 1934576021062130740095475)
                ·
                  refine ⟨2901864031593196110143213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934576021062130740095475 2901864031593196110143213)
                  ·
                    refine ⟨1088199011847448541303705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901864031593196110143213 1088199011847448541303705)
                    ·
                      rfl

theorem cell22_3178890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_3178890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178890 prefixEnd_3178890 := by exact prefixLift 3178890
  have htrace : WordTrace (prefixWord ++ tailWord_3178890) baseStart_3178890 baseEnd_3178890 := by
    simpa [prefixWord, tailWord_3178890, baseEnd_3178890] using wordTrace_append hprefix tailTrace_3178890
  have hstable : (prefixWord ++ tailWord_3178890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178890).length < 2 ^ (prefixWord ++ tailWord_3178890).sum := by decide
  have hdescent : baseEnd_3178890 < baseStart_3178890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178914 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_3178914 : Nat := 118140960795 + 3178914 * 2 ^ 59
def prefixEnd_3178914 : Nat := 4983230072969 + 3 ^ 40 * 3178914 * 2
def baseEnd_3178914 : Nat := 362735742512640159567877

theorem tailTrace_3178914 : CollatzResearch.WordTrace tailWord_3178914 prefixEnd_3178914 362735742512640159567877 := by
  unfold tailWord_3178914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28986129701336242033153949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77296345870229978755077197 28986129701336242033153949)
  ·
    refine ⟨10869798638001090762432731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28986129701336242033153949 10869798638001090762432731)
    ·
      refine ⟨16304697957001636143649097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10869798638001090762432731 16304697957001636143649097)
      ·
        refine ⟨12228523467751227107736823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16304697957001636143649097 12228523467751227107736823)
        ·
          refine ⟨18342785201626840661605235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12228523467751227107736823 18342785201626840661605235)
          ·
            refine ⟨27514177802440260992407853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18342785201626840661605235 27514177802440260992407853)
            ·
              refine ⟨10317816675915097872152945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27514177802440260992407853 10317816675915097872152945)
              ·
                refine ⟨7738362506936323404114709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10317816675915097872152945 7738362506936323404114709)
                ·
                  refine ⟨362735742512640159567877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7738362506936323404114709 362735742512640159567877)
                  ·
                    rfl

theorem cell22_3178914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_3178914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178914 prefixEnd_3178914 := by exact prefixLift 3178914
  have htrace : WordTrace (prefixWord ++ tailWord_3178914) baseStart_3178914 baseEnd_3178914 := by
    simpa [prefixWord, tailWord_3178914, baseEnd_3178914] using wordTrace_append hprefix tailTrace_3178914
  have hstable : (prefixWord ++ tailWord_3178914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178914).length < 2 ^ (prefixWord ++ tailWord_3178914).sum := by decide
  have hdescent : baseEnd_3178914 < baseStart_3178914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178929 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3178929 : Nat := 118140960795 + 3178929 * 2 ^ 59
def prefixEnd_3178929 : Nat := 4983230072969 + 3 ^ 40 * 3178929 * 2
def baseEnd_3178929 : Nat := 1088212362344465439578585

theorem tailTrace_3178929 : CollatzResearch.WordTrace tailWord_3178929 prefixEnd_3178929 1088212362344465439578585 := by
  unfold tailWord_3178929
  simp only [CollatzResearch.WordTrace]
  refine ⟨115945065900290625694411841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77296710600193750462941227 115945065900290625694411841)
  ·
    refine ⟨86958799425217969270808881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115945065900290625694411841 86958799425217969270808881)
    ·
      refine ⟨65219099568913476953106661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86958799425217969270808881 65219099568913476953106661)
      ·
        refine ⟨12228581169171276928707499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65219099568913476953106661 12228581169171276928707499)
        ·
          refine ⟨18342871753756915393061249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12228581169171276928707499 18342871753756915393061249)
          ·
            refine ⟨13757153815317686544795937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18342871753756915393061249 13757153815317686544795937)
            ·
              refine ⟨10317865361488264908596953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13757153815317686544795937 10317865361488264908596953)
              ·
                refine ⟨7738399021116198681447715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10317865361488264908596953 7738399021116198681447715)
                ·
                  refine ⟨11607598531674298022171573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7738399021116198681447715 11607598531674298022171573)
                  ·
                    refine ⟨1088212362344465439578585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11607598531674298022171573 1088212362344465439578585)
                    ·
                      rfl

theorem cell22_3178929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3178929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178929 prefixEnd_3178929 := by exact prefixLift 3178929
  have htrace : WordTrace (prefixWord ++ tailWord_3178929) baseStart_3178929 baseEnd_3178929 := by
    simpa [prefixWord, tailWord_3178929, baseEnd_3178929] using wordTrace_append hprefix tailTrace_3178929
  have hstable : (prefixWord ++ tailWord_3178929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178929).length < 2 ^ (prefixWord ++ tailWord_3178929).sum := by decide
  have hdescent : baseEnd_3178929 < baseStart_3178929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3178987 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 9]
def baseStart_3178987 : Nat := 118140960795 + 3178987 * 2 ^ 59
def prefixEnd_3178987 : Nat := 4983230072969 + 3 ^ 40 * 3178987 * 2
def baseEnd_3178987 : Nat := 362744072309924207209469

theorem tailTrace_3178987 : CollatzResearch.WordTrace tailWord_3178987 prefixEnd_3178987 362744072309924207209469 := by
  unfold tailWord_3178987
  simp only [CollatzResearch.WordTrace]
  refine ⟨115947181334080501600023215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77298120889387001066682143 115947181334080501600023215)
  ·
    refine ⟨173920772001120752400034823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115947181334080501600023215 173920772001120752400034823)
    ·
      refine ⟨260881158001681128600052235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173920772001120752400034823 260881158001681128600052235)
      ·
        refine ⟨391321737002521692900078353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260881158001681128600052235 391321737002521692900078353)
        ·
          refine ⟨293491302751891269675058765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391321737002521692900078353 293491302751891269675058765)
          ·
            refine ⟨110059238531959226128147037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293491302751891269675058765 110059238531959226128147037)
            ·
              refine ⟨41272214449484709798055139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110059238531959226128147037 41272214449484709798055139)
              ·
                refine ⟨61908321674227064697082709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41272214449484709798055139 61908321674227064697082709)
                ·
                  refine ⟨362744072309924207209469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61908321674227064697082709 362744072309924207209469)
                  ·
                    rfl

theorem cell22_3178987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_3178987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3178987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3178987 prefixEnd_3178987 := by exact prefixLift 3178987
  have htrace : WordTrace (prefixWord ++ tailWord_3178987) baseStart_3178987 baseEnd_3178987 := by
    simpa [prefixWord, tailWord_3178987, baseEnd_3178987] using wordTrace_append hprefix tailTrace_3178987
  have hstable : (prefixWord ++ tailWord_3178987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3178987).length < 2 ^ (prefixWord ++ tailWord_3178987).sum := by decide
  have hdescent : baseEnd_3178987 < baseStart_3178987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3178987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179004 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 5]
def baseStart_3179004 : Nat := 118140960795 + 3179004 * 2 ^ 59
def prefixEnd_3179004 : Nat := 4983230072969 + 3 ^ 40 * 3179004 * 2
def baseEnd_3179004 : Nat := 362746012125730081317785

theorem tailTrace_3179004 : CollatzResearch.WordTrace tailWord_3179004 prefixEnd_3179004 362746012125730081317785 := by
  unfold tailWord_3179004
  simp only [CollatzResearch.WordTrace]
  refine ⟨57973900687509456751696033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77298534250012609002261377 57973900687509456751696033)
  ·
    refine ⟨43480425515632092563772025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57973900687509456751696033 43480425515632092563772025)
    ·
      refine ⟨32610319136724069422829019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43480425515632092563772025 32610319136724069422829019)
      ·
        refine ⟨48915478705086104134243529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32610319136724069422829019 48915478705086104134243529)
        ·
          refine ⟨36686609028814578100682647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48915478705086104134243529 36686609028814578100682647)
          ·
            refine ⟨55029913543221867151023971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36686609028814578100682647 55029913543221867151023971)
            ·
              refine ⟨82544870314832800726535957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55029913543221867151023971 82544870314832800726535957)
              ·
                refine ⟨3869290796007787534056373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82544870314832800726535957 3869290796007787534056373)
                ·
                  refine ⟨362746012125730081317785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3869290796007787534056373 362746012125730081317785)
                  ·
                    rfl

theorem cell22_3179004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_3179004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179004 prefixEnd_3179004 := by exact prefixLift 3179004
  have htrace : WordTrace (prefixWord ++ tailWord_3179004) baseStart_3179004 baseEnd_3179004 := by
    simpa [prefixWord, tailWord_3179004, baseEnd_3179004] using wordTrace_append hprefix tailTrace_3179004
  have hstable : (prefixWord ++ tailWord_3179004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179004).length < 2 ^ (prefixWord ++ tailWord_3179004).sum := by decide
  have hdescent : baseEnd_3179004 < baseStart_3179004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179014 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3179014 : Nat := 118140960795 + 3179014 * 2 ^ 59
def prefixEnd_3179014 : Nat := 4983230072969 + 3 ^ 40 * 3179014 * 2
def baseEnd_3179014 : Nat := 1088241459581553551203325

theorem tailTrace_3179014 : CollatzResearch.WordTrace tailWord_3179014 prefixEnd_3179014 1088241459581553551203325 := by
  unfold tailWord_3179014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623380190780708912851753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77298777403321790140837397 3623380190780708912851753)
  ·
    refine ⟨2717535143085531684638815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3623380190780708912851753 2717535143085531684638815)
    ·
      refine ⟨4076302714628297526958223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717535143085531684638815 4076302714628297526958223)
      ·
        refine ⟨6114454071942446290437335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076302714628297526958223 6114454071942446290437335)
        ·
          refine ⟨9171681107913669435656003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114454071942446290437335 9171681107913669435656003)
          ·
            refine ⟨13757521661870504153484005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9171681107913669435656003 13757521661870504153484005)
            ·
              refine ⟨2579535311600719528778251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13757521661870504153484005 2579535311600719528778251)
              ·
                refine ⟨3869302967401079293167377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579535311600719528778251 3869302967401079293167377)
                ·
                  refine ⟨2901977225550809469875533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3869302967401079293167377 2901977225550809469875533)
                  ·
                    refine ⟨1088241459581553551203325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2901977225550809469875533 1088241459581553551203325)
                    ·
                      rfl

theorem cell22_3179014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3179014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179014 prefixEnd_3179014 := by exact prefixLift 3179014
  have htrace : WordTrace (prefixWord ++ tailWord_3179014) baseStart_3179014 baseEnd_3179014 := by
    simpa [prefixWord, tailWord_3179014, baseEnd_3179014] using wordTrace_append hprefix tailTrace_3179014
  have hstable : (prefixWord ++ tailWord_3179014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179014).length < 2 ^ (prefixWord ++ tailWord_3179014).sum := by decide
  have hdescent : baseEnd_3179014 < baseStart_3179014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179064 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_3179064 : Nat := 118140960795 + 3179064 * 2 ^ 59
def prefixEnd_3179064 : Nat := 4983230072969 + 3 ^ 40 * 3179064 * 2
def baseEnd_3179064 : Nat := 1088258575603370087453171

theorem tailTrace_3179064 : CollatzResearch.WordTrace tailWord_3179064 prefixEnd_3179064 1088258575603370087453171 := by
  unfold tailWord_3179064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57974994877400771875288123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77299993169867695833717497 57974994877400771875288123)
  ·
    refine ⟨86962492316101157812932185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57974994877400771875288123 86962492316101157812932185)
    ·
      refine ⟨65221869237075868359699139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86962492316101157812932185 65221869237075868359699139)
      ·
        refine ⟨97832803855613802539548709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65221869237075868359699139 97832803855613802539548709)
        ·
          refine ⟨18343650722927587976165383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97832803855613802539548709 18343650722927587976165383)
          ·
            refine ⟨27515476084391381964248075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18343650722927587976165383 27515476084391381964248075)
            ·
              refine ⟨41273214126587072946372113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27515476084391381964248075 41273214126587072946372113)
              ·
                refine ⟨30954910594940304709779085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41273214126587072946372113 30954910594940304709779085)
                ·
                  refine ⟨11608091473102614266167157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30954910594940304709779085 11608091473102614266167157)
                  ·
                    refine ⟨1088258575603370087453171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11608091473102614266167157 1088258575603370087453171)
                    ·
                      rfl

theorem cell22_3179064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_3179064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179064 prefixEnd_3179064 := by exact prefixLift 3179064
  have htrace : WordTrace (prefixWord ++ tailWord_3179064) baseStart_3179064 baseEnd_3179064 := by
    simpa [prefixWord, tailWord_3179064, baseEnd_3179064] using wordTrace_append hprefix tailTrace_3179064
  have hstable : (prefixWord ++ tailWord_3179064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179064).length < 2 ^ (prefixWord ++ tailWord_3179064).sum := by decide
  have hdescent : baseEnd_3179064 < baseStart_3179064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179096 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_3179096 : Nat := 118140960795 + 3179096 * 2 ^ 59
def prefixEnd_3179096 : Nat := 4983230072969 + 3 ^ 40 * 3179096 * 2
def baseEnd_3179096 : Nat := 1088269529857332670653073

theorem tailTrace_3179096 : CollatzResearch.WordTrace tailWord_3179096 prefixEnd_3179096 1088269529857332670653073 := by
  unfold tailWord_3179096
  simp only [CollatzResearch.WordTrace]
  refine ⟨57975578445342806607870571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77300771260457075477160761 57975578445342806607870571)
  ·
    refine ⟨86963367668014209911805857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57975578445342806607870571 86963367668014209911805857)
    ·
      refine ⟨65222525751010657433854393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86963367668014209911805857 65222525751010657433854393)
      ·
        refine ⟨48916894313257993075390795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65222525751010657433854393 48916894313257993075390795)
        ·
          refine ⟨73375341469886989613086193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48916894313257993075390795 73375341469886989613086193)
          ·
            refine ⟨55031506102415242209814645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73375341469886989613086193 55031506102415242209814645)
            ·
              refine ⟨5159203697101428957170123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55031506102415242209814645 5159203697101428957170123)
              ·
                refine ⟨7738805545652143435755185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159203697101428957170123 7738805545652143435755185)
                ·
                  refine ⟨5804104159239107576816389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7738805545652143435755185 5804104159239107576816389)
                  ·
                    refine ⟨1088269529857332670653073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804104159239107576816389 1088269529857332670653073)
                    ·
                      rfl

theorem cell22_3179096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_3179096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179096 prefixEnd_3179096 := by exact prefixLift 3179096
  have htrace : WordTrace (prefixWord ++ tailWord_3179096) baseStart_3179096 baseEnd_3179096 := by
    simpa [prefixWord, tailWord_3179096, baseEnd_3179096] using wordTrace_append hprefix tailTrace_3179096
  have hstable : (prefixWord ++ tailWord_3179096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179096).length < 2 ^ (prefixWord ++ tailWord_3179096).sum := by decide
  have hdescent : baseEnd_3179096 < baseStart_3179096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179100 : List Nat := [2, 2, 4, 1, 3, 1, 2, 3, 4]
def baseStart_3179100 : Nat := 118140960795 + 3179100 * 2 ^ 59
def prefixEnd_3179100 : Nat := 4983230072969 + 3 ^ 40 * 3179100 * 2
def baseEnd_3179100 : Nat := 362756966379692664517687

theorem tailTrace_3179100 : CollatzResearch.WordTrace tailWord_3179100 prefixEnd_3179100 362756966379692664517687 := by
  unfold tailWord_3179100
  simp only [CollatzResearch.WordTrace]
  refine ⟨57975651391335560949443377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77300868521780747932591169 57975651391335560949443377)
  ·
    refine ⟨43481738543501670712082533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57975651391335560949443377 43481738543501670712082533)
    ·
      refine ⟨8152825976906563258515475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43481738543501670712082533 8152825976906563258515475)
      ·
        refine ⟨12229238965359844887773213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8152825976906563258515475 12229238965359844887773213)
        ·
          refine ⟨4585964612009941832914955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12229238965359844887773213 4585964612009941832914955)
          ·
            refine ⟨6878946918014912749372433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585964612009941832914955 6878946918014912749372433)
            ·
              refine ⟨5159210188511184562029325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6878946918014912749372433 5159210188511184562029325)
              ·
                refine ⟨1934703820691694210760997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5159210188511184562029325 1934703820691694210760997)
                ·
                  refine ⟨362756966379692664517687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934703820691694210760997 362756966379692664517687)
                  ·
                    rfl

theorem cell22_3179100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_3179100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179100 prefixEnd_3179100 := by exact prefixLift 3179100
  have htrace : WordTrace (prefixWord ++ tailWord_3179100) baseStart_3179100 baseEnd_3179100 := by
    simpa [prefixWord, tailWord_3179100, baseEnd_3179100] using wordTrace_append hprefix tailTrace_3179100
  have hstable : (prefixWord ++ tailWord_3179100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179100).length < 2 ^ (prefixWord ++ tailWord_3179100).sum := by decide
  have hdescent : baseEnd_3179100 < baseStart_3179100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179186 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_3179186 : Nat := 118140960795 + 3179186 * 2 ^ 59
def prefixEnd_3179186 : Nat := 4983230072969 + 3 ^ 40 * 3179186 * 2
def baseEnd_3179186 : Nat := 1088300338696602435902797

theorem tailTrace_3179186 : CollatzResearch.WordTrace tailWord_3179186 prefixEnd_3179186 1088300338696602435902797 := by
  unfold tailWord_3179186
  simp only [CollatzResearch.WordTrace]
  refine ⟨28988609865089889646629353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77302959640239705724344941 28988609865089889646629353)
  ·
    refine ⟨21741457398817417234972015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28988609865089889646629353 21741457398817417234972015)
    ·
      refine ⟨32612186098226125852458023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21741457398817417234972015 32612186098226125852458023)
      ·
        refine ⟨48918279147339188778687035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32612186098226125852458023 48918279147339188778687035)
        ·
          refine ⟨73377418721008783168030553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48918279147339188778687035 73377418721008783168030553)
          ·
            refine ⟨55033064040756587376022915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73377418721008783168030553 55033064040756587376022915)
            ·
              refine ⟨82549596061134881064034373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55033064040756587376022915 82549596061134881064034373)
              ·
                refine ⟨15478049261462790199506445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82549596061134881064034373 15478049261462790199506445)
                ·
                  refine ⟨5804268473048546324814917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15478049261462790199506445 5804268473048546324814917)
                  ·
                    refine ⟨1088300338696602435902797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804268473048546324814917 1088300338696602435902797)
                    ·
                      rfl

theorem cell22_3179186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_3179186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179186 prefixEnd_3179186 := by exact prefixLift 3179186
  have htrace : WordTrace (prefixWord ++ tailWord_3179186) baseStart_3179186 baseEnd_3179186 := by
    simpa [prefixWord, tailWord_3179186, baseEnd_3179186] using wordTrace_append hprefix tailTrace_3179186
  have hstable : (prefixWord ++ tailWord_3179186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179186).length < 2 ^ (prefixWord ++ tailWord_3179186).sum := by decide
  have hdescent : baseEnd_3179186 < baseStart_3179186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179235 : List Nat := [1, 1, 1, 7, 1, 2, 1, 4, 4]
def baseStart_3179235 : Nat := 118140960795 + 3179235 * 2 ^ 59
def prefixEnd_3179235 : Nat := 4983230072969 + 3 ^ 40 * 3179235 * 2
def baseEnd_3179235 : Nat := 362772370799327547142549

theorem tailTrace_3179235 : CollatzResearch.WordTrace tailWord_3179235 prefixEnd_3179235 362772370799327547142549 := by
  unfold tailWord_3179235
  simp only [CollatzResearch.WordTrace]
  refine ⟨115956226637182039955051159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77304151091454693303367439 115956226637182039955051159)
  ·
    refine ⟨173934339955773059932576739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115956226637182039955051159 173934339955773059932576739)
    ·
      refine ⟨260901509933659589898865109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173934339955773059932576739 260901509933659589898865109)
      ·
        refine ⟨6114879139070146638254651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 260901509933659589898865109 6114879139070146638254651)
        ·
          refine ⟨9172318708605219957381977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114879139070146638254651 9172318708605219957381977)
          ·
            refine ⟨6879239031453914968036483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9172318708605219957381977 6879239031453914968036483)
            ·
              refine ⟨10318858547180872452054725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879239031453914968036483 10318858547180872452054725)
              ·
                refine ⟨1934785977596413584760261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10318858547180872452054725 1934785977596413584760261)
                ·
                  refine ⟨362772370799327547142549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934785977596413584760261 362772370799327547142549)
                  ·
                    rfl

theorem cell22_3179235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 4].length) (baseStart_3179235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179235 prefixEnd_3179235 := by exact prefixLift 3179235
  have htrace : WordTrace (prefixWord ++ tailWord_3179235) baseStart_3179235 baseEnd_3179235 := by
    simpa [prefixWord, tailWord_3179235, baseEnd_3179235] using wordTrace_append hprefix tailTrace_3179235
  have hstable : (prefixWord ++ tailWord_3179235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179235).length < 2 ^ (prefixWord ++ tailWord_3179235).sum := by decide
  have hdescent : baseEnd_3179235 < baseStart_3179235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179250 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_3179250 : Nat := 118140960795 + 3179250 * 2 ^ 59
def prefixEnd_3179250 : Nat := 4983230072969 + 3 ^ 40 * 3179250 * 2
def baseEnd_3179250 : Nat := 1088322247204527602302601

theorem tailTrace_3179250 : CollatzResearch.WordTrace tailWord_3179250 prefixEnd_3179250 1088322247204527602302601 := by
  unfold tailWord_3179250
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989193433031924379211801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77304515821418465011231469 28989193433031924379211801)
  ·
    refine ⟨21741895074773943284408851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28989193433031924379211801 21741895074773943284408851)
    ·
      refine ⟨32612842612160914926613277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21741895074773943284408851 32612842612160914926613277)
      ·
        refine ⟨12229815979560343097479979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32612842612160914926613277 12229815979560343097479979)
        ·
          refine ⟨18344723969340514646219969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12229815979560343097479979 18344723969340514646219969)
          ·
            refine ⟨13758542977005385984664977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18344723969340514646219969 13758542977005385984664977)
            ·
              refine ⟨10318907232754039488498733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13758542977005385984664977 10318907232754039488498733)
              ·
                refine ⟨3869590212282764808187025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10318907232754039488498733 3869590212282764808187025)
                ·
                  refine ⟨2902192659212073606140269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3869590212282764808187025 2902192659212073606140269)
                  ·
                    refine ⟨1088322247204527602302601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902192659212073606140269 1088322247204527602302601)
                    ·
                      rfl

theorem cell22_3179250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_3179250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179250 prefixEnd_3179250 := by exact prefixLift 3179250
  have htrace : WordTrace (prefixWord ++ tailWord_3179250) baseStart_3179250 baseEnd_3179250 := by
    simpa [prefixWord, tailWord_3179250, baseEnd_3179250] using wordTrace_append hprefix tailTrace_3179250
  have hstable : (prefixWord ++ tailWord_3179250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179250).length < 2 ^ (prefixWord ++ tailWord_3179250).sum := by decide
  have hdescent : baseEnd_3179250 < baseStart_3179250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179252 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3179252 : Nat := 118140960795 + 3179252 * 2 ^ 59
def prefixEnd_3179252 : Nat := 4983230072969 + 3 ^ 40 * 3179252 * 2
def baseEnd_3179252 : Nat := 362774310615133421250865

theorem tailTrace_3179252 : CollatzResearch.WordTrace tailWord_3179252 prefixEnd_3179252 362774310615133421250865 := by
  unfold tailWord_3179252
  simp only [CollatzResearch.WordTrace]
  refine ⟨57978423339060225929210005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77304564452080301238946673 57978423339060225929210005)
  ·
    refine ⟨2717738594018448090431719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57978423339060225929210005 2717738594018448090431719)
    ·
      refine ⟨4076607891027672135647579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717738594018448090431719 4076607891027672135647579)
      ·
        refine ⟨6114911836541508203471369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076607891027672135647579 6114911836541508203471369)
        ·
          refine ⟨4586183877406131152603527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6114911836541508203471369 4586183877406131152603527)
          ·
            refine ⟨6879275816109196728905291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586183877406131152603527 6879275816109196728905291)
            ·
              refine ⟨10318913724163795093357937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879275816109196728905291 10318913724163795093357937)
              ·
                refine ⟨7739185293122846320018453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10318913724163795093357937 7739185293122846320018453)
                ·
                  refine ⟨362774310615133421250865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7739185293122846320018453 362774310615133421250865)
                  ·
                    rfl

theorem cell22_3179252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3179252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179252 prefixEnd_3179252 := by exact prefixLift 3179252
  have htrace : WordTrace (prefixWord ++ tailWord_3179252) baseStart_3179252 baseEnd_3179252 := by
    simpa [prefixWord, tailWord_3179252, baseEnd_3179252] using wordTrace_append hprefix tailTrace_3179252
  have hstable : (prefixWord ++ tailWord_3179252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179252).length < 2 ^ (prefixWord ++ tailWord_3179252).sum := by decide
  have hdescent : baseEnd_3179252 < baseStart_3179252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179278 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3179278 : Nat := 118140960795 + 3179278 * 2 ^ 59
def prefixEnd_3179278 : Nat := 4983230072969 + 3 ^ 40 * 3179278 * 2
def baseEnd_3179278 : Nat := 1088331832176744862602515

theorem tailTrace_3179278 : CollatzResearch.WordTrace tailWord_3179278 prefixEnd_3179278 1088331832176744862602515 := by
  unfold tailWord_3179278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494724372003282287358311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77305196650684172199244325 14494724372003282287358311)
  ·
    refine ⟨21742086558004923431037467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14494724372003282287358311 21742086558004923431037467)
    ·
      refine ⟨32613129837007385146556201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21742086558004923431037467 32613129837007385146556201)
      ·
        refine ⟨24459847377755538859917151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32613129837007385146556201 24459847377755538859917151)
        ·
          refine ⟨36689771066633308289875727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24459847377755538859917151 36689771066633308289875727)
          ·
            refine ⟨55034656599949962434813591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36689771066633308289875727 55034656599949962434813591)
            ·
              refine ⟨82551984899924943652220387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55034656599949962434813591 82551984899924943652220387)
              ·
                refine ⟨123827977349887415478330581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82551984899924943652220387 123827977349887415478330581)
                ·
                  refine ⟨2902218219137986300273373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123827977349887415478330581 2902218219137986300273373)
                  ·
                    refine ⟨1088331832176744862602515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902218219137986300273373 1088331832176744862602515)
                    ·
                      rfl

theorem cell22_3179278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3179278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179278 prefixEnd_3179278 := by exact prefixLift 3179278
  have htrace : WordTrace (prefixWord ++ tailWord_3179278) baseStart_3179278 baseEnd_3179278 := by
    simpa [prefixWord, tailWord_3179278, baseEnd_3179278] using wordTrace_append hprefix tailTrace_3179278
  have hstable : (prefixWord ++ tailWord_3179278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179278).length < 2 ^ (prefixWord ++ tailWord_3179278).sum := by decide
  have hdescent : baseEnd_3179278 < baseStart_3179278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179295 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 3, 3]
def baseStart_3179295 : Nat := 118140960795 + 3179295 * 2 ^ 59
def prefixEnd_3179295 : Nat := 4983230072969 + 3 ^ 40 * 3179295 * 2
def baseEnd_3179295 : Nat := 1088337651624162484927463

theorem tailTrace_3179295 : CollatzResearch.WordTrace tailWord_3179295 prefixEnd_3179295 1088337651624162484927463 := by
  unfold tailWord_3179295
  simp only [CollatzResearch.WordTrace]
  refine ⟨115958415016964670202235339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77305610011309780134823559 115958415016964670202235339)
  ·
    refine ⟨173937622525447005303353009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115958415016964670202235339 173937622525447005303353009)
    ·
      refine ⟨130453216894085253977514757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173937622525447005303353009 130453216894085253977514757)
      ·
        refine ⟨24459978167640985120784017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130453216894085253977514757 24459978167640985120784017)
        ·
          refine ⟨18344983625730738840588013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24459978167640985120784017 18344983625730738840588013)
          ·
            refine ⟨6879368859649027065220505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18344983625730738840588013 6879368859649027065220505)
            ·
              refine ⟨5159526644736770298915379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6879368859649027065220505 5159526644736770298915379)
              ·
                refine ⟨7739289967105155448373069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159526644736770298915379 7739289967105155448373069)
                ·
                  refine ⟨2902233737664433293139901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7739289967105155448373069 2902233737664433293139901)
                  ·
                    refine ⟨1088337651624162484927463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902233737664433293139901 1088337651624162484927463)
                    ·
                      rfl

theorem cell22_3179295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_3179295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179295 prefixEnd_3179295 := by exact prefixLift 3179295
  have htrace : WordTrace (prefixWord ++ tailWord_3179295) baseStart_3179295 baseEnd_3179295 := by
    simpa [prefixWord, tailWord_3179295, baseEnd_3179295] using wordTrace_append hprefix tailTrace_3179295
  have hstable : (prefixWord ++ tailWord_3179295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179295).length < 2 ^ (prefixWord ++ tailWord_3179295).sum := by decide
  have hdescent : baseEnd_3179295 < baseStart_3179295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179353 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 6]
def baseStart_3179353 : Nat := 118140960795 + 3179353 * 2 ^ 59
def prefixEnd_3179353 : Nat := 4983230072969 + 3 ^ 40 * 3179353 * 2
def baseEnd_3179353 : Nat := 362785835403156555659095

theorem tailTrace_3179353 : CollatzResearch.WordTrace tailWord_3179353 prefixEnd_3179353 362785835403156555659095 := by
  unfold tailWord_3179353
  simp only [CollatzResearch.WordTrace]
  refine ⟨115960530450754546107846713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77307020300503030738564475 115960530450754546107846713)
  ·
    refine ⟨86970397838065909580885035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115960530450754546107846713 86970397838065909580885035)
    ·
      refine ⟨130455596757098864371327553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86970397838065909580885035 130455596757098864371327553)
      ·
        refine ⟨97841697567824148278495665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130455596757098864371327553 97841697567824148278495665)
        ·
          refine ⟨73381273175868111208871749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97841697567824148278495665 73381273175868111208871749)
          ·
            refine ⟨13758988720475270851663453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73381273175868111208871749 13758988720475270851663453)
            ·
              refine ⟨5159620770178226569373795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13758988720475270851663453 5159620770178226569373795)
              ·
                refine ⟨7739431155267339854060693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159620770178226569373795 7739431155267339854060693)
                ·
                  refine ⟨362785835403156555659095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7739431155267339854060693 362785835403156555659095)
                  ·
                    rfl

theorem cell22_3179353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_3179353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179353 prefixEnd_3179353 := by exact prefixLift 3179353
  have htrace : WordTrace (prefixWord ++ tailWord_3179353) baseStart_3179353 baseEnd_3179353 := by
    simpa [prefixWord, tailWord_3179353, baseEnd_3179353] using wordTrace_append hprefix tailTrace_3179353
  have hstable : (prefixWord ++ tailWord_3179353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179353).length < 2 ^ (prefixWord ++ tailWord_3179353).sum := by decide
  have hdescent : baseEnd_3179353 < baseStart_3179353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179400 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3179400 : Nat := 118140960795 + 3179400 * 2 ^ 59
def prefixEnd_3179400 : Nat := 4983230072969 + 3 ^ 40 * 3179400 * 2
def baseEnd_3179400 : Nat := 1088373595269977211052141

theorem tailTrace_3179400 : CollatzResearch.WordTrace tailWord_3179400 prefixEnd_3179400 1088373595269977211052141 := by
  unfold tailWord_3179400
  simp only [CollatzResearch.WordTrace]
  refine ⟨57981122340792136567403827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77308163121056182089871769 57981122340792136567403827)
  ·
    refine ⟨86971683511188204851105741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57981122340792136567403827 86971683511188204851105741)
    ·
      refine ⟨32614381316695576819164653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86971683511188204851105741 32614381316695576819164653)
      ·
        refine ⟨12230392993760841307186745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32614381316695576819164653 12230392993760841307186745)
        ·
          refine ⟨9172794745320630980390059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12230392993760841307186745 9172794745320630980390059)
          ·
            refine ⟨13759192117980946470585089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172794745320630980390059 13759192117980946470585089)
            ·
              refine ⟨10319394088485709852938817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13759192117980946470585089 10319394088485709852938817)
              ·
                refine ⟨7739545566364282389704113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10319394088485709852938817 7739545566364282389704113)
                ·
                  refine ⟨5804659174773211792278085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7739545566364282389704113 5804659174773211792278085)
                  ·
                    refine ⟨1088373595269977211052141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5804659174773211792278085 1088373595269977211052141)
                    ·
                      rfl

theorem cell22_3179400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3179400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179400 prefixEnd_3179400 := by exact prefixLift 3179400
  have htrace : WordTrace (prefixWord ++ tailWord_3179400) baseStart_3179400 baseEnd_3179400 := by
    simpa [prefixWord, tailWord_3179400, baseEnd_3179400] using wordTrace_append hprefix tailTrace_3179400
  have hstable : (prefixWord ++ tailWord_3179400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179400).length < 2 ^ (prefixWord ++ tailWord_3179400).sum := by decide
  have hdescent : baseEnd_3179400 < baseStart_3179400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179402 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_3179402 : Nat := 118140960795 + 3179402 * 2 ^ 59
def prefixEnd_3179402 : Nat := 4983230072969 + 3 ^ 40 * 3179402 * 2
def baseEnd_3179402 : Nat := 1088374279910849872502135

theorem tailTrace_3179402 : CollatzResearch.WordTrace tailWord_3179402 prefixEnd_3179402 1088374279910849872502135 := by
  unfold tailWord_3179402
  simp only [CollatzResearch.WordTrace]
  refine ⟨28990579406894256869095115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77308211751718018317586973 28990579406894256869095115)
  ·
    refine ⟨43485869110341385303642673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28990579406894256869095115 43485869110341385303642673)
    ·
      refine ⟨32614401832756038977732005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43485869110341385303642673 32614401832756038977732005)
      ·
        refine ⟨6115200343641757308324751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32614401832756038977732005 6115200343641757308324751)
        ·
          refine ⟨9172800515462635962487127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6115200343641757308324751 9172800515462635962487127)
          ·
            refine ⟨13759200773193953943730691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172800515462635962487127 13759200773193953943730691)
            ·
              refine ⟨20638801159790930915596037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13759200773193953943730691 20638801159790930915596037)
              ·
                refine ⟨3869775217460799546674257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20638801159790930915596037 3869775217460799546674257)
                ·
                  refine ⟨2902331413095599660005693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3869775217460799546674257 2902331413095599660005693)
                  ·
                    refine ⟨1088374279910849872502135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902331413095599660005693 1088374279910849872502135)
                    ·
                      rfl

theorem cell22_3179402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_3179402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179402 prefixEnd_3179402 := by exact prefixLift 3179402
  have htrace : WordTrace (prefixWord ++ tailWord_3179402) baseStart_3179402 baseEnd_3179402 := by
    simpa [prefixWord, tailWord_3179402, baseEnd_3179402] using wordTrace_append hprefix tailTrace_3179402
  have hstable : (prefixWord ++ tailWord_3179402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179402).length < 2 ^ (prefixWord ++ tailWord_3179402).sum := by decide
  have hdescent : baseEnd_3179402 < baseStart_3179402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179428 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3179428 : Nat := 118140960795 + 3179428 * 2 ^ 59
def prefixEnd_3179428 : Nat := 4983230072969 + 3 ^ 40 * 3179428 * 2
def baseEnd_3179428 : Nat := 1088383180242194471352055

theorem tailTrace_3179428 : CollatzResearch.WordTrace tailWord_3179428 prefixEnd_3179428 1088383180242194471352055 := by
  unfold tailWord_3179428
  simp only [CollatzResearch.WordTrace]
  refine ⟨57981632962741416958413469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77308843950321889277884625 57981632962741416958413469)
  ·
    refine ⟨21743112361028031359405051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57981632962741416958413469 21743112361028031359405051)
    ·
      refine ⟨32614668541542047039107577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21743112361028031359405051 32614668541542047039107577)
      ·
        refine ⟨24461001406156535279330683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32614668541542047039107577 24461001406156535279330683)
        ·
          refine ⟨36691502109234802918996025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24461001406156535279330683 36691502109234802918996025)
          ·
            refine ⟨27518626581926102189247019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36691502109234802918996025 27518626581926102189247019)
            ·
              refine ⟨41277939872889153283870529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27518626581926102189247019 41277939872889153283870529)
              ·
                refine ⟨30958454904666864962902897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41277939872889153283870529 30958454904666864962902897)
                ·
                  refine ⟨23218841178500148722177173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30958454904666864962902897 23218841178500148722177173)
                  ·
                    refine ⟨1088383180242194471352055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23218841178500148722177173 1088383180242194471352055)
                    ·
                      rfl

theorem cell22_3179428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3179428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179428 prefixEnd_3179428 := by exact prefixLift 3179428
  have htrace : WordTrace (prefixWord ++ tailWord_3179428) baseStart_3179428 baseEnd_3179428 := by
    simpa [prefixWord, tailWord_3179428, baseEnd_3179428] using wordTrace_append hprefix tailTrace_3179428
  have hstable : (prefixWord ++ tailWord_3179428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179428).length < 2 ^ (prefixWord ++ tailWord_3179428).sum := by decide
  have hdescent : baseEnd_3179428 < baseStart_3179428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179447 : List Nat := [1, 1, 3, 1, 3, 1, 3, 5, 1, 3]
def baseStart_3179447 : Nat := 118140960795 + 3179447 * 2 ^ 59
def prefixEnd_3179447 : Nat := 4983230072969 + 3 ^ 40 * 3179447 * 2
def baseEnd_3179447 : Nat := 1088389684330484755126997

theorem tailTrace_3179447 : CollatzResearch.WordTrace tailWord_3179447 prefixEnd_3179447 1088389684330484755126997 := by
  unfold tailWord_3179447
  simp only [CollatzResearch.WordTrace]
  refine ⟨115963958912414000161768595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77309305941609333441179063 115963958912414000161768595)
  ·
    refine ⟨173945938368621000242652893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115963958912414000161768595 173945938368621000242652893)
    ·
      refine ⟨65229726888232875090994835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173945938368621000242652893 65229726888232875090994835)
      ·
        refine ⟨97844590332349312636492253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65229726888232875090994835 97844590332349312636492253)
        ·
          refine ⟨36691721374630992238684595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97844590332349312636492253 36691721374630992238684595)
          ·
            refine ⟨55037582061946488358026893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36691721374630992238684595 55037582061946488358026893)
            ·
              refine ⟨20639093273229933134260085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55037582061946488358026893 20639093273229933134260085)
              ·
                refine ⟨1934914994365306231336883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20639093273229933134260085 1934914994365306231336883)
                ·
                  refine ⟨2902372491547959347005325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934914994365306231336883 2902372491547959347005325)
                  ·
                    refine ⟨1088389684330484755126997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902372491547959347005325 1088389684330484755126997)
                    ·
                      rfl

theorem cell22_3179447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_3179447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179447 prefixEnd_3179447 := by exact prefixLift 3179447
  have htrace : WordTrace (prefixWord ++ tailWord_3179447) baseStart_3179447 baseEnd_3179447 := by
    simpa [prefixWord, tailWord_3179447, baseEnd_3179447] using wordTrace_append hprefix tailTrace_3179447
  have hstable : (prefixWord ++ tailWord_3179447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179447).length < 2 ^ (prefixWord ++ tailWord_3179447).sum := by decide
  have hdescent : baseEnd_3179447 < baseStart_3179447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179580 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_3179580 : Nat := 118140960795 + 3179580 * 2 ^ 59
def prefixEnd_3179580 : Nat := 4983230072969 + 3 ^ 40 * 3179580 * 2
def baseEnd_3179580 : Nat := 1088435212948516741551589

theorem tailTrace_3179580 : CollatzResearch.WordTrace tailWord_3179580 prefixEnd_3179580 1088435212948516741551589 := by
  unfold tailWord_3179580
  simp only [CollatzResearch.WordTrace]
  refine ⟨57984404910466081938180097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77312539880621442584240129 57984404910466081938180097)
  ·
    refine ⟨43488303682849561453635073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57984404910466081938180097 43488303682849561453635073)
    ·
      refine ⟨32616227762137171090226305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43488303682849561453635073 32616227762137171090226305)
      ·
        refine ⟨24462170821602878317669729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32616227762137171090226305 24462170821602878317669729)
        ·
          refine ⟨18346628116202158738252297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24462170821602878317669729 18346628116202158738252297)
          ·
            refine ⟨13759971087151619053689223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18346628116202158738252297 13759971087151619053689223)
            ·
              refine ⟨20639956630727428580533835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13759971087151619053689223 20639956630727428580533835)
              ·
                refine ⟨30959934946091142870800753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20639956630727428580533835 30959934946091142870800753)
                ·
                  refine ⟨23219951209568357153100565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30959934946091142870800753 23219951209568357153100565)
                  ·
                    refine ⟨1088435212948516741551589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23219951209568357153100565 1088435212948516741551589)
                    ·
                      rfl

theorem cell22_3179580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_3179580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179580 prefixEnd_3179580 := by exact prefixLift 3179580
  have htrace : WordTrace (prefixWord ++ tailWord_3179580) baseStart_3179580 baseEnd_3179580 := by
    simpa [prefixWord, tailWord_3179580, baseEnd_3179580] using wordTrace_append hprefix tailTrace_3179580
  have hstable : (prefixWord ++ tailWord_3179580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179580).length < 2 ^ (prefixWord ++ tailWord_3179580).sum := by decide
  have hdescent : baseEnd_3179580 < baseStart_3179580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179629 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 5]
def baseStart_3179629 : Nat := 118140960795 + 3179629 * 2 ^ 59
def prefixEnd_3179629 : Nat := 4983230072969 + 3 ^ 40 * 3179629 * 2
def baseEnd_3179629 : Nat := 362817328883298982358813

theorem tailTrace_3179629 : CollatzResearch.WordTrace tailWord_3179629 prefixEnd_3179629 362817328883298982358813 := by
  unfold tailWord_3179629
  simp only [CollatzResearch.WordTrace]
  refine ⟨115970596997754645244893941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77313731331836430163262627 115970596997754645244893941)
  ·
    refine ⟨10872243468539497991708807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115970596997754645244893941 10872243468539497991708807)
    ·
      refine ⟨16308365202809246987563211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10872243468539497991708807 16308365202809246987563211)
      ·
        refine ⟨24462547804213870481344817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16308365202809246987563211 24462547804213870481344817)
        ·
          refine ⟨18346910853160402861008613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24462547804213870481344817 18346910853160402861008613)
          ·
            refine ⟨3440045784967575536439115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18346910853160402861008613 3440045784967575536439115)
            ·
              refine ⟨5160068677451363304658673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440045784967575536439115 5160068677451363304658673)
              ·
                refine ⟨3870051508088522478494005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160068677451363304658673 3870051508088522478494005)
                ·
                  refine ⟨362817328883298982358813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870051508088522478494005 362817328883298982358813)
                  ·
                    rfl

theorem cell22_3179629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_3179629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179629 prefixEnd_3179629 := by exact prefixLift 3179629
  have htrace : WordTrace (prefixWord ++ tailWord_3179629) baseStart_3179629 baseEnd_3179629 := by
    simpa [prefixWord, tailWord_3179629, baseEnd_3179629] using wordTrace_append hprefix tailTrace_3179629
  have hstable : (prefixWord ++ tailWord_3179629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179629).length < 2 ^ (prefixWord ++ tailWord_3179629).sum := by decide
  have hdescent : baseEnd_3179629 < baseStart_3179629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179640 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 6]
def baseStart_3179640 : Nat := 118140960795 + 3179640 * 2 ^ 59
def prefixEnd_3179640 : Nat := 4983230072969 + 3 ^ 40 * 3179640 * 2
def baseEnd_3179640 : Nat := 362818584058232195017135

theorem tailTrace_3179640 : CollatzResearch.WordTrace tailWord_3179640 prefixEnd_3179640 362818584058232195017135 := by
  unfold tailWord_3179640
  simp only [CollatzResearch.WordTrace]
  refine ⟨57985499100357397061772187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77313998800476529415696249 57985499100357397061772187)
  ·
    refine ⟨86978248650536095592658281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57985499100357397061772187 86978248650536095592658281)
    ·
      refine ⟨65233686487902071694493711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86978248650536095592658281 65233686487902071694493711)
      ·
        refine ⟨97850529731853107541740567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65233686487902071694493711 97850529731853107541740567)
        ·
          refine ⟨146775794597779661312610851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97850529731853107541740567 146775794597779661312610851)
          ·
            refine ⟨220163691896669491968916277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146775794597779661312610851 220163691896669491968916277)
            ·
              refine ⟨20640346115312764872085901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220163691896669491968916277 20640346115312764872085901)
              ·
                refine ⟨7740129793242286827032213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20640346115312764872085901 7740129793242286827032213)
                ·
                  refine ⟨362818584058232195017135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7740129793242286827032213 362818584058232195017135)
                  ·
                    rfl

theorem cell22_3179640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_3179640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179640 prefixEnd_3179640 := by exact prefixLift 3179640
  have htrace : WordTrace (prefixWord ++ tailWord_3179640) baseStart_3179640 baseEnd_3179640 := by
    simpa [prefixWord, tailWord_3179640, baseEnd_3179640] using wordTrace_append hprefix tailTrace_3179640
  have hstable : (prefixWord ++ tailWord_3179640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179640).length < 2 ^ (prefixWord ++ tailWord_3179640).sum := by decide
  have hdescent : baseEnd_3179640 < baseStart_3179640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179685 : List Nat := [1, 3, 1, 2, 1, 4, 10]
def baseStart_3179685 : Nat := 118140960795 + 3179685 * 2 ^ 59
def prefixEnd_3179685 : Nat := 4983230072969 + 3 ^ 40 * 3179685 * 2
def baseEnd_3179685 : Nat := 40313746540530795099121

theorem tailTrace_3179685 : CollatzResearch.WordTrace tailWord_3179685 prefixEnd_3179685 40313746540530795099121 := by
  unfold tailWord_3179685
  simp only [CollatzResearch.WordTrace]
  refine ⟨115972639485551766808932509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77315092990367844539288339 115972639485551766808932509)
  ·
    refine ⟨43489739807081912553349691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115972639485551766808932509 43489739807081912553349691)
    ·
      refine ⟨65234609710622868830024537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43489739807081912553349691 65234609710622868830024537)
      ·
        refine ⟨48925957282967151622518403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65234609710622868830024537 48925957282967151622518403)
        ·
          refine ⟨73388935924450727433777605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48925957282967151622518403 73388935924450727433777605)
          ·
            refine ⟨13760425485834511393833301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73388935924450727433777605 13760425485834511393833301)
            ·
              refine ⟨40313746540530795099121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13760425485834511393833301 40313746540530795099121)
              ·
                rfl

theorem cell22_3179685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 10].length) (baseStart_3179685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179685 prefixEnd_3179685 := by exact prefixLift 3179685
  have htrace : WordTrace (prefixWord ++ tailWord_3179685) baseStart_3179685 baseEnd_3179685 := by
    simpa [prefixWord, tailWord_3179685, baseEnd_3179685] using wordTrace_append hprefix tailTrace_3179685
  have hstable : (prefixWord ++ tailWord_3179685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179685).length < 2 ^ (prefixWord ++ tailWord_3179685).sum := by decide
  have hdescent : baseEnd_3179685 < baseStart_3179685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179715 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 4, 6]
def baseStart_3179715 : Nat := 118140960795 + 3179715 * 2 ^ 59
def prefixEnd_3179715 : Nat := 4983230072969 + 3 ^ 40 * 3179715 * 2
def baseEnd_3179715 : Nat := 1088481426207421389426175

theorem tailTrace_3179715 : CollatzResearch.WordTrace tailWord_3179715 prefixEnd_3179715 1088481426207421389426175 := by
  unfold tailWord_3179715
  simp only [CollatzResearch.WordTrace]
  refine ⟨115973733675443081932524599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77315822450295387955016399 115973733675443081932524599)
  ·
    refine ⟨173960600513164622898786899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115973733675443081932524599 173960600513164622898786899)
    ·
      refine ⟨260940900769746934348180349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173960600513164622898786899 260940900769746934348180349)
      ·
        refine ⟨97852837788655100380567631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260940900769746934348180349 97852837788655100380567631)
        ·
          refine ⟨146779256682982650570851447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97852837788655100380567631 146779256682982650570851447)
          ·
            refine ⟨220168885024473975856277171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146779256682982650570851447 220168885024473975856277171)
            ·
              refine ⟨330253327536710963784415757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220168885024473975856277171 330253327536710963784415757)
              ·
                refine ⟨123844997826266611419155909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330253327536710963784415757 123844997826266611419155909)
                ·
                  refine ⟨23220937092424989641091733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123844997826266611419155909 23220937092424989641091733)
                  ·
                    refine ⟨1088481426207421389426175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23220937092424989641091733 1088481426207421389426175)
                    ·
                      rfl

theorem cell22_3179715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_3179715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179715 prefixEnd_3179715 := by exact prefixLift 3179715
  have htrace : WordTrace (prefixWord ++ tailWord_3179715) baseStart_3179715 baseEnd_3179715 := by
    simpa [prefixWord, tailWord_3179715, baseEnd_3179715] using wordTrace_append hprefix tailTrace_3179715
  have hstable : (prefixWord ++ tailWord_3179715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179715).length < 2 ^ (prefixWord ++ tailWord_3179715).sum := by decide
  have hdescent : baseEnd_3179715 < baseStart_3179715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179717 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_3179717 : Nat := 118140960795 + 3179717 * 2 ^ 59
def prefixEnd_3179717 : Nat := 4983230072969 + 3 ^ 40 * 3179717 * 2
def baseEnd_3179717 : Nat := 1088482110848294050876169

theorem tailTrace_3179717 : CollatzResearch.WordTrace tailWord_3179717 prefixEnd_3179717 1088482110848294050876169 := by
  unfold tailWord_3179717
  simp only [CollatzResearch.WordTrace]
  refine ⟨115973806621435836274097405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77315871080957224182731603 115973806621435836274097405)
  ·
    refine ⟨43490177483038438602786527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115973806621435836274097405 43490177483038438602786527)
    ·
      refine ⟨65235266224557657904179791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43490177483038438602786527 65235266224557657904179791)
      ·
        refine ⟨97852899336836486856269687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65235266224557657904179791 97852899336836486856269687)
        ·
          refine ⟨146779349005254730284404531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97852899336836486856269687 146779349005254730284404531)
          ·
            refine ⟨220169023507882095426606797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146779349005254730284404531 220169023507882095426606797)
            ·
              refine ⟨82563383815455785784977549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220169023507882095426606797 82563383815455785784977549)
              ·
                refine ⟨30961268930795919669366581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82563383815455785784977549 30961268930795919669366581)
                ·
                  refine ⟨2902618962262117469003117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30961268930795919669366581 2902618962262117469003117)
                  ·
                    refine ⟨1088482110848294050876169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902618962262117469003117 1088482110848294050876169)
                    ·
                      rfl

theorem cell22_3179717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_3179717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179717 prefixEnd_3179717 := by exact prefixLift 3179717
  have htrace : WordTrace (prefixWord ++ tailWord_3179717) baseStart_3179717 baseEnd_3179717 := by
    simpa [prefixWord, tailWord_3179717, baseEnd_3179717] using wordTrace_append hprefix tailTrace_3179717
  have hstable : (prefixWord ++ tailWord_3179717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179717).length < 2 ^ (prefixWord ++ tailWord_3179717).sum := by decide
  have hdescent : baseEnd_3179717 < baseStart_3179717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179841 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3179841 : Nat := 118140960795 + 3179841 * 2 ^ 59
def prefixEnd_3179841 : Nat := 4983230072969 + 3 ^ 40 * 3179841 * 2
def baseEnd_3179841 : Nat := 1088524558582399060775789

theorem tailTrace_3179841 : CollatzResearch.WordTrace tailWord_3179841 prefixEnd_3179841 1088524558582399060775789 := by
  unfold tailWord_3179841
  simp only [CollatzResearch.WordTrace]
  refine ⟨115978329272986605451611377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77318886181991070301074251 115978329272986605451611377)
  ·
    refine ⟨86983746954739954088708533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115978329272986605451611377 86983746954739954088708533)
    ·
      refine ⟨8154726277006870695816425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86983746954739954088708533 8154726277006870695816425)
      ·
        refine ⟨6116044707755153021862319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8154726277006870695816425 6116044707755153021862319)
        ·
          refine ⟨9174067061632729532793479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6116044707755153021862319 9174067061632729532793479)
          ·
            refine ⟨13761100592449094299190219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9174067061632729532793479 13761100592449094299190219)
            ·
              refine ⟨20641650888673641448785329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13761100592449094299190219 20641650888673641448785329)
              ·
                refine ⟨15481238166505231086588997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20641650888673641448785329 15481238166505231086588997)
                ·
                  refine ⟨2902732156219730828735437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15481238166505231086588997 2902732156219730828735437)
                  ·
                    refine ⟨1088524558582399060775789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902732156219730828735437 1088524558582399060775789)
                    ·
                      rfl

theorem cell22_3179841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3179841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179841 prefixEnd_3179841 := by exact prefixLift 3179841
  have htrace : WordTrace (prefixWord ++ tailWord_3179841) baseStart_3179841 baseEnd_3179841 := by
    simpa [prefixWord, tailWord_3179841, baseEnd_3179841] using wordTrace_append hprefix tailTrace_3179841
  have hstable : (prefixWord ++ tailWord_3179841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179841).length < 2 ^ (prefixWord ++ tailWord_3179841).sum := by decide
  have hdescent : baseEnd_3179841 < baseStart_3179841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179929 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_3179929 : Nat := 118140960795 + 3179929 * 2 ^ 59
def prefixEnd_3179929 : Nat := 4983230072969 + 3 ^ 40 * 3179929 * 2
def baseEnd_3179929 : Nat := 1088554682780796164575519

theorem tailTrace_3179929 : CollatzResearch.WordTrace tailWord_3179929 prefixEnd_3179929 1088554682780796164575519 := by
  unfold tailWord_3179929
  simp only [CollatzResearch.WordTrace]
  refine ⟨115981538896667796480814841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77321025931111864320543227 115981538896667796480814841)
  ·
    refine ⟨86986154172500847360611131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115981538896667796480814841 86986154172500847360611131)
    ·
      refine ⟨130479231258751271040916697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86986154172500847360611131 130479231258751271040916697)
      ·
        refine ⟨97859423444063453280687523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130479231258751271040916697 97859423444063453280687523)
        ·
          refine ⟨146789135166095179921031285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97859423444063453280687523 146789135166095179921031285)
          ·
            refine ⟨13761481421821423117596683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146789135166095179921031285 13761481421821423117596683)
            ·
              refine ⟨20642222132732134676395025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13761481421821423117596683 20642222132732134676395025)
              ·
                refine ⟨15481666599549101007296269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20642222132732134676395025 15481666599549101007296269)
                ·
                  refine ⟨5805624974830912877736101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15481666599549101007296269 5805624974830912877736101)
                  ·
                    refine ⟨1088554682780796164575519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5805624974830912877736101 1088554682780796164575519)
                    ·
                      rfl

theorem cell22_3179929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_3179929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179929 prefixEnd_3179929 := by exact prefixLift 3179929
  have htrace : WordTrace (prefixWord ++ tailWord_3179929) baseStart_3179929 baseEnd_3179929 := by
    simpa [prefixWord, tailWord_3179929, baseEnd_3179929] using wordTrace_append hprefix tailTrace_3179929
  have hstable : (prefixWord ++ tailWord_3179929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179929).length < 2 ^ (prefixWord ++ tailWord_3179929).sum := by decide
  have hdescent : baseEnd_3179929 < baseStart_3179929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179959 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3179959 : Nat := 118140960795 + 3179959 * 2 ^ 59
def prefixEnd_3179959 : Nat := 4983230072969 + 3 ^ 40 * 3179959 * 2
def baseEnd_3179959 : Nat := 1088564952393886086325427

theorem tailTrace_3179959 : CollatzResearch.WordTrace tailWord_3179959 prefixEnd_3179959 1088564952393886086325427 := by
  unfold tailWord_3179959
  simp only [CollatzResearch.WordTrace]
  refine ⟨115982633086559111604406931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77321755391039407736271287 115982633086559111604406931)
  ·
    refine ⟨173973949629838667406610397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115982633086559111604406931 173973949629838667406610397)
    ·
      refine ⟨65240231111189500277478899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173973949629838667406610397 65240231111189500277478899)
      ·
        refine ⟨97860346666784250416218349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65240231111189500277478899 97860346666784250416218349)
        ·
          refine ⟨36697630000044093906081881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97860346666784250416218349 36697630000044093906081881)
          ·
            refine ⟨27523222500033070429561411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36697630000044093906081881 27523222500033070429561411)
            ·
              refine ⟨41284833750049605644342117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27523222500033070429561411 41284833750049605644342117)
              ·
                refine ⟨7740906328134301058314147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41284833750049605644342117 7740906328134301058314147)
                ·
                  refine ⟨11611359492201451587471221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7740906328134301058314147 11611359492201451587471221)
                  ·
                    refine ⟨1088564952393886086325427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11611359492201451587471221 1088564952393886086325427)
                    ·
                      rfl

theorem cell22_3179959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3179959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179959 prefixEnd_3179959 := by exact prefixLift 3179959
  have htrace : WordTrace (prefixWord ++ tailWord_3179959) baseStart_3179959 baseEnd_3179959 := by
    simpa [prefixWord, tailWord_3179959, baseEnd_3179959] using wordTrace_append hprefix tailTrace_3179959
  have hstable : (prefixWord ++ tailWord_3179959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179959).length < 2 ^ (prefixWord ++ tailWord_3179959).sum := by decide
  have hdescent : baseEnd_3179959 < baseStart_3179959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179976 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 4, 3]
def baseStart_3179976 : Nat := 118140960795 + 3179976 * 2 ^ 59
def prefixEnd_3179976 : Nat := 4983230072969 + 3 ^ 40 * 3179976 * 2
def baseEnd_3179976 : Nat := 1088570771841303708650375

theorem tailTrace_3179976 : CollatzResearch.WordTrace tailWord_3179976 prefixEnd_3179976 1088570771841303708650375 := by
  unfold tailWord_3179976
  simp only [CollatzResearch.WordTrace]
  refine ⟨57991626563748761753887891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77322168751665015671850521 57991626563748761753887891)
  ·
    refine ⟨86987439845623142630831837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57991626563748761753887891 86987439845623142630831837)
    ·
      refine ⟨32620289942108678486561939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86987439845623142630831837 32620289942108678486561939)
      ·
        refine ⟨48930434913163017729842909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32620289942108678486561939 48930434913163017729842909)
        ·
          refine ⟨18348913092436131648691091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48930434913163017729842909 18348913092436131648691091)
          ·
            refine ⟨27523369638654197473036637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18348913092436131648691091 27523369638654197473036637)
            ·
              refine ⟨10321263614495324052388739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27523369638654197473036637 10321263614495324052388739)
              ·
                refine ⟨15481895421742986078583109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10321263614495324052388739 15481895421742986078583109)
                ·
                  refine ⟨2902855391576809889734333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15481895421742986078583109 2902855391576809889734333)
                  ·
                    refine ⟨1088570771841303708650375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902855391576809889734333 1088570771841303708650375)
                    ·
                      rfl

theorem cell22_3179976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_3179976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179976 prefixEnd_3179976 := by exact prefixLift 3179976
  have htrace : WordTrace (prefixWord ++ tailWord_3179976) baseStart_3179976 baseEnd_3179976 := by
    simpa [prefixWord, tailWord_3179976, baseEnd_3179976] using wordTrace_append hprefix tailTrace_3179976
  have hstable : (prefixWord ++ tailWord_3179976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179976).length < 2 ^ (prefixWord ++ tailWord_3179976).sum := by decide
  have hdescent : baseEnd_3179976 < baseStart_3179976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3179989 : List Nat := [1, 3, 2, 3, 1, 1, 2, 9]
def baseStart_3179989 : Nat := 118140960795 + 3179989 * 2 ^ 59
def prefixEnd_3179989 : Nat := 4983230072969 + 3 ^ 40 * 3179989 * 2
def baseEnd_3179989 : Nat := 120952802445219556452815

theorem tailTrace_3179989 : CollatzResearch.WordTrace tailWord_3179989 prefixEnd_3179989 120952802445219556452815 := by
  unfold tailWord_3179989
  simp only [CollatzResearch.WordTrace]
  refine ⟨115983727276450426727999021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77322484850966951151999347 115983727276450426727999021)
  ·
    refine ⟨43493897728668910022999633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115983727276450426727999021 43493897728668910022999633)
    ·
      refine ⟨32620423296501682517249725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43493897728668910022999633 32620423296501682517249725)
      ·
        refine ⟨12232658736188130943968647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32620423296501682517249725 12232658736188130943968647)
        ·
          refine ⟨18348988104282196415952971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12232658736188130943968647 18348988104282196415952971)
          ·
            refine ⟨27523482156423294623929457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18348988104282196415952971 27523482156423294623929457)
            ·
              refine ⟨20642611617317470967947093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27523482156423294623929457 20642611617317470967947093)
              ·
                refine ⟨120952802445219556452815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20642611617317470967947093 120952802445219556452815)
                ·
                  rfl

theorem cell22_3179989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 9].length) (baseStart_3179989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3179989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3179989 prefixEnd_3179989 := by exact prefixLift 3179989
  have htrace : WordTrace (prefixWord ++ tailWord_3179989) baseStart_3179989 baseEnd_3179989 := by
    simpa [prefixWord, tailWord_3179989, baseEnd_3179989] using wordTrace_append hprefix tailTrace_3179989
  have hstable : (prefixWord ++ tailWord_3179989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3179989).length < 2 ^ (prefixWord ++ tailWord_3179989).sum := by decide
  have hdescent : baseEnd_3179989 < baseStart_3179989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3179989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180049 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3180049 : Nat := 118140960795 + 3180049 * 2 ^ 59
def prefixEnd_3180049 : Nat := 4983230072969 + 3 ^ 40 * 3180049 * 2
def baseEnd_3180049 : Nat := 1088595761233155851575151

theorem tailTrace_3180049 : CollatzResearch.WordTrace tailWord_3180049 prefixEnd_3180049 1088595761233155851575151 := by
  unfold tailWord_3180049
  simp only [CollatzResearch.WordTrace]
  refine ⟨115985915656233056975183201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77323943770822037983455467 115985915656233056975183201)
  ·
    refine ⟨86989436742174792731387401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115985915656233056975183201 86989436742174792731387401)
    ·
      refine ⟨65242077556631094548540551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86989436742174792731387401 65242077556631094548540551)
      ·
        refine ⟨97863116334946641822810827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65242077556631094548540551 97863116334946641822810827)
        ·
          refine ⟨146794674502419962734216241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97863116334946641822810827 146794674502419962734216241)
          ·
            refine ⟨110096005876814972050662181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146794674502419962734216241 110096005876814972050662181)
            ·
              refine ⟨20643001101902807259499159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110096005876814972050662181 20643001101902807259499159)
              ·
                refine ⟨30964501652854210889248739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20643001101902807259499159 30964501652854210889248739)
                ·
                  refine ⟨46446752479281316333873109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30964501652854210889248739 46446752479281316333873109)
                  ·
                    refine ⟨1088595761233155851575151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46446752479281316333873109 1088595761233155851575151)
                    ·
                      rfl

theorem cell22_3180049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3180049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180049 prefixEnd_3180049 := by exact prefixLift 3180049
  have htrace : WordTrace (prefixWord ++ tailWord_3180049) baseStart_3180049 baseEnd_3180049 := by
    simpa [prefixWord, tailWord_3180049, baseEnd_3180049] using wordTrace_append hprefix tailTrace_3180049
  have hstable : (prefixWord ++ tailWord_3180049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180049).length < 2 ^ (prefixWord ++ tailWord_3180049).sum := by decide
  have hdescent : baseEnd_3180049 < baseStart_3180049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180051 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 5]
def baseStart_3180051 : Nat := 118140960795 + 3180051 * 2 ^ 59
def prefixEnd_3180051 : Nat := 4983230072969 + 3 ^ 40 * 3180051 * 2
def baseEnd_3180051 : Nat := 362865481958009504341715

theorem tailTrace_3180051 : CollatzResearch.WordTrace tailWord_3180051 prefixEnd_3180051 362865481958009504341715 := by
  unfold tailWord_3180051
  simp only [CollatzResearch.WordTrace]
  refine ⟨115985988602225811316756007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77323992401483874211170671 115985988602225811316756007)
  ·
    refine ⟨173978982903338716975134011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115985988602225811316756007 173978982903338716975134011)
    ·
      refine ⟨260968474355008075462701017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173978982903338716975134011 260968474355008075462701017)
      ·
        refine ⟨195726355766256056597025763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260968474355008075462701017 195726355766256056597025763)
        ·
          refine ⟨293589533649384084895538645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195726355766256056597025763 293589533649384084895538645)
          ·
            refine ⟨6881004694907439489739187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 293589533649384084895538645 6881004694907439489739187)
            ·
              refine ⟨10321507042361159234608781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881004694907439489739187 10321507042361159234608781)
              ·
                refine ⟨3870565140885434712978293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10321507042361159234608781 3870565140885434712978293)
                ·
                  refine ⟨362865481958009504341715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870565140885434712978293 362865481958009504341715)
                  ·
                    rfl

theorem cell22_3180051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 5].length) (baseStart_3180051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180051 prefixEnd_3180051 := by exact prefixLift 3180051
  have htrace : WordTrace (prefixWord ++ tailWord_3180051) baseStart_3180051 baseEnd_3180051 := by
    simpa [prefixWord, tailWord_3180051, baseEnd_3180051] using wordTrace_append hprefix tailTrace_3180051
  have hstable : (prefixWord ++ tailWord_3180051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180051).length < 2 ^ (prefixWord ++ tailWord_3180051).sum := by decide
  have hdescent : baseEnd_3180051 < baseStart_3180051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180111 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 6, 3]
def baseStart_3180111 : Nat := 118140960795 + 3180111 * 2 ^ 59
def prefixEnd_3180111 : Nat := 4983230072969 + 3 ^ 40 * 3180111 * 2
def baseEnd_3180111 : Nat := 1088616985100208356524961

theorem tailTrace_3180111 : CollatzResearch.WordTrace tailWord_3180111 prefixEnd_3180111 1088616985100208356524961 := by
  unfold tailWord_3180111
  simp only [CollatzResearch.WordTrace]
  refine ⟨115988176982008441563940187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77325451321338961042626791 115988176982008441563940187)
  ·
    refine ⟨173982265473012662345910281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115988176982008441563940187 173982265473012662345910281)
    ·
      refine ⟨130486699104759496759432711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173982265473012662345910281 130486699104759496759432711)
      ·
        refine ⟨195730048657139245139149067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130486699104759496759432711 195730048657139245139149067)
        ·
          refine ⟨293595072985708867708723601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195730048657139245139149067 293595072985708867708723601)
          ·
            refine ⟨220196304739281650781542701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293595072985708867708723601 220196304739281650781542701)
            ·
              refine ⟨82573614277230619043078513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220196304739281650781542701 82573614277230619043078513)
              ·
                refine ⟨61930210707922964282308885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82573614277230619043078513 61930210707922964282308885)
                ·
                  refine ⟨2902978626933888950733229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61930210707922964282308885 2902978626933888950733229)
                  ·
                    refine ⟨1088616985100208356524961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902978626933888950733229 1088616985100208356524961)
                    ·
                      rfl

theorem cell22_3180111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_3180111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180111 prefixEnd_3180111 := by exact prefixLift 3180111
  have htrace : WordTrace (prefixWord ++ tailWord_3180111) baseStart_3180111 baseEnd_3180111 := by
    simpa [prefixWord, tailWord_3180111, baseEnd_3180111] using wordTrace_append hprefix tailTrace_3180111
  have hstable : (prefixWord ++ tailWord_3180111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180111).length < 2 ^ (prefixWord ++ tailWord_3180111).sum := by decide
  have hdescent : baseEnd_3180111 < baseStart_3180111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180207 : List Nat := [1, 1, 2, 1, 2, 4, 5, 2, 1, 3]
def baseStart_3180207 : Nat := 118140960795 + 3180207 * 2 ^ 59
def prefixEnd_3180207 : Nat := 4983230072969 + 3 ^ 40 * 3180207 * 2
def baseEnd_3180207 : Nat := 1088649847862096106124667

theorem tailTrace_3180207 : CollatzResearch.WordTrace tailWord_3180207 prefixEnd_3180207 1088649847862096106124667 := by
  unfold tailWord_3180207
  simp only [CollatzResearch.WordTrace]
  refine ⟨115991678389660649959434875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77327785593107099972956583 115991678389660649959434875)
  ·
    refine ⟨173987517584490974939152313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115991678389660649959434875 173987517584490974939152313)
    ·
      refine ⟨130490638188368231204364235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173987517584490974939152313 130490638188368231204364235)
      ·
        refine ⟨195735957282552346806546353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130490638188368231204364235 195735957282552346806546353)
        ·
          refine ⟨146801967961914260104909765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195735957282552346806546353 146801967961914260104909765)
          ·
            refine ⟨27525368992858923769670581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146801967961914260104909765 27525368992858923769670581)
            ·
              refine ⟨2580503343080524103406617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27525368992858923769670581 2580503343080524103406617)
              ·
                refine ⟨1935377507310393077554963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580503343080524103406617 1935377507310393077554963)
                ·
                  refine ⟨2903066260965589616332445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935377507310393077554963 2903066260965589616332445)
                  ·
                    refine ⟨1088649847862096106124667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903066260965589616332445 1088649847862096106124667)
                    ·
                      rfl

theorem cell22_3180207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 1, 3].length) (baseStart_3180207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180207 prefixEnd_3180207 := by exact prefixLift 3180207
  have htrace : WordTrace (prefixWord ++ tailWord_3180207) baseStart_3180207 baseEnd_3180207 := by
    simpa [prefixWord, tailWord_3180207, baseEnd_3180207] using wordTrace_append hprefix tailTrace_3180207
  have hstable : (prefixWord ++ tailWord_3180207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180207).length < 2 ^ (prefixWord ++ tailWord_3180207).sum := by decide
  have hdescent : baseEnd_3180207 < baseStart_3180207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180220 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 5]
def baseStart_3180220 : Nat := 118140960795 + 3180220 * 2 ^ 59
def prefixEnd_3180220 : Nat := 4983230072969 + 3 ^ 40 * 3180220 * 2
def baseEnd_3180220 : Nat := 362884766009256135183209

theorem tailTrace_3180220 : CollatzResearch.WordTrace tailWord_3180220 prefixEnd_3180220 362884766009256135183209 := by
  unfold tailWord_3180220
  simp only [CollatzResearch.WordTrace]
  refine ⟨57996076269306776589829057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77328101692409035453105409 57996076269306776589829057)
  ·
    refine ⟨43497057201980082442371793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57996076269306776589829057 43497057201980082442371793)
    ·
      refine ⟨32622792901485061831778845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43497057201980082442371793 32622792901485061831778845)
      ·
        refine ⟨12233547338056898186917067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32622792901485061831778845 12233547338056898186917067)
        ·
          refine ⟨18350321007085347280375601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12233547338056898186917067 18350321007085347280375601)
          ·
            refine ⟨13762740755314010460281701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18350321007085347280375601 13762740755314010460281701)
            ·
              refine ⟨2580513891621376961302819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13762740755314010460281701 2580513891621376961302819)
              ·
                refine ⟨3870770837432065441954229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580513891621376961302819 3870770837432065441954229)
                ·
                  refine ⟨362884766009256135183209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870770837432065441954229 362884766009256135183209)
                  ·
                    rfl

theorem cell22_3180220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_3180220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180220 prefixEnd_3180220 := by exact prefixLift 3180220
  have htrace : WordTrace (prefixWord ++ tailWord_3180220) baseStart_3180220 baseEnd_3180220 := by
    simpa [prefixWord, tailWord_3180220, baseEnd_3180220] using wordTrace_append hprefix tailTrace_3180220
  have hstable : (prefixWord ++ tailWord_3180220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180220).length < 2 ^ (prefixWord ++ tailWord_3180220).sum := by decide
  have hdescent : baseEnd_3180220 < baseStart_3180220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180231 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 8]
def baseStart_3180231 : Nat := 118140960795 + 3180231 * 2 ^ 59
def prefixEnd_3180231 : Nat := 4983230072969 + 3 ^ 40 * 3180231 * 2
def baseEnd_3180231 : Nat := 362886021184189347841531

theorem tailTrace_3180231 : CollatzResearch.WordTrace tailWord_3180231 prefixEnd_3180231 362886021184189347841531 := by
  unfold tailWord_3180231
  simp only [CollatzResearch.WordTrace]
  refine ⟨115992553741573702058308547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77328369161049134705539031 115992553741573702058308547)
  ·
    refine ⟨173988830612360553087462821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115992553741573702058308547 173988830612360553087462821)
    ·
      refine ⟨32622905739817603703899279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173988830612360553087462821 32622905739817603703899279)
      ·
        refine ⟨48934358609726405555848919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32622905739817603703899279 48934358609726405555848919)
        ·
          refine ⟨73401537914589608333773379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48934358609726405555848919 73401537914589608333773379)
          ·
            refine ⟨110102306871884412500660069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73401537914589608333773379 110102306871884412500660069)
            ·
              refine ⟨20644182538478327343873763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110102306871884412500660069 20644182538478327343873763)
              ·
                refine ⟨30966273807717491015810645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20644182538478327343873763 30966273807717491015810645)
                ·
                  refine ⟨362886021184189347841531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30966273807717491015810645 362886021184189347841531)
                  ·
                    rfl

theorem cell22_3180231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 8].length) (baseStart_3180231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180231 prefixEnd_3180231 := by exact prefixLift 3180231
  have htrace : WordTrace (prefixWord ++ tailWord_3180231) baseStart_3180231 baseEnd_3180231 := by
    simpa [prefixWord, tailWord_3180231, baseEnd_3180231] using wordTrace_append hprefix tailTrace_3180231
  have hstable : (prefixWord ++ tailWord_3180231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180231).length < 2 ^ (prefixWord ++ tailWord_3180231).sum := by decide
  have hdescent : baseEnd_3180231 < baseStart_3180231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180295 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3180295 : Nat := 118140960795 + 3180295 * 2 ^ 59
def prefixEnd_3180295 : Nat := 4983230072969 + 3 ^ 40 * 3180295 * 2
def baseEnd_3180295 : Nat := 1088679972060493209924397

theorem tailTrace_3180295 : CollatzResearch.WordTrace tailWord_3180295 prefixEnd_3180295 1088679972060493209924397 := by
  unfold tailWord_3180295
  simp only [CollatzResearch.WordTrace]
  refine ⟨115994888013341840988638339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77329925342227893992425559 115994888013341840988638339)
  ·
    refine ⟨173992332020012761482957509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115994888013341840988638339 173992332020012761482957509)
    ·
      refine ⟨32623562253752392778054533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173992332020012761482957509 32623562253752392778054533)
      ·
        refine ⟨6116917922578573645885225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32623562253752392778054533 6116917922578573645885225)
        ·
          refine ⟨4587688441933930234413919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6116917922578573645885225 4587688441933930234413919)
          ·
            refine ⟨6881532662900895351620879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587688441933930234413919 6881532662900895351620879)
            ·
              refine ⟨10322298994351343027431319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881532662900895351620879 10322298994351343027431319)
              ·
                refine ⟨15483448491527014541146979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10322298994351343027431319 15483448491527014541146979)
                ·
                  refine ⟨23225172737290521811720469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15483448491527014541146979 23225172737290521811720469)
                  ·
                    refine ⟨1088679972060493209924397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23225172737290521811720469 1088679972060493209924397)
                    ·
                      rfl

theorem cell22_3180295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3180295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180295 prefixEnd_3180295 := by exact prefixLift 3180295
  have htrace : WordTrace (prefixWord ++ tailWord_3180295) baseStart_3180295 baseEnd_3180295 := by
    simpa [prefixWord, tailWord_3180295, baseEnd_3180295] using wordTrace_append hprefix tailTrace_3180295
  have hstable : (prefixWord ++ tailWord_3180295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180295).length < 2 ^ (prefixWord ++ tailWord_3180295).sum := by decide
  have hdescent : baseEnd_3180295 < baseStart_3180295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180325 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_3180325 : Nat := 118140960795 + 3180325 * 2 ^ 59
def prefixEnd_3180325 : Nat := 4983230072969 + 3 ^ 40 * 3180325 * 2
def baseEnd_3180325 : Nat := 1088690241673583131674305

theorem tailTrace_3180325 : CollatzResearch.WordTrace tailWord_3180325 prefixEnd_3180325 1088690241673583131674305 := by
  unfold tailWord_3180325
  simp only [CollatzResearch.WordTrace]
  refine ⟨115995982203233156112230429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77330654802155437408153619 115995982203233156112230429)
  ·
    refine ⟨43498493326212433542086411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115995982203233156112230429 43498493326212433542086411)
    ·
      refine ⟨65247739989318650313129617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43498493326212433542086411 65247739989318650313129617)
      ·
        refine ⟨48935804991988987734847213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65247739989318650313129617 48935804991988987734847213)
        ·
          refine ⟨18350926871995870400567705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48935804991988987734847213 18350926871995870400567705)
          ·
            refine ⟨13763195153996902800425779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18350926871995870400567705 13763195153996902800425779)
            ·
              refine ⟨20644792730995354200638669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13763195153996902800425779 20644792730995354200638669)
              ·
                refine ⟨7741797274123257825239501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20644792730995354200638669 7741797274123257825239501)
                ·
                  refine ⟨2903173977796221684464813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7741797274123257825239501 2903173977796221684464813)
                  ·
                    refine ⟨1088690241673583131674305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903173977796221684464813 1088690241673583131674305)
                    ·
                      rfl

theorem cell22_3180325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_3180325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180325 prefixEnd_3180325 := by exact prefixLift 3180325
  have htrace : WordTrace (prefixWord ++ tailWord_3180325) baseStart_3180325 baseEnd_3180325 := by
    simpa [prefixWord, tailWord_3180325, baseEnd_3180325] using wordTrace_append hprefix tailTrace_3180325
  have hstable : (prefixWord ++ tailWord_3180325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180325).length < 2 ^ (prefixWord ++ tailWord_3180325).sum := by decide
  have hdescent : baseEnd_3180325 < baseStart_3180325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180368 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_3180368 : Nat := 118140960795 + 3180368 * 2 ^ 59
def prefixEnd_3180368 : Nat := 4983230072969 + 3 ^ 40 * 3180368 * 2
def baseEnd_3180368 : Nat := 1088704961452345352849173

theorem tailTrace_3180368 : CollatzResearch.WordTrace tailWord_3180368 prefixEnd_3180368 1088704961452345352849173 := by
  unfold tailWord_3180368
  simp only [CollatzResearch.WordTrace]
  refine ⟨57998775271038687228022879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77331700361384916304030505 57998775271038687228022879)
  ·
    refine ⟨86998162906558030842034319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57998775271038687228022879 86998162906558030842034319)
    ·
      refine ⟨130497244359837046263051479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86998162906558030842034319 130497244359837046263051479)
      ·
        refine ⟨195745866539755569394577219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130497244359837046263051479 195745866539755569394577219)
        ·
          refine ⟨293618799809633354091865829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195745866539755569394577219 293618799809633354091865829)
          ·
            refine ⟨55053524964306253892224843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293618799809633354091865829 55053524964306253892224843)
            ·
              refine ⟨82580287446459380838337265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55053524964306253892224843 82580287446459380838337265)
              ·
                refine ⟨61935215584844535628752949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82580287446459380838337265 61935215584844535628752949)
                ·
                  refine ⟨5806426461079175215195589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61935215584844535628752949 5806426461079175215195589)
                  ·
                    refine ⟨1088704961452345352849173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5806426461079175215195589 1088704961452345352849173)
                    ·
                      rfl

theorem cell22_3180368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_3180368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180368 prefixEnd_3180368 := by exact prefixLift 3180368
  have htrace : WordTrace (prefixWord ++ tailWord_3180368) baseStart_3180368 baseEnd_3180368 := by
    simpa [prefixWord, tailWord_3180368, baseEnd_3180368] using wordTrace_append hprefix tailTrace_3180368
  have hstable : (prefixWord ++ tailWord_3180368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180368).length < 2 ^ (prefixWord ++ tailWord_3180368).sum := by decide
  have hdescent : baseEnd_3180368 < baseStart_3180368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180434 : List Nat := [3, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_3180434 : Nat := 118140960795 + 3180434 * 2 ^ 59
def prefixEnd_3180434 : Nat := 4983230072969 + 3 ^ 40 * 3180434 * 2
def baseEnd_3180434 : Nat := 362909184867047726899657

theorem tailTrace_3180434 : CollatzResearch.WordTrace tailWord_3180434 prefixEnd_3180434 362909184867047726899657 := by
  unfold tailWord_3180434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28999989439959566931987089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77333305173225511818632237 28999989439959566931987089)
  ·
    refine ⟨21749992079969675198990317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28999989439959566931987089 21749992079969675198990317)
    ·
      refine ⟨8156247029988628199621369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21749992079969675198990317 8156247029988628199621369)
      ·
        refine ⟨6117185272491471149716027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8156247029988628199621369 6117185272491471149716027)
        ·
          refine ⟨9175777908737206724574041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117185272491471149716027 9175777908737206724574041)
          ·
            refine ⟨6881833431552905043430531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9175777908737206724574041 6881833431552905043430531)
            ·
              refine ⟨10322750147329357565145797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881833431552905043430531 10322750147329357565145797)
              ·
                refine ⟨1935515652624254543464837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10322750147329357565145797 1935515652624254543464837)
                ·
                  refine ⟨362909184867047726899657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1935515652624254543464837 362909184867047726899657)
                  ·
                    rfl

theorem cell22_3180434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_3180434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180434 prefixEnd_3180434 := by exact prefixLift 3180434
  have htrace : WordTrace (prefixWord ++ tailWord_3180434) baseStart_3180434 baseEnd_3180434 := by
    simpa [prefixWord, tailWord_3180434, baseEnd_3180434] using wordTrace_append hprefix tailTrace_3180434
  have hstable : (prefixWord ++ tailWord_3180434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180434).length < 2 ^ (prefixWord ++ tailWord_3180434).sum := by decide
  have hdescent : baseEnd_3180434 < baseStart_3180434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180445 : List Nat := [1, 4, 2, 1, 2, 2, 3, 7]
def baseStart_3180445 : Nat := 118140960795 + 3180445 * 2 ^ 59
def prefixEnd_3180445 : Nat := 4983230072969 + 3 ^ 40 * 3180445 * 2
def baseEnd_3180445 : Nat := 120970146680660313185993

theorem tailTrace_3180445 : CollatzResearch.WordTrace tailWord_3180445 prefixEnd_3180445 120970146680660313185993 := by
  unfold tailWord_3180445
  simp only [CollatzResearch.WordTrace]
  refine ⟨116000358962798416606598789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77333572641865611071065859 116000358962798416606598789)
  ·
    refine ⟨21750067305524703113737273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116000358962798416606598789 21750067305524703113737273)
    ·
      refine ⟨16312550479143527335302955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21750067305524703113737273 16312550479143527335302955)
      ·
        refine ⟨24468825718715291002954433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16312550479143527335302955 24468825718715291002954433)
        ·
          refine ⟨18351619289036468252215825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24468825718715291002954433 18351619289036468252215825)
          ·
            refine ⟨13763714466777351189161869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18351619289036468252215825 13763714466777351189161869)
            ·
              refine ⟨5161392925041506695935701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13763714466777351189161869 5161392925041506695935701)
              ·
                refine ⟨120970146680660313185993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5161392925041506695935701 120970146680660313185993)
                ·
                  rfl

theorem cell22_3180445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 7].length) (baseStart_3180445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180445 prefixEnd_3180445 := by exact prefixLift 3180445
  have htrace : WordTrace (prefixWord ++ tailWord_3180445) baseStart_3180445 baseEnd_3180445 := by
    simpa [prefixWord, tailWord_3180445, baseEnd_3180445] using wordTrace_append hprefix tailTrace_3180445
  have hstable : (prefixWord ++ tailWord_3180445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180445).length < 2 ^ (prefixWord ++ tailWord_3180445).sum := by decide
  have hdescent : baseEnd_3180445 < baseStart_3180445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180494 : List Nat := [4, 1, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_3180494 : Nat := 118140960795 + 3180494 * 2 ^ 59
def prefixEnd_3180494 : Nat := 4983230072969 + 3 ^ 40 * 3180494 * 2
def baseEnd_3180494 : Nat := 1088748093827323024198787

theorem tailTrace_3180494 : CollatzResearch.WordTrace tailWord_3180494 prefixEnd_3180494 1088748093827323024198787 := by
  unfold tailWord_3180494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500268267452612246891567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77334764093080598650088357 14500268267452612246891567)
  ·
    refine ⟨21750402401178918370337351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14500268267452612246891567 21750402401178918370337351)
    ·
      refine ⟨32625603601768377555506027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21750402401178918370337351 32625603601768377555506027)
      ·
        refine ⟨48938405402652566333259041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32625603601768377555506027 48938405402652566333259041)
        ·
          refine ⟨36703804051989424749944281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48938405402652566333259041 36703804051989424749944281)
          ·
            refine ⟨27527853038992068562458211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36703804051989424749944281 27527853038992068562458211)
            ·
              refine ⟨41291779558488102843687317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27527853038992068562458211 41291779558488102843687317)
              ·
                refine ⟨1935552166804129820797843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41291779558488102843687317 1935552166804129820797843)
                ·
                  refine ⟨2903328250206194731196765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935552166804129820797843 2903328250206194731196765)
                  ·
                    refine ⟨1088748093827323024198787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903328250206194731196765 1088748093827323024198787)
                    ·
                      rfl

theorem cell22_3180494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_3180494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180494 prefixEnd_3180494 := by exact prefixLift 3180494
  have htrace : WordTrace (prefixWord ++ tailWord_3180494) baseStart_3180494 baseEnd_3180494 := by
    simpa [prefixWord, tailWord_3180494, baseEnd_3180494] using wordTrace_append hprefix tailTrace_3180494
  have hstable : (prefixWord ++ tailWord_3180494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180494).length < 2 ^ (prefixWord ++ tailWord_3180494).sum := by decide
  have hdescent : baseEnd_3180494 < baseStart_3180494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180537 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_3180537 : Nat := 118140960795 + 3180537 * 2 ^ 59
def prefixEnd_3180537 : Nat := 4983230072969 + 3 ^ 40 * 3180537 * 2
def baseEnd_3180537 : Nat := 1088762813606085245373655

theorem tailTrace_3180537 : CollatzResearch.WordTrace tailWord_3180537 prefixEnd_3180537 1088762813606085245373655 := by
  unfold tailWord_3180537
  simp only [CollatzResearch.WordTrace]
  refine ⟨116003714478465116318947865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77335809652310077545965243 116003714478465116318947865)
  ·
    refine ⟨87002785858848837239210899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116003714478465116318947865 87002785858848837239210899)
    ·
      refine ⟨130504178788273255858816349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87002785858848837239210899 130504178788273255858816349)
      ·
        refine ⟨48939067045602470947056131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130504178788273255858816349 48939067045602470947056131)
        ·
          refine ⟨73408600568403706420584197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48939067045602470947056131 73408600568403706420584197)
          ·
            refine ⟨13764112606575694953859537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73408600568403706420584197 13764112606575694953859537)
            ·
              refine ⟨10323084454931771215394653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13764112606575694953859537 10323084454931771215394653)
              ·
                refine ⟨3871156670599414205772995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323084454931771215394653 3871156670599414205772995)
                ·
                  refine ⟨5806735005899121308659493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871156670599414205772995 5806735005899121308659493)
                  ·
                    refine ⟨1088762813606085245373655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5806735005899121308659493 1088762813606085245373655)
                    ·
                      rfl

theorem cell22_3180537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_3180537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180537 prefixEnd_3180537 := by exact prefixLift 3180537
  have htrace : WordTrace (prefixWord ++ tailWord_3180537) baseStart_3180537 baseEnd_3180537 := by
    simpa [prefixWord, tailWord_3180537, baseEnd_3180537] using wordTrace_append hprefix tailTrace_3180537
  have hstable : (prefixWord ++ tailWord_3180537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180537).length < 2 ^ (prefixWord ++ tailWord_3180537).sum := by decide
  have hdescent : baseEnd_3180537 < baseStart_3180537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180601 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 2, 3]
def baseStart_3180601 : Nat := 118140960795 + 3180601 * 2 ^ 59
def prefixEnd_3180601 : Nat := 4983230072969 + 3 ^ 40 * 3180601 * 2
def baseEnd_3180601 : Nat := 1088784722114010411773459

theorem tailTrace_3180601 : CollatzResearch.WordTrace tailWord_3180601 prefixEnd_3180601 1088784722114010411773459 := by
  unfold tailWord_3180601
  simp only [CollatzResearch.WordTrace]
  refine ⟨116006048750233255249277657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77337365833488836832851771 116006048750233255249277657)
  ·
    refine ⟨87004536562674941436958243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116006048750233255249277657 87004536562674941436958243)
    ·
      refine ⟨130506804844012412155437365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87004536562674941436958243 130506804844012412155437365)
      ·
        refine ⟨12235012954126163639572253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130506804844012412155437365 12235012954126163639572253)
        ·
          refine ⟨4588129857797311364839595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12235012954126163639572253 4588129857797311364839595)
          ·
            refine ⟨6882194786695967047259393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588129857797311364839595 6882194786695967047259393)
            ·
              refine ⟨5161646090021975285444545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6882194786695967047259393 5161646090021975285444545)
              ·
                refine ⟨3871234567516481464083409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5161646090021975285444545 3871234567516481464083409)
                ·
                  refine ⟨2903425925637361098062557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871234567516481464083409 2903425925637361098062557)
                  ·
                    refine ⟨1088784722114010411773459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903425925637361098062557 1088784722114010411773459)
                    ·
                      rfl

theorem cell22_3180601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_3180601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180601 prefixEnd_3180601 := by exact prefixLift 3180601
  have htrace : WordTrace (prefixWord ++ tailWord_3180601) baseStart_3180601 baseEnd_3180601 := by
    simpa [prefixWord, tailWord_3180601, baseEnd_3180601] using wordTrace_append hprefix tailTrace_3180601
  have hstable : (prefixWord ++ tailWord_3180601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180601).length < 2 ^ (prefixWord ++ tailWord_3180601).sum := by decide
  have hdescent : baseEnd_3180601 < baseStart_3180601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180625 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 9]
def baseStart_3180625 : Nat := 118140960795 + 3180625 * 2 ^ 59
def prefixEnd_3180625 : Nat := 4983230072969 + 3 ^ 40 * 3180625 * 2
def baseEnd_3180625 : Nat := 362930979268160783057795

theorem tailTrace_3180625 : CollatzResearch.WordTrace tailWord_3180625 prefixEnd_3180625 362930979268160783057795 := by
  unfold tailWord_3180625
  simp only [CollatzResearch.WordTrace]
  refine ⟨116006924102146307348151329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77337949401430871565434219 116006924102146307348151329)
  ·
    refine ⟨87005193076609730511113497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116006924102146307348151329 87005193076609730511113497)
    ·
      refine ⟨65253894807457297883335123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87005193076609730511113497 65253894807457297883335123)
      ·
        refine ⟨97880842211185946825002685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65253894807457297883335123 97880842211185946825002685)
        ·
          refine ⟨36705315829194730059376007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97880842211185946825002685 36705315829194730059376007)
          ·
            refine ⟨55057973743792095089064011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36705315829194730059376007 55057973743792095089064011)
            ·
              refine ⟨82586960615688142633596017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55057973743792095089064011 82586960615688142633596017)
              ·
                refine ⟨61940220461766106975197013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82586960615688142633596017 61940220461766106975197013)
                ·
                  refine ⟨362930979268160783057795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61940220461766106975197013 362930979268160783057795)
                  ·
                    rfl

theorem cell22_3180625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_3180625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180625 prefixEnd_3180625 := by exact prefixLift 3180625
  have htrace : WordTrace (prefixWord ++ tailWord_3180625) baseStart_3180625 baseEnd_3180625 := by
    simpa [prefixWord, tailWord_3180625, baseEnd_3180625] using wordTrace_append hprefix tailTrace_3180625
  have hstable : (prefixWord ++ tailWord_3180625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180625).length < 2 ^ (prefixWord ++ tailWord_3180625).sum := by decide
  have hdescent : baseEnd_3180625 < baseStart_3180625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180629 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_3180629 : Nat := 118140960795 + 3180629 * 2 ^ 59
def prefixEnd_3180629 : Nat := 4983230072969 + 3 ^ 40 * 3180629 * 2
def baseEnd_3180629 : Nat := 1088794307086227672073373

theorem tailTrace_3180629 : CollatzResearch.WordTrace tailWord_3180629 prefixEnd_3180629 1088794307086227672073373 := by
  unfold tailWord_3180629
  simp only [CollatzResearch.WordTrace]
  refine ⟨116007069994131816031296941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77338046662754544020864627 116007069994131816031296941)
  ·
    refine ⟨43502651247799431011736353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116007069994131816031296941 43502651247799431011736353)
    ·
      refine ⟨32626988435849573258802265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43502651247799431011736353 32626988435849573258802265)
      ·
        refine ⟨24470241326887179944101699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32626988435849573258802265 24470241326887179944101699)
        ·
          refine ⟨36705361990330769916152549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24470241326887179944101699 36705361990330769916152549)
          ·
            refine ⟨6882255373187019359278603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36705361990330769916152549 6882255373187019359278603)
            ·
              refine ⟨10323383059780529038917905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882255373187019359278603 10323383059780529038917905)
              ·
                refine ⟨7742537294835396779188429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10323383059780529038917905 7742537294835396779188429)
                ·
                  refine ⟨2903451485563273792195661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7742537294835396779188429 2903451485563273792195661)
                  ·
                    refine ⟨1088794307086227672073373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903451485563273792195661 1088794307086227672073373)
                    ·
                      rfl

theorem cell22_3180629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_3180629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180629 prefixEnd_3180629 := by exact prefixLift 3180629
  have htrace : WordTrace (prefixWord ++ tailWord_3180629) baseStart_3180629 baseEnd_3180629 := by
    simpa [prefixWord, tailWord_3180629, baseEnd_3180629] using wordTrace_append hprefix tailTrace_3180629
  have hstable : (prefixWord ++ tailWord_3180629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180629).length < 2 ^ (prefixWord ++ tailWord_3180629).sum := by decide
  have hdescent : baseEnd_3180629 < baseStart_3180629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180706 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3180706 : Nat := 118140960795 + 3180706 * 2 ^ 59
def prefixEnd_3180706 : Nat := 4983230072969 + 3 ^ 40 * 3180706 * 2
def baseEnd_3180706 : Nat := 1088820665759825137898137

theorem tailTrace_3180706 : CollatzResearch.WordTrace tailWord_3180706 prefixEnd_3180706 1088820665759825137898137 := by
  unfold tailWord_3180706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29002469603713214545462493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77339918943235238787899981 29002469603713214545462493)
  ·
    refine ⟨10875926101392455454548435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29002469603713214545462493 10875926101392455454548435)
    ·
      refine ⟨16313889152088683181822653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875926101392455454548435 16313889152088683181822653)
      ·
        refine ⟨6117708432033256193183495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16313889152088683181822653 6117708432033256193183495)
        ·
          refine ⟨9176562648049884289775243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117708432033256193183495 9176562648049884289775243)
          ·
            refine ⟨13764843972074826434662865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176562648049884289775243 13764843972074826434662865)
            ·
              refine ⟨10323632979056119825997149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13764843972074826434662865 10323632979056119825997149)
              ·
                refine ⟨3871362367146044934748931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323632979056119825997149 3871362367146044934748931)
                ·
                  refine ⟨5807043550719067402123397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871362367146044934748931 5807043550719067402123397)
                  ·
                    refine ⟨1088820665759825137898137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807043550719067402123397 1088820665759825137898137)
                    ·
                      rfl

theorem cell22_3180706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3180706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180706 prefixEnd_3180706 := by exact prefixLift 3180706
  have htrace : WordTrace (prefixWord ++ tailWord_3180706) baseStart_3180706 baseEnd_3180706 := by
    simpa [prefixWord, tailWord_3180706, baseEnd_3180706] using wordTrace_append hprefix tailTrace_3180706
  have hstable : (prefixWord ++ tailWord_3180706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180706).length < 2 ^ (prefixWord ++ tailWord_3180706).sum := by decide
  have hdescent : baseEnd_3180706 < baseStart_3180706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180719 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 2, 3]
def baseStart_3180719 : Nat := 118140960795 + 3180719 * 2 ^ 59
def prefixEnd_3180719 : Nat := 4983230072969 + 3 ^ 40 * 3180719 * 2
def baseEnd_3180719 : Nat := 1088825115925497437323097

theorem tailTrace_3180719 : CollatzResearch.WordTrace tailWord_3180719 prefixEnd_3180719 1088825115925497437323097 := by
  unfold tailWord_3180719
  simp only [CollatzResearch.WordTrace]
  refine ⟨116010352563805761402073211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77340235042537174268048807 116010352563805761402073211)
  ·
    refine ⟨174015528845708642103109817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116010352563805761402073211 174015528845708642103109817)
    ·
      refine ⟨130511646634281481577332363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174015528845708642103109817 130511646634281481577332363)
      ·
        refine ⟨195767469951422222365998545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130511646634281481577332363 195767469951422222365998545)
        ·
          refine ⟨146825602463566666774498909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195767469951422222365998545 146825602463566666774498909)
          ·
            refine ⟨55059600923837500040437091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146825602463566666774498909 55059600923837500040437091)
            ·
              refine ⟨82589401385756250060655637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55059600923837500040437091 82589401385756250060655637)
              ·
                refine ⟨3871378189957324221593233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82589401385756250060655637 3871378189957324221593233)
                ·
                  refine ⟨2903533642467993166194925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871378189957324221593233 2903533642467993166194925)
                  ·
                    refine ⟨1088825115925497437323097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903533642467993166194925 1088825115925497437323097)
                    ·
                      rfl

theorem cell22_3180719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_3180719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180719 prefixEnd_3180719 := by exact prefixLift 3180719
  have htrace : WordTrace (prefixWord ++ tailWord_3180719) baseStart_3180719 baseEnd_3180719 := by
    simpa [prefixWord, tailWord_3180719, baseEnd_3180719] using wordTrace_append hprefix tailTrace_3180719
  have hstable : (prefixWord ++ tailWord_3180719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180719).length < 2 ^ (prefixWord ++ tailWord_3180719).sum := by decide
  have hdescent : baseEnd_3180719 < baseStart_3180719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180721 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 6]
def baseStart_3180721 : Nat := 118140960795 + 3180721 * 2 ^ 59
def prefixEnd_3180721 : Nat := 4983230072969 + 3 ^ 40 * 3180721 * 2
def baseEnd_3180721 : Nat := 362941933522123366257697

theorem tailTrace_3180721 : CollatzResearch.WordTrace tailWord_3180721 prefixEnd_3180721 362941933522123366257697 := by
  unfold tailWord_3180721
  simp only [CollatzResearch.WordTrace]
  refine ⟨116010425509798515743646017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77340283673199010495764011 116010425509798515743646017)
  ·
    refine ⟨87007819132348886807734513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116010425509798515743646017 87007819132348886807734513)
    ·
      refine ⟨65255864349261665105800885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87007819132348886807734513 65255864349261665105800885)
      ·
        refine ⟨6117737282743281103668833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65255864349261665105800885 6117737282743281103668833)
        ·
          refine ⟨4588302962057460827751625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117737282743281103668833 4588302962057460827751625)
          ·
            refine ⟨3441227221543095620813719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4588302962057460827751625 3441227221543095620813719)
            ·
              refine ⟨5161840832314643431220579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441227221543095620813719 5161840832314643431220579)
              ·
                refine ⟨7742761248471965146830869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161840832314643431220579 7742761248471965146830869)
                ·
                  refine ⟨362941933522123366257697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7742761248471965146830869 362941933522123366257697)
                  ·
                    rfl

theorem cell22_3180721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_3180721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180721 prefixEnd_3180721 := by exact prefixLift 3180721
  have htrace : WordTrace (prefixWord ++ tailWord_3180721) baseStart_3180721 baseEnd_3180721 := by
    simpa [prefixWord, tailWord_3180721, baseEnd_3180721] using wordTrace_append hprefix tailTrace_3180721
  have hstable : (prefixWord ++ tailWord_3180721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180721).length < 2 ^ (prefixWord ++ tailWord_3180721).sum := by decide
  have hdescent : baseEnd_3180721 < baseStart_3180721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180736 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 2, 3]
def baseStart_3180736 : Nat := 118140960795 + 3180736 * 2 ^ 59
def prefixEnd_3180736 : Nat := 4983230072969 + 3 ^ 40 * 3180736 * 2
def baseEnd_3180736 : Nat := 1088830935372915059648045

theorem tailTrace_3180736 : CollatzResearch.WordTrace tailWord_3180736 prefixEnd_3180736 1088830935372915059648045 := by
  unfold tailWord_3180736
  simp only [CollatzResearch.WordTrace]
  refine ⟨58005486302372086652721031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77340648403162782203628041 58005486302372086652721031)
  ·
    refine ⟨87008229453558129979081547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58005486302372086652721031 87008229453558129979081547)
    ·
      refine ⟨130512344180337194968622321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87008229453558129979081547 130512344180337194968622321)
      ·
        refine ⟨97884258135252896226466741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130512344180337194968622321 97884258135252896226466741)
        ·
          refine ⟨9176649200179959021231257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97884258135252896226466741 9176649200179959021231257)
          ·
            refine ⟨6882486900134969265923443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9176649200179959021231257 6882486900134969265923443)
            ·
              refine ⟨10323730350202453898885165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882486900134969265923443 10323730350202453898885165)
              ·
                refine ⟨3871398881325920212081937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323730350202453898885165 3871398881325920212081937)
                ·
                  refine ⟨2903549160994440159061453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871398881325920212081937 2903549160994440159061453)
                  ·
                    refine ⟨1088830935372915059648045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903549160994440159061453 1088830935372915059648045)
                    ·
                      rfl

theorem cell22_3180736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_3180736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180736 prefixEnd_3180736 := by exact prefixLift 3180736
  have htrace : WordTrace (prefixWord ++ tailWord_3180736) baseStart_3180736 baseEnd_3180736 := by
    simpa [prefixWord, tailWord_3180736, baseEnd_3180736] using wordTrace_append hprefix tailTrace_3180736
  have hstable : (prefixWord ++ tailWord_3180736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180736).length < 2 ^ (prefixWord ++ tailWord_3180736).sum := by decide
  have hdescent : baseEnd_3180736 < baseStart_3180736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180794 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_3180794 : Nat := 118140960795 + 3180794 * 2 ^ 59
def prefixEnd_3180794 : Nat := 4983230072969 + 3 ^ 40 * 3180794 * 2
def baseEnd_3180794 : Nat := 362950263319407413899289

theorem tailTrace_3180794 : CollatzResearch.WordTrace tailWord_3180794 prefixEnd_3180794 362950263319407413899289 := by
  unfold tailWord_3180794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29003272009633512302763359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77342058692356032807368957 29003272009633512302763359)
  ·
    refine ⟨43504908014450268454145039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29003272009633512302763359 43504908014450268454145039)
    ·
      refine ⟨65257362021675402681217559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43504908014450268454145039 65257362021675402681217559)
      ·
        refine ⟨97886043032513104021826339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65257362021675402681217559 97886043032513104021826339)
        ·
          refine ⟨146829064548769656032739509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97886043032513104021826339 146829064548769656032739509)
          ·
            refine ⟨13765224801447155253069329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146829064548769656032739509 13765224801447155253069329)
            ·
              refine ⟨10323918601085366439801997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13765224801447155253069329 10323918601085366439801997)
              ·
                refine ⟨3871469475407012414925749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323918601085366439801997 3871469475407012414925749)
                ·
                  refine ⟨362950263319407413899289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871469475407012414925749 362950263319407413899289)
                  ·
                    rfl

theorem cell22_3180794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_3180794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180794 prefixEnd_3180794 := by exact prefixLift 3180794
  have htrace : WordTrace (prefixWord ++ tailWord_3180794) baseStart_3180794 baseEnd_3180794 := by
    simpa [prefixWord, tailWord_3180794, baseEnd_3180794] using wordTrace_append hprefix tailTrace_3180794
  have hstable : (prefixWord ++ tailWord_3180794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180794).length < 2 ^ (prefixWord ++ tailWord_3180794).sum := by decide
  have hdescent : baseEnd_3180794 < baseStart_3180794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180845 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3180845 : Nat := 118140960795 + 3180845 * 2 ^ 59
def prefixEnd_3180845 : Nat := 4983230072969 + 3 ^ 40 * 3180845 * 2
def baseEnd_3180845 : Nat := 362956082766825036224237

theorem tailTrace_3180845 : CollatzResearch.WordTrace tailWord_3180845 prefixEnd_3180845 362956082766825036224237 := by
  unfold tailWord_3180845
  simp only [CollatzResearch.WordTrace]
  refine ⟨116014948161349284921159989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77343298774232856614106659 116014948161349284921159989)
  ·
    refine ⟨10876401390126495461358749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116014948161349284921159989 10876401390126495461358749)
    ·
      refine ⟨4078650521297435798009531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10876401390126495461358749 4078650521297435798009531)
      ·
        refine ⟨6117975781946153697014297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078650521297435798009531 6117975781946153697014297)
        ·
          refine ⟨4588481836459615272760723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117975781946153697014297 4588481836459615272760723)
          ·
            refine ⟨6882722754689422909141085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588481836459615272760723 6882722754689422909141085)
            ·
              refine ⟨2581021033008533590927907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6882722754689422909141085 2581021033008533590927907)
              ·
                refine ⟨3871531549512800386391861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581021033008533590927907 3871531549512800386391861)
                ·
                  refine ⟨362956082766825036224237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871531549512800386391861 362956082766825036224237)
                  ·
                    rfl

theorem cell22_3180845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3180845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180845 prefixEnd_3180845 := by exact prefixLift 3180845
  have htrace : WordTrace (prefixWord ++ tailWord_3180845) baseStart_3180845 baseEnd_3180845 := by
    simpa [prefixWord, tailWord_3180845, baseEnd_3180845] using wordTrace_append hprefix tailTrace_3180845
  have hstable : (prefixWord ++ tailWord_3180845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180845).length < 2 ^ (prefixWord ++ tailWord_3180845).sum := by decide
  have hdescent : baseEnd_3180845 < baseStart_3180845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180884 : List Nat := [2, 4, 1, 1, 2, 2, 10]
def baseStart_3180884 : Nat := 118140960795 + 3180884 * 2 ^ 59
def prefixEnd_3180884 : Nat := 4983230072969 + 3 ^ 40 * 3180884 * 2
def baseEnd_3180884 : Nat := 40328948103610815072133

theorem tailTrace_3180884 : CollatzResearch.WordTrace tailWord_3180884 prefixEnd_3180884 40328948103610815072133 := by
  unfold tailWord_3180884
  simp only [CollatzResearch.WordTrace]
  refine ⟨58008185304103997290914853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77344247072138663054553137 58008185304103997290914853)
  ·
    refine ⟨10876534744519499492046535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58008185304103997290914853 10876534744519499492046535)
    ·
      refine ⟨16314802116779249238069803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10876534744519499492046535 16314802116779249238069803)
      ·
        refine ⟨24472203175168873857104705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16314802116779249238069803 24472203175168873857104705)
        ·
          refine ⟨18354152381376655392828529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24472203175168873857104705 18354152381376655392828529)
          ·
            refine ⟨13765614286032491544621397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18354152381376655392828529 13765614286032491544621397)
            ·
              refine ⟨40328948103610815072133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13765614286032491544621397 40328948103610815072133)
              ·
                rfl

theorem cell22_3180884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 10].length) (baseStart_3180884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180884 prefixEnd_3180884 := by exact prefixLift 3180884
  have htrace : WordTrace (prefixWord ++ tailWord_3180884) baseStart_3180884 baseEnd_3180884 := by
    simpa [prefixWord, tailWord_3180884, baseEnd_3180884] using wordTrace_append hprefix tailTrace_3180884
  have hstable : (prefixWord ++ tailWord_3180884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180884).length < 2 ^ (prefixWord ++ tailWord_3180884).sum := by decide
  have hdescent : baseEnd_3180884 < baseStart_3180884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180933 : List Nat := [1, 3, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_3180933 : Nat := 118140960795 + 3180933 * 2 ^ 59
def prefixEnd_3180933 : Nat := 4983230072969 + 3 ^ 40 * 3180933 * 2
def baseEnd_3180933 : Nat := 1088898372498872212472441

theorem tailTrace_3180933 : CollatzResearch.WordTrace tailWord_3180933 prefixEnd_3180933 1088898372498872212472441 := by
  unfold tailWord_3180933
  simp only [CollatzResearch.WordTrace]
  refine ⟨116018157785030475950363453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77345438523353650633575635 116018157785030475950363453)
  ·
    refine ⟨43506809169386428481386295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116018157785030475950363453 43506809169386428481386295)
    ·
      refine ⟨65260213754079642722079443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43506809169386428481386295 65260213754079642722079443)
      ·
        refine ⟨97890320631119464083119165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65260213754079642722079443 97890320631119464083119165)
        ·
          refine ⟨36708870236669799031169687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97890320631119464083119165 36708870236669799031169687)
          ·
            refine ⟨55063305355004698546754531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36708870236669799031169687 55063305355004698546754531)
            ·
              refine ⟨82594958032507047820131797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55063305355004698546754531 82594958032507047820131797)
              ·
                refine ⟨1935819328886883933284339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 82594958032507047820131797 1935819328886883933284339)
                ·
                  refine ⟨2903728993330325899926509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935819328886883933284339 2903728993330325899926509)
                  ·
                    refine ⟨1088898372498872212472441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903728993330325899926509 1088898372498872212472441)
                    ·
                      rfl

theorem cell22_3180933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_3180933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3180933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3180933 prefixEnd_3180933 := by exact prefixLift 3180933
  have htrace : WordTrace (prefixWord ++ tailWord_3180933) baseStart_3180933 baseEnd_3180933 := by
    simpa [prefixWord, tailWord_3180933, baseEnd_3180933] using wordTrace_append hprefix tailTrace_3180933
  have hstable : (prefixWord ++ tailWord_3180933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180933).length < 2 ^ (prefixWord ++ tailWord_3180933).sum := by decide
  have hdescent : baseEnd_3180933 < baseStart_3180933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181021 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3181021 : Nat := 118140960795 + 3181021 * 2 ^ 59
def prefixEnd_3181021 : Nat := 4983230072969 + 3 ^ 40 * 3181021 * 2
def baseEnd_3181021 : Nat := 1088928496697269316272171

theorem tailTrace_3181021 : CollatzResearch.WordTrace tailWord_3181021 prefixEnd_3181021 1088928496697269316272171 := by
  unfold tailWord_3181021
  simp only [CollatzResearch.WordTrace]
  refine ⟨116021367408711666979566917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77347578272474444653044611 116021367408711666979566917)
  ·
    refine ⟨21754006389133437558668797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116021367408711666979566917 21754006389133437558668797)
    ·
      refine ⟨8157752395925039084500799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21754006389133437558668797 8157752395925039084500799)
      ·
        refine ⟨12236628593887558626751199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8157752395925039084500799 12236628593887558626751199)
        ·
          refine ⟨18354942890831337940126799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236628593887558626751199 18354942890831337940126799)
          ·
            refine ⟨27532414336247006910190199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18354942890831337940126799 27532414336247006910190199)
            ·
              refine ⟨41298621504370510365285299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27532414336247006910190199 41298621504370510365285299)
              ·
                refine ⟨61947932256555765547927949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41298621504370510365285299 61947932256555765547927949)
                ·
                  refine ⟨23230474596208412080472981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61947932256555765547927949 23230474596208412080472981)
                  ·
                    refine ⟨1088928496697269316272171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23230474596208412080472981 1088928496697269316272171)
                    ·
                      rfl

theorem cell22_3181021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3181021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181021 prefixEnd_3181021 := by exact prefixLift 3181021
  have htrace : WordTrace (prefixWord ++ tailWord_3181021) baseStart_3181021 baseEnd_3181021 := by
    simpa [prefixWord, tailWord_3181021, baseEnd_3181021] using wordTrace_append hprefix tailTrace_3181021
  have hstable : (prefixWord ++ tailWord_3181021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181021).length < 2 ^ (prefixWord ++ tailWord_3181021).sum := by decide
  have hdescent : baseEnd_3181021 < baseStart_3181021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181023 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 1, 5]
def baseStart_3181023 : Nat := 118140960795 + 3181023 * 2 ^ 59
def prefixEnd_3181023 : Nat := 4983230072969 + 3 ^ 40 * 3181023 * 2
def baseEnd_3181023 : Nat := 1088929181338141977722165

theorem tailTrace_3181023 : CollatzResearch.WordTrace tailWord_3181023 prefixEnd_3181023 1088929181338141977722165 := by
  unfold tailWord_3181023
  simp only [CollatzResearch.WordTrace]
  refine ⟨116021440354704421321139723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77347626903136280880759815 116021440354704421321139723)
  ·
    refine ⟨174032160532056631981709585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116021440354704421321139723 174032160532056631981709585)
    ·
      refine ⟨130524120399042473986282189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174032160532056631981709585 130524120399042473986282189)
      ·
        refine ⟨48946545149640927744855821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130524120399042473986282189 48946545149640927744855821)
        ·
          refine ⟨18354954431115347904320933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48946545149640927744855821 18354954431115347904320933)
          ·
            refine ⟨3441553955834127732060175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18354954431115347904320933 3441553955834127732060175)
            ·
              refine ⟨5162330933751191598090263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441553955834127732060175 5162330933751191598090263)
              ·
                refine ⟨7743496400626787397135395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162330933751191598090263 7743496400626787397135395)
                ·
                  refine ⟨11615244600940181095703093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7743496400626787397135395 11615244600940181095703093)
                  ·
                    refine ⟨1088929181338141977722165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11615244600940181095703093 1088929181338141977722165)
                    ·
                      rfl

theorem cell22_3181023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_3181023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181023 prefixEnd_3181023 := by exact prefixLift 3181023
  have htrace : WordTrace (prefixWord ++ tailWord_3181023) baseStart_3181023 baseEnd_3181023 := by
    simpa [prefixWord, tailWord_3181023, baseEnd_3181023] using wordTrace_append hprefix tailTrace_3181023
  have hstable : (prefixWord ++ tailWord_3181023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181023).length < 2 ^ (prefixWord ++ tailWord_3181023).sum := by decide
  have hdescent : baseEnd_3181023 < baseStart_3181023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181042 : List Nat := [3, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3181042 : Nat := 118140960795 + 3181042 * 2 ^ 59
def prefixEnd_3181042 : Nat := 4983230072969 + 3 ^ 40 * 3181042 * 2
def baseEnd_3181042 : Nat := 362978561808810753832369

theorem tailTrace_3181042 : CollatzResearch.WordTrace tailWord_3181042 prefixEnd_3181042 362978561808810753832369 := by
  unfold tailWord_3181042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29005533335408896891520345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77348088894423725044054253 29005533335408896891520345)
  ·
    refine ⟨21754150001556672668640259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29005533335408896891520345 21754150001556672668640259)
    ·
      refine ⟨32631225002335009002960389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21754150001556672668640259 32631225002335009002960389)
      ·
        refine ⟨6118354687937814188055073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32631225002335009002960389 6118354687937814188055073)
        ·
          refine ⟨4588766015953360641041305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6118354687937814188055073 4588766015953360641041305)
          ·
            refine ⟨3441574511965020480780979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4588766015953360641041305 3441574511965020480780979)
            ·
              refine ⟨5162361767947530721171469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441574511965020480780979 5162361767947530721171469)
              ·
                refine ⟨1935885662980324020439301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5162361767947530721171469 1935885662980324020439301)
                ·
                  refine ⟨362978561808810753832369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1935885662980324020439301 362978561808810753832369)
                  ·
                    rfl

theorem cell22_3181042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3181042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181042 prefixEnd_3181042 := by exact prefixLift 3181042
  have htrace : WordTrace (prefixWord ++ tailWord_3181042) baseStart_3181042 baseEnd_3181042 := by
    simpa [prefixWord, tailWord_3181042, baseEnd_3181042] using wordTrace_append hprefix tailTrace_3181042
  have hstable : (prefixWord ++ tailWord_3181042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181042).length < 2 ^ (prefixWord ++ tailWord_3181042).sum := by decide
  have hdescent : baseEnd_3181042 < baseStart_3181042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181066 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_3181066 : Nat := 118140960795 + 3181066 * 2 ^ 59
def prefixEnd_3181066 : Nat := 4983230072969 + 3 ^ 40 * 3181066 * 2
def baseEnd_3181066 : Nat := 1088943901116904198897033

theorem tailTrace_3181066 : CollatzResearch.WordTrace tailWord_3181066 prefixEnd_3181066 1088943901116904198897033 := by
  unfold tailWord_3181066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29005752173387159916238763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77348672462365759776636701 29005752173387159916238763)
  ·
    refine ⟨43508628260080739874358145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29005752173387159916238763 43508628260080739874358145)
    ·
      refine ⟨32631471195060554905768609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43508628260080739874358145 32631471195060554905768609)
      ·
        refine ⟨24473603396295416179326457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32631471195060554905768609 24473603396295416179326457)
        ·
          refine ⟨18355202547221562134494843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24473603396295416179326457 18355202547221562134494843)
          ·
            refine ⟨27532803820832343201742265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18355202547221562134494843 27532803820832343201742265)
            ·
              refine ⟨20649602865624257401306699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27532803820832343201742265 20649602865624257401306699)
              ·
                refine ⟨30974404298436386101960049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20649602865624257401306699 30974404298436386101960049)
                ·
                  refine ⟨23230803223827289576470037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30974404298436386101960049 23230803223827289576470037)
                  ·
                    refine ⟨1088943901116904198897033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23230803223827289576470037 1088943901116904198897033)
                    ·
                      rfl

theorem cell22_3181066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_3181066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181066 prefixEnd_3181066 := by exact prefixLift 3181066
  have htrace : WordTrace (prefixWord ++ tailWord_3181066) baseStart_3181066 baseEnd_3181066 := by
    simpa [prefixWord, tailWord_3181066, baseEnd_3181066] using wordTrace_append hprefix tailTrace_3181066
  have hstable : (prefixWord ++ tailWord_3181066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181066).length < 2 ^ (prefixWord ++ tailWord_3181066).sum := by decide
  have hdescent : baseEnd_3181066 < baseStart_3181066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181081 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 5]
def baseStart_3181081 : Nat := 118140960795 + 3181081 * 2 ^ 59
def prefixEnd_3181081 : Nat := 4983230072969 + 3 ^ 40 * 3181081 * 2
def baseEnd_3181081 : Nat := 362983011974483053257329

theorem tailTrace_3181081 : CollatzResearch.WordTrace tailWord_3181081 prefixEnd_3181081 362983011974483053257329 := by
  unfold tailWord_3181081
  simp only [CollatzResearch.WordTrace]
  refine ⟨116023555788494297226751097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77349037192329531484500731 116023555788494297226751097)
  ·
    refine ⟨87017666841370722920063323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116023555788494297226751097 87017666841370722920063323)
    ·
      refine ⟨130526500262056084380094985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87017666841370722920063323 130526500262056084380094985)
      ·
        refine ⟨97894875196542063285071239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130526500262056084380094985 97894875196542063285071239)
        ·
          refine ⟨146842312794813094927606859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97894875196542063285071239 146842312794813094927606859)
          ·
            refine ⟨220263469192219642391410289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146842312794813094927606859 220263469192219642391410289)
            ·
              refine ⟨165197601894164731793557717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220263469192219642391410289 165197601894164731793557717)
              ·
                refine ⟨3871818794394485901411509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165197601894164731793557717 3871818794394485901411509)
                ·
                  refine ⟨362983011974483053257329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871818794394485901411509 362983011974483053257329)
                  ·
                    rfl

theorem cell22_3181081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_3181081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181081 prefixEnd_3181081 := by exact prefixLift 3181081
  have htrace : WordTrace (prefixWord ++ tailWord_3181081) baseStart_3181081 baseEnd_3181081 := by
    simpa [prefixWord, tailWord_3181081, baseEnd_3181081] using wordTrace_append hprefix tailTrace_3181081
  have hstable : (prefixWord ++ tailWord_3181081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181081).length < 2 ^ (prefixWord ++ tailWord_3181081).sum := by decide
  have hdescent : baseEnd_3181081 < baseStart_3181081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181175 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 2, 3]
def baseStart_3181175 : Nat := 118140960795 + 3181175 * 2 ^ 59
def prefixEnd_3181175 : Nat := 4983230072969 + 3 ^ 40 * 3181175 * 2
def baseEnd_3181175 : Nat := 1088981214044464247921699

theorem tailTrace_3181175 : CollatzResearch.WordTrace tailWord_3181175 prefixEnd_3181175 1088981214044464247921699 := by
  unfold tailWord_3181175
  simp only [CollatzResearch.WordTrace]
  refine ⟨116026984250153751280672979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77351322833435834187115319 116026984250153751280672979)
  ·
    refine ⟨174040476375230626921009469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116026984250153751280672979 174040476375230626921009469)
    ·
      refine ⟨65265178640711485095378551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174040476375230626921009469 65265178640711485095378551)
      ·
        refine ⟨97897767961067227643067827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65265178640711485095378551 97897767961067227643067827)
        ·
          refine ⟨146846651941600841464601741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97897767961067227643067827 146846651941600841464601741)
          ·
            refine ⟨55067494478100315549225653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146846651941600841464601741 55067494478100315549225653)
            ·
              refine ⟨5162577607321904582739905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55067494478100315549225653 5162577607321904582739905)
              ·
                refine ⟨3871933205491428437054929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162577607321904582739905 3871933205491428437054929)
                ·
                  refine ⟨2903949904118571327791197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871933205491428437054929 2903949904118571327791197)
                  ·
                    refine ⟨1088981214044464247921699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903949904118571327791197 1088981214044464247921699)
                    ·
                      rfl

theorem cell22_3181175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_3181175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181175 prefixEnd_3181175 := by exact prefixLift 3181175
  have htrace : WordTrace (prefixWord ++ tailWord_3181175) baseStart_3181175 baseEnd_3181175 := by
    simpa [prefixWord, tailWord_3181175, baseEnd_3181175] using wordTrace_append hprefix tailTrace_3181175
  have hstable : (prefixWord ++ tailWord_3181175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181175).length < 2 ^ (prefixWord ++ tailWord_3181175).sum := by decide
  have hdescent : baseEnd_3181175 < baseStart_3181175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181201 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3181201 : Nat := 118140960795 + 3181201 * 2 ^ 59
def prefixEnd_3181201 : Nat := 4983230072969 + 3 ^ 40 * 3181201 * 2
def baseEnd_3181201 : Nat := 1088990114375808846771619

theorem tailTrace_3181201 : CollatzResearch.WordTrace tailWord_3181201 prefixEnd_3181201 1088990114375808846771619 := by
  unfold tailWord_3181201
  simp only [CollatzResearch.WordTrace]
  refine ⟨116027932548059557721119457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77351955032039705147412971 116027932548059557721119457)
  ·
    refine ⟨87020949411044668290839593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116027932548059557721119457 87020949411044668290839593)
    ·
      refine ⟨65265712058283501218129695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87020949411044668290839593 65265712058283501218129695)
      ·
        refine ⟨97898568087425251827194543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65265712058283501218129695 97898568087425251827194543)
        ·
          refine ⟨146847852131137877740791815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97898568087425251827194543 146847852131137877740791815)
          ·
            refine ⟨220271778196706816611187723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146847852131137877740791815 220271778196706816611187723)
            ·
              refine ⟨330407667295060224916781585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220271778196706816611187723 330407667295060224916781585)
              ·
                refine ⟨247805750471295168687586189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330407667295060224916781585 247805750471295168687586189)
                ·
                  refine ⟨92927156426735688257844821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247805750471295168687586189 92927156426735688257844821)
                  ·
                    refine ⟨1088990114375808846771619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92927156426735688257844821 1088990114375808846771619)
                    ·
                      rfl

theorem cell22_3181201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3181201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181201 prefixEnd_3181201 := by exact prefixLift 3181201
  have htrace : WordTrace (prefixWord ++ tailWord_3181201) baseStart_3181201 baseEnd_3181201 := by
    simpa [prefixWord, tailWord_3181201, baseEnd_3181201] using wordTrace_append hprefix tailTrace_3181201
  have hstable : (prefixWord ++ tailWord_3181201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181201).length < 2 ^ (prefixWord ++ tailWord_3181201).sum := by decide
  have hdescent : baseEnd_3181201 < baseStart_3181201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181237 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3181237 : Nat := 118140960795 + 3181237 * 2 ^ 59
def prefixEnd_3181237 : Nat := 4983230072969 + 3 ^ 40 * 3181237 * 2
def baseEnd_3181237 : Nat := 1089002437911516752871509

theorem tailTrace_3181237 : CollatzResearch.WordTrace tailWord_3181237 prefixEnd_3181237 1089002437911516752871509 := by
  unfold tailWord_3181237
  simp only [CollatzResearch.WordTrace]
  refine ⟨116029245575929135869429965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77352830383952757246286643 116029245575929135869429965)
  ·
    refine ⟨43510967090973425951036237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116029245575929135869429965 43510967090973425951036237)
    ·
      refine ⟨16316612659115034731638589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43510967090973425951036237 16316612659115034731638589)
      ·
        refine ⟨6118729747168138024364471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16316612659115034731638589 6118729747168138024364471)
        ·
          refine ⟨9178094620752207036546707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6118729747168138024364471 9178094620752207036546707)
          ·
            refine ⟨13767141931128310554820061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178094620752207036546707 13767141931128310554820061)
            ·
              refine ⟨5162678224173116458057523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13767141931128310554820061 5162678224173116458057523)
              ·
                refine ⟨7744017336259674687086285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162678224173116458057523 7744017336259674687086285)
                ·
                  refine ⟨2904006501097378007657357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7744017336259674687086285 2904006501097378007657357)
                  ·
                    refine ⟨1089002437911516752871509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904006501097378007657357 1089002437911516752871509)
                    ·
                      rfl

theorem cell22_3181237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3181237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181237 prefixEnd_3181237 := by exact prefixLift 3181237
  have htrace : WordTrace (prefixWord ++ tailWord_3181237) baseStart_3181237 baseEnd_3181237 := by
    simpa [prefixWord, tailWord_3181237, baseEnd_3181237] using wordTrace_append hprefix tailTrace_3181237
  have hstable : (prefixWord ++ tailWord_3181237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181237).length < 2 ^ (prefixWord ++ tailWord_3181237).sum := by decide
  have hdescent : baseEnd_3181237 < baseStart_3181237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181288 : List Nat := [2, 1, 4, 1, 5, 1, 2, 2, 1, 3]
def baseStart_3181288 : Nat := 118140960795 + 3181288 * 2 ^ 59
def prefixEnd_3181288 : Nat := 4983230072969 + 3 ^ 40 * 3181288 * 2
def baseEnd_3181288 : Nat := 1089019896253769619846353

theorem tailTrace_3181288 : CollatzResearch.WordTrace tailWord_3181288 prefixEnd_3181288 1089019896253769619846353 := by
  unfold tailWord_3181288
  simp only [CollatzResearch.WordTrace]
  refine ⟨58015552849372185789768259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77354070465829581053024345 58015552849372185789768259)
  ·
    refine ⟨87023329274058278684652389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58015552849372185789768259 87023329274058278684652389)
    ·
      refine ⟨16316874238885927253372323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87023329274058278684652389 16316874238885927253372323)
      ·
        refine ⟨24475311358328890880058485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16316874238885927253372323 24475311358328890880058485)
        ·
          refine ⟨2294560439843333520005483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24475311358328890880058485 2294560439843333520005483)
          ·
            refine ⟨3441840659765000280008225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294560439843333520005483 3441840659765000280008225)
            ·
              refine ⟨2581380494823750210006169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441840659765000280008225 2581380494823750210006169)
              ·
                refine ⟨1936035371117812657504627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581380494823750210006169 1936035371117812657504627)
                ·
                  refine ⟨2904053056676718986256941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936035371117812657504627 2904053056676718986256941)
                  ·
                    refine ⟨1089019896253769619846353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904053056676718986256941 1089019896253769619846353)
                    ·
                      rfl

theorem cell22_3181288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_3181288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181288 prefixEnd_3181288 := by exact prefixLift 3181288
  have htrace : WordTrace (prefixWord ++ tailWord_3181288) baseStart_3181288 baseEnd_3181288 := by
    simpa [prefixWord, tailWord_3181288, baseEnd_3181288] using wordTrace_append hprefix tailTrace_3181288
  have hstable : (prefixWord ++ tailWord_3181288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181288).length < 2 ^ (prefixWord ++ tailWord_3181288).sum := by decide
  have hdescent : baseEnd_3181288 < baseStart_3181288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181344 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 2, 3]
def baseStart_3181344 : Nat := 118140960795 + 3181344 * 2 ^ 59
def prefixEnd_3181344 : Nat := 4983230072969 + 3 ^ 40 * 3181344 * 2
def baseEnd_3181344 : Nat := 1089039066198204140446181

theorem tailTrace_3181344 : CollatzResearch.WordTrace tailWord_3181344 prefixEnd_3181344 1089039066198204140446181 := by
  unfold tailWord_3181344
  simp only [CollatzResearch.WordTrace]
  refine ⟨58016574093270746571787543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77355432124360995429050057 58016574093270746571787543)
  ·
    refine ⟨87024861139906119857681315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58016574093270746571787543 87024861139906119857681315)
    ·
      refine ⟨130537291709859179786521973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87024861139906119857681315 130537291709859179786521973)
      ·
        refine ⟨12237871097799298104986435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130537291709859179786521973 12237871097799298104986435)
        ·
          refine ⟨18356806646698947157479653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12237871097799298104986435 18356806646698947157479653)
          ·
            refine ⟨3441901246256052592027435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18356806646698947157479653 3441901246256052592027435)
            ·
              refine ⟨5162851869384078888041153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441901246256052592027435 5162851869384078888041153)
              ·
                refine ⟨3872138902038059166030865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162851869384078888041153 3872138902038059166030865)
                ·
                  refine ⟨2904104176528544374523149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872138902038059166030865 2904104176528544374523149)
                  ·
                    refine ⟨1089039066198204140446181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904104176528544374523149 1089039066198204140446181)
                    ·
                      rfl

theorem cell22_3181344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_3181344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181344 prefixEnd_3181344 := by exact prefixLift 3181344
  have htrace : WordTrace (prefixWord ++ tailWord_3181344) baseStart_3181344 baseEnd_3181344 := by
    simpa [prefixWord, tailWord_3181344, baseEnd_3181344] using wordTrace_append hprefix tailTrace_3181344
  have hstable : (prefixWord ++ tailWord_3181344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181344).length < 2 ^ (prefixWord ++ tailWord_3181344).sum := by decide
  have hdescent : baseEnd_3181344 < baseStart_3181344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181355 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 3, 3]
def baseStart_3181355 : Nat := 118140960795 + 3181355 * 2 ^ 59
def prefixEnd_3181355 : Nat := 4983230072969 + 3 ^ 40 * 3181355 * 2
def baseEnd_3181355 : Nat := 1089042831723003778421147

theorem tailTrace_3181355 : CollatzResearch.WordTrace tailWord_3181355 prefixEnd_3181355 1089042831723003778421147 := by
  unfold tailWord_3181355
  simp only [CollatzResearch.WordTrace]
  refine ⟨116033549389501642022225519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77355699593001094681483679 116033549389501642022225519)
  ·
    refine ⟨174050324084252463033338279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116033549389501642022225519 174050324084252463033338279)
    ·
      refine ⟨261075486126378694550007419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174050324084252463033338279 261075486126378694550007419)
      ·
        refine ⟨391613229189568041825011129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261075486126378694550007419 391613229189568041825011129)
        ·
          refine ⟨293709921892176031368758347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391613229189568041825011129 293709921892176031368758347)
          ·
            refine ⟨440564882838264047053137521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293709921892176031368758347 440564882838264047053137521)
            ·
              refine ⟨330423662128698035289853141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440564882838264047053137521 330423662128698035289853141)
              ·
                refine ⟨7744304581141360202105933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 330423662128698035289853141 7744304581141360202105933)
                ·
                  refine ⟨2904114217928010075789725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7744304581141360202105933 2904114217928010075789725)
                  ·
                    refine ⟨1089042831723003778421147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904114217928010075789725 1089042831723003778421147)
                    ·
                      rfl

theorem cell22_3181355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 3].length) (baseStart_3181355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181355 prefixEnd_3181355 := by exact prefixLift 3181355
  have htrace : WordTrace (prefixWord ++ tailWord_3181355) baseStart_3181355 baseEnd_3181355 := by
    simpa [prefixWord, tailWord_3181355, baseEnd_3181355] using wordTrace_append hprefix tailTrace_3181355
  have hstable : (prefixWord ++ tailWord_3181355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181355).length < 2 ^ (prefixWord ++ tailWord_3181355).sum := by decide
  have hdescent : baseEnd_3181355 < baseStart_3181355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181374 : List Nat := [4, 2, 1, 2, 3, 2, 2, 6]
def baseStart_3181374 : Nat := 118140960795 + 3181374 * 2 ^ 59
def prefixEnd_3181374 : Nat := 4983230072969 + 3 ^ 40 * 3181374 * 2
def baseEnd_3181374 : Nat := 121005481756810451355121

theorem tailTrace_3181374 : CollatzResearch.WordTrace tailWord_3181374 prefixEnd_3181374 121005481756810451355121 := by
  unfold tailWord_3181374
  simp only [CollatzResearch.WordTrace]
  refine ⟨14504280297054101033395897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77356161584288538844778117 14504280297054101033395897)
  ·
    refine ⟨10878210222790575775046923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14504280297054101033395897 10878210222790575775046923)
    ·
      refine ⟨16317315334185863662570385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10878210222790575775046923 16317315334185863662570385)
      ·
        refine ⟨12237986500639397746927789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16317315334185863662570385 12237986500639397746927789)
        ·
          refine ⟨4589244937739774155097921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12237986500639397746927789 4589244937739774155097921)
          ·
            refine ⟨3441933703304830616323441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4589244937739774155097921 3441933703304830616323441)
            ·
              refine ⟨2581450277478622962242581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441933703304830616323441 2581450277478622962242581)
              ·
                refine ⟨121005481756810451355121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2581450277478622962242581 121005481756810451355121)
                ·
                  rfl

theorem cell22_3181374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_3181374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181374 prefixEnd_3181374 := by exact prefixLift 3181374
  have htrace : WordTrace (prefixWord ++ tailWord_3181374) baseStart_3181374 baseEnd_3181374 := by
    simpa [prefixWord, tailWord_3181374, baseEnd_3181374] using wordTrace_append hprefix tailTrace_3181374
  have hstable : (prefixWord ++ tailWord_3181374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181374).length < 2 ^ (prefixWord ++ tailWord_3181374).sum := by decide
  have hdescent : baseEnd_3181374 < baseStart_3181374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181445 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_3181445 : Nat := 118140960795 + 3181445 * 2 ^ 59
def prefixEnd_3181445 : Nat := 4983230072969 + 3 ^ 40 * 3181445 * 2
def baseEnd_3181445 : Nat := 1089073640562273543670871

theorem tailTrace_3181445 : CollatzResearch.WordTrace tailWord_3181445 prefixEnd_3181445 1089073640562273543670871 := by
  unfold tailWord_3181445
  simp only [CollatzResearch.WordTrace]
  refine ⟨116036831959175587393001789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77357887972783724928667859 116036831959175587393001789)
  ·
    refine ⟨43513811984690845272375671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116036831959175587393001789 43513811984690845272375671)
    ·
      refine ⟨65270717977036267908563507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43513811984690845272375671 65270717977036267908563507)
      ·
        refine ⟨97906076965554401862845261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65270717977036267908563507 97906076965554401862845261)
        ·
          refine ⟨36714778862082900698566973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97906076965554401862845261 36714778862082900698566973)
          ·
            refine ⟨13768042073281087761962615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36714778862082900698566973 13768042073281087761962615)
            ·
              refine ⟨20652063109921631642943923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13768042073281087761962615 20652063109921631642943923)
              ·
                refine ⟨30978094664882447464415885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20652063109921631642943923 30978094664882447464415885)
                ·
                  refine ⟨11616785499330917799155957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30978094664882447464415885 11616785499330917799155957)
                  ·
                    refine ⟨1089073640562273543670871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11616785499330917799155957 1089073640562273543670871)
                    ·
                      rfl

theorem cell22_3181445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_3181445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181445 prefixEnd_3181445 := by exact prefixLift 3181445
  have htrace : WordTrace (prefixWord ++ tailWord_3181445) baseStart_3181445 baseEnd_3181445 := by
    simpa [prefixWord, tailWord_3181445, baseEnd_3181445] using wordTrace_append hprefix tailTrace_3181445
  have hstable : (prefixWord ++ tailWord_3181445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181445).length < 2 ^ (prefixWord ++ tailWord_3181445).sum := by decide
  have hdescent : baseEnd_3181445 < baseStart_3181445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181449 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 1, 4]
def baseStart_3181449 : Nat := 118140960795 + 3181449 * 2 ^ 59
def prefixEnd_3181449 : Nat := 4983230072969 + 3 ^ 40 * 3181449 * 2
def baseEnd_3181449 : Nat := 1089075009844018866570859

theorem tailTrace_3181449 : CollatzResearch.WordTrace tailWord_3181449 prefixEnd_3181449 1089075009844018866570859 := by
  unfold tailWord_3181449
  simp only [CollatzResearch.WordTrace]
  refine ⟨116036977851161096076147401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77357985234107397384098267 116036977851161096076147401)
  ·
    refine ⟨87027733388370822057110551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116036977851161096076147401 87027733388370822057110551)
    ·
      refine ⟨130541600082556233085665827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87027733388370822057110551 130541600082556233085665827)
      ·
        refine ⟨195812400123834349628498741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130541600082556233085665827 195812400123834349628498741)
        ·
          refine ⟨18357412511609470277671757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195812400123834349628498741 18357412511609470277671757)
          ·
            refine ⟨6884029691853551354126909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18357412511609470277671757 6884029691853551354126909)
            ·
              refine ⟨2581511134445081757797591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6884029691853551354126909 2581511134445081757797591)
              ·
                refine ⟨3872266701667622636696387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581511134445081757797591 3872266701667622636696387)
                ·
                  refine ⟨5808400052501433955044581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872266701667622636696387 5808400052501433955044581)
                  ·
                    refine ⟨1089075009844018866570859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5808400052501433955044581 1089075009844018866570859)
                    ·
                      rfl

theorem cell22_3181449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_3181449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181449 prefixEnd_3181449 := by exact prefixLift 3181449
  have htrace : WordTrace (prefixWord ++ tailWord_3181449) baseStart_3181449 baseEnd_3181449 := by
    simpa [prefixWord, tailWord_3181449, baseEnd_3181449] using wordTrace_append hprefix tailTrace_3181449
  have hstable : (prefixWord ++ tailWord_3181449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181449).length < 2 ^ (prefixWord ++ tailWord_3181449).sum := by decide
  have hdescent : baseEnd_3181449 < baseStart_3181449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181475 : List Nat := [1, 1, 1, 4, 1, 2, 5, 7]
def baseStart_3181475 : Nat := 118140960795 + 3181475 * 2 ^ 59
def prefixEnd_3181475 : Nat := 4983230072969 + 3 ^ 40 * 3181475 * 2
def baseEnd_3181475 : Nat := 121009323352818162824531

theorem tailTrace_3181475 : CollatzResearch.WordTrace tailWord_3181475 prefixEnd_3181475 121009323352818162824531 := by
  unfold tailWord_3181475
  simp only [CollatzResearch.WordTrace]
  refine ⟨116037926149066902516593879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77358617432711268344395919 116037926149066902516593879)
  ·
    refine ⟨174056889223600353774890819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116037926149066902516593879 174056889223600353774890819)
    ·
      refine ⟨261085333835400530662336229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174056889223600353774890819 261085333835400530662336229)
      ·
        refine ⟨48953500094137599499188043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261085333835400530662336229 48953500094137599499188043)
        ·
          refine ⟨73430250141206399248782065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48953500094137599499188043 73430250141206399248782065)
          ·
            refine ⟨55072687605904799436586549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73430250141206399248782065 55072687605904799436586549)
            ·
              refine ⟨5163064463053574947179989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55072687605904799436586549 5163064463053574947179989)
              ·
                refine ⟨121009323352818162824531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5163064463053574947179989 121009323352818162824531)
                ·
                  rfl

theorem cell22_3181475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 7].length) (baseStart_3181475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181475 prefixEnd_3181475 := by exact prefixLift 3181475
  have htrace : WordTrace (prefixWord ++ tailWord_3181475) baseStart_3181475 baseEnd_3181475 := by
    simpa [prefixWord, tailWord_3181475, baseEnd_3181475] using wordTrace_append hprefix tailTrace_3181475
  have hstable : (prefixWord ++ tailWord_3181475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181475).length < 2 ^ (prefixWord ++ tailWord_3181475).sum := by decide
  have hdescent : baseEnd_3181475 < baseStart_3181475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181479 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3181479 : Nat := 118140960795 + 3181479 * 2 ^ 59
def prefixEnd_3181479 : Nat := 4983230072969 + 3 ^ 40 * 3181479 * 2
def baseEnd_3181479 : Nat := 1089085279457108788320767

theorem tailTrace_3181479 : CollatzResearch.WordTrace tailWord_3181479 prefixEnd_3181479 1089085279457108788320767 := by
  unfold tailWord_3181479
  simp only [CollatzResearch.WordTrace]
  refine ⟨116038072041052411199739491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77358714694034940799826327 116038072041052411199739491)
  ·
    refine ⟨174057108061578616799609237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116038072041052411199739491 174057108061578616799609237)
    ·
      refine ⟨8158926940386497662481683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174057108061578616799609237 8158926940386497662481683)
      ·
        refine ⟨12238390410579746493722525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8158926940386497662481683 12238390410579746493722525)
        ·
          refine ⟨4589396403967404935145947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12238390410579746493722525 4589396403967404935145947)
          ·
            refine ⟨6884094605951107402718921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589396403967404935145947 6884094605951107402718921)
            ·
              refine ⟨5163070954463330552039191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6884094605951107402718921 5163070954463330552039191)
              ·
                refine ⟨7744606431694995828058787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163070954463330552039191 7744606431694995828058787)
                ·
                  refine ⟨11616909647542493742088181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744606431694995828058787 11616909647542493742088181)
                  ·
                    refine ⟨1089085279457108788320767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11616909647542493742088181 1089085279457108788320767)
                    ·
                      rfl

theorem cell22_3181479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3181479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181479 prefixEnd_3181479 := by exact prefixLift 3181479
  have htrace : WordTrace (prefixWord ++ tailWord_3181479) baseStart_3181479 baseEnd_3181479 := by
    simpa [prefixWord, tailWord_3181479, baseEnd_3181479] using wordTrace_append hprefix tailTrace_3181479
  have hstable : (prefixWord ++ tailWord_3181479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181479).length < 2 ^ (prefixWord ++ tailWord_3181479).sum := by decide
  have hdescent : baseEnd_3181479 < baseStart_3181479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181524 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3181524 : Nat := 118140960795 + 3181524 * 2 ^ 59
def prefixEnd_3181524 : Nat := 4983230072969 + 3 ^ 40 * 3181524 * 2
def baseEnd_3181524 : Nat := 1089100683876743670945629

theorem tailTrace_3181524 : CollatzResearch.WordTrace tailWord_3181524 prefixEnd_3181524 1089100683876743670945629 := by
  unfold tailWord_3181524
  simp only [CollatzResearch.WordTrace]
  refine ⟨58019856662944691942563813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77359808883926255923418417 58019856662944691942563813)
  ·
    refine ⟨10878723124302129739230715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58019856662944691942563813 10878723124302129739230715)
    ·
      refine ⟨16318084686453194608846073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10878723124302129739230715 16318084686453194608846073)
      ·
        refine ⟨12238563514839895956634555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16318084686453194608846073 12238563514839895956634555)
        ·
          refine ⟨18357845272259843934951833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12238563514839895956634555 18357845272259843934951833)
          ·
            refine ⟨13768383954194882951213875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18357845272259843934951833 13768383954194882951213875)
            ·
              refine ⟨20652575931292324426820813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13768383954194882951213875 20652575931292324426820813)
              ·
                refine ⟨7744715974234621660057805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20652575931292324426820813 7744715974234621660057805)
                ·
                  refine ⟨2904268490337983122521677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7744715974234621660057805 2904268490337983122521677)
                  ·
                    refine ⟨1089100683876743670945629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904268490337983122521677 1089100683876743670945629)
                    ·
                      rfl

theorem cell22_3181524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3181524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181524 prefixEnd_3181524 := by exact prefixLift 3181524
  have htrace : WordTrace (prefixWord ++ tailWord_3181524) baseStart_3181524 baseEnd_3181524 := by
    simpa [prefixWord, tailWord_3181524, baseEnd_3181524] using wordTrace_append hprefix tailTrace_3181524
  have hstable : (prefixWord ++ tailWord_3181524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181524).length < 2 ^ (prefixWord ++ tailWord_3181524).sum := by decide
  have hdescent : baseEnd_3181524 < baseStart_3181524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181558 : List Nat := [5, 1, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_3181558 : Nat := 118140960795 + 3181558 * 2 ^ 59
def prefixEnd_3181558 : Nat := 4983230072969 + 3 ^ 40 * 3181558 * 2
def baseEnd_3181558 : Nat := 1089112322771578915595525

theorem tailTrace_3181558 : CollatzResearch.WordTrace tailWord_3181558 prefixEnd_3181558 1089112322771578915595525 := by
  unfold tailWord_3181558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7252559587985387980741583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77360635605177471794576885 7252559587985387980741583)
  ·
    refine ⟨10878839381978081971112375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7252559587985387980741583 10878839381978081971112375)
    ·
      refine ⟨16318259072967122956668563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10878839381978081971112375 16318259072967122956668563)
      ·
        refine ⟨24477388609450684435002845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16318259072967122956668563 24477388609450684435002845)
        ·
          refine ⟨9179020728544006663126067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24477388609450684435002845 9179020728544006663126067)
          ·
            refine ⟨13768531092816009994689101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9179020728544006663126067 13768531092816009994689101)
            ·
              refine ⟨5163199159806003748008413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13768531092816009994689101 5163199159806003748008413)
              ·
                refine ⟨1936199684927251405503155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5163199159806003748008413 1936199684927251405503155)
                ·
                  refine ⟨2904299527390877108254733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936199684927251405503155 2904299527390877108254733)
                  ·
                    refine ⟨1089112322771578915595525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904299527390877108254733 1089112322771578915595525)
                    ·
                      rfl

theorem cell22_3181558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_3181558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181558 prefixEnd_3181558 := by exact prefixLift 3181558
  have htrace : WordTrace (prefixWord ++ tailWord_3181558) baseStart_3181558 baseEnd_3181558 := by
    simpa [prefixWord, tailWord_3181558, baseEnd_3181558] using wordTrace_append hprefix tailTrace_3181558
  have hstable : (prefixWord ++ tailWord_3181558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181558).length < 2 ^ (prefixWord ++ tailWord_3181558).sum := by decide
  have hdescent : baseEnd_3181558 < baseStart_3181558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181601 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 1, 4]
def baseStart_3181601 : Nat := 118140960795 + 3181601 * 2 ^ 59
def prefixEnd_3181601 : Nat := 4983230072969 + 3 ^ 40 * 3181601 * 2
def baseEnd_3181601 : Nat := 1089127042550341136770393

theorem tailTrace_3181601 : CollatzResearch.WordTrace tailWord_3181601 prefixEnd_3181601 1089127042550341136770393 := by
  unfold tailWord_3181601
  simp only [CollatzResearch.WordTrace]
  refine ⟨116042521746610426035680657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77361681164406950690453771 116042521746610426035680657)
  ·
    refine ⟨87031891309957819526760493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116042521746610426035680657 87031891309957819526760493)
    ·
      refine ⟨32636959241234182322535185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87031891309957819526760493 32636959241234182322535185)
      ·
        refine ⟨24477719430925636741901389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32636959241234182322535185 24477719430925636741901389)
        ·
          refine ⟨9179144786597113778213021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24477719430925636741901389 9179144786597113778213021)
          ·
            refine ⟨3442179294973917666829883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9179144786597113778213021 3442179294973917666829883)
            ·
              refine ⟨5163268942460876500244825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442179294973917666829883 5163268942460876500244825)
              ·
                refine ⟨3872451706845657375183619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5163268942460876500244825 3872451706845657375183619)
                ·
                  refine ⟨5808677560268486062775429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872451706845657375183619 5808677560268486062775429)
                  ·
                    refine ⟨1089127042550341136770393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5808677560268486062775429 1089127042550341136770393)
                    ·
                      rfl

theorem cell22_3181601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_3181601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181601 prefixEnd_3181601 := by exact prefixLift 3181601
  have htrace : WordTrace (prefixWord ++ tailWord_3181601) baseStart_3181601 baseEnd_3181601 := by
    simpa [prefixWord, tailWord_3181601, baseEnd_3181601] using wordTrace_append hprefix tailTrace_3181601
  have hstable : (prefixWord ++ tailWord_3181601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181601).length < 2 ^ (prefixWord ++ tailWord_3181601).sum := by decide
  have hdescent : baseEnd_3181601 < baseStart_3181601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181614 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3181614 : Nat := 118140960795 + 3181614 * 2 ^ 59
def prefixEnd_3181614 : Nat := 4983230072969 + 3 ^ 40 * 3181614 * 2
def baseEnd_3181614 : Nat := 1089131492716013436195353

theorem tailTrace_3181614 : CollatzResearch.WordTrace tailWord_3181614 prefixEnd_3181614 1089131492716013436195353 := by
  unfold tailWord_3181614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14505374486945416156987987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77361997263708886170602597 14505374486945416156987987)
  ·
    refine ⟨21758061730418124235481981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14505374486945416156987987 21758061730418124235481981)
    ·
      refine ⟨8159273148906796588305743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21758061730418124235481981 8159273148906796588305743)
      ·
        refine ⟨12238909723360194882458615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159273148906796588305743 12238909723360194882458615)
        ·
          refine ⟨18358364585040292323687923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12238909723360194882458615 18358364585040292323687923)
          ·
            refine ⟨27537546877560438485531885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18358364585040292323687923 27537546877560438485531885)
            ·
              refine ⟨10326580079085164432074457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27537546877560438485531885 10326580079085164432074457)
              ·
                refine ⟨7744935059313873324055843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10326580079085164432074457 7744935059313873324055843)
                ·
                  refine ⟨11617402588970809986083765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744935059313873324055843 11617402588970809986083765)
                  ·
                    refine ⟨1089131492716013436195353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11617402588970809986083765 1089131492716013436195353)
                    ·
                      rfl

theorem cell22_3181614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3181614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181614 prefixEnd_3181614 := by exact prefixLift 3181614
  have htrace : WordTrace (prefixWord ++ tailWord_3181614) baseStart_3181614 baseEnd_3181614 := by
    simpa [prefixWord, tailWord_3181614, baseEnd_3181614] using wordTrace_append hprefix tailTrace_3181614
  have hstable : (prefixWord ++ tailWord_3181614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181614).length < 2 ^ (prefixWord ++ tailWord_3181614).sum := by decide
  have hdescent : baseEnd_3181614 < baseStart_3181614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181629 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_3181629 : Nat := 118140960795 + 3181629 * 2 ^ 59
def prefixEnd_3181629 : Nat := 4983230072969 + 3 ^ 40 * 3181629 * 2
def baseEnd_3181629 : Nat := 1089136627522558397070307

theorem tailTrace_3181629 : CollatzResearch.WordTrace tailWord_3181629 prefixEnd_3181629 1089136627522558397070307 := by
  unfold tailWord_3181629
  simp only [CollatzResearch.WordTrace]
  refine ⟨116043542990508986817699941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77362361993672657878466627 116043542990508986817699941)
  ·
    refine ⟨21758164310720435028318739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116043542990508986817699941 21758164310720435028318739)
    ·
      refine ⟨32637246466080652542478109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21758164310720435028318739 32637246466080652542478109)
      ·
        refine ⟨12238967424780244703429291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32637246466080652542478109 12238967424780244703429291)
        ·
          refine ⟨18358451137170367055143937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12238967424780244703429291 18358451137170367055143937)
          ·
            refine ⟨13768838352877775291357953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18358451137170367055143937 13768838352877775291357953)
            ·
              refine ⟨10326628764658331468518465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13768838352877775291357953 10326628764658331468518465)
              ·
                refine ⟨7744971573493748601388849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10326628764658331468518465 7744971573493748601388849)
                ·
                  refine ⟨5808728680120311451041637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7744971573493748601388849 5808728680120311451041637)
                  ·
                    refine ⟨1089136627522558397070307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5808728680120311451041637 1089136627522558397070307)
                    ·
                      rfl

theorem cell22_3181629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_3181629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181629 prefixEnd_3181629 := by exact prefixLift 3181629
  have htrace : WordTrace (prefixWord ++ tailWord_3181629) baseStart_3181629 baseEnd_3181629 := by
    simpa [prefixWord, tailWord_3181629, baseEnd_3181629] using wordTrace_append hprefix tailTrace_3181629
  have hstable : (prefixWord ++ tailWord_3181629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181629).length < 2 ^ (prefixWord ++ tailWord_3181629).sum := by decide
  have hdescent : baseEnd_3181629 < baseStart_3181629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181687 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3181687 : Nat := 118140960795 + 3181687 * 2 ^ 59
def prefixEnd_3181687 : Nat := 4983230072969 + 3 ^ 40 * 3181687 * 2
def baseEnd_3181687 : Nat := 1089156482107865579120129

theorem tailTrace_3181687 : CollatzResearch.WordTrace tailWord_3181687 prefixEnd_3181687 1089156482107865579120129 := by
  unfold tailWord_3181687
  simp only [CollatzResearch.WordTrace]
  refine ⟨116045658424298862723311315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77363772282865908482207543 116045658424298862723311315)
  ·
    refine ⟨174068487636448294084966973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116045658424298862723311315 174068487636448294084966973)
    ·
      refine ⟨65275682863668110281862615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174068487636448294084966973 65275682863668110281862615)
      ·
        refine ⟨97913524295502165422793923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65275682863668110281862615 97913524295502165422793923)
        ·
          refine ⟨146870286443253248134190885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97913524295502165422793923 146870286443253248134190885)
          ·
            refine ⟨27538178708109984025160791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146870286443253248134190885 27538178708109984025160791)
            ·
              refine ⟨41307268062164976037741187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27538178708109984025160791 41307268062164976037741187)
              ·
                refine ⟨61960902093247464056611781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41307268062164976037741187 61960902093247464056611781)
                ·
                  refine ⟨11617669142483899510614709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61960902093247464056611781 11617669142483899510614709)
                  ·
                    refine ⟨1089156482107865579120129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11617669142483899510614709 1089156482107865579120129)
                    ·
                      rfl

theorem cell22_3181687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3181687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181687 prefixEnd_3181687 := by exact prefixLift 3181687
  have htrace : WordTrace (prefixWord ++ tailWord_3181687) baseStart_3181687 baseEnd_3181687 := by
    simpa [prefixWord, tailWord_3181687, baseEnd_3181687] using wordTrace_append hprefix tailTrace_3181687
  have hstable : (prefixWord ++ tailWord_3181687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181687).length < 2 ^ (prefixWord ++ tailWord_3181687).sum := by decide
  have hdescent : baseEnd_3181687 < baseStart_3181687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181689 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 7]
def baseStart_3181689 : Nat := 118140960795 + 3181689 * 2 ^ 59
def prefixEnd_3181689 : Nat := 4983230072969 + 3 ^ 40 * 3181689 * 2
def baseEnd_3181689 : Nat := 363052388916246080190041

theorem tailTrace_3181689 : CollatzResearch.WordTrace tailWord_3181689 prefixEnd_3181689 363052388916246080190041 := by
  unfold tailWord_3181689
  simp only [CollatzResearch.WordTrace]
  refine ⟨116045731370291617064884121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77363820913527744709922747 116045731370291617064884121)
  ·
    refine ⟨87034298527718712798663091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116045731370291617064884121 87034298527718712798663091)
    ·
      refine ⟨130551447791578069197994637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87034298527718712798663091 130551447791578069197994637)
      ·
        refine ⟨48956792921841775949247989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130551447791578069197994637 48956792921841775949247989)
        ·
          refine ⟨4589699336422666495241999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48956792921841775949247989 4589699336422666495241999)
          ·
            refine ⟨6884549004633999742862999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589699336422666495241999 6884549004633999742862999)
            ·
              refine ⟨10326823506950999614294499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884549004633999742862999 10326823506950999614294499)
              ·
                refine ⟨15490235260426499421441749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10326823506950999614294499 15490235260426499421441749)
                ·
                  refine ⟨363052388916246080190041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15490235260426499421441749 363052388916246080190041)
                  ·
                    rfl

theorem cell22_3181689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_3181689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181689 prefixEnd_3181689 := by exact prefixLift 3181689
  have htrace : WordTrace (prefixWord ++ tailWord_3181689) baseStart_3181689 baseEnd_3181689 := by
    simpa [prefixWord, tailWord_3181689, baseEnd_3181689] using wordTrace_append hprefix tailTrace_3181689
  have hstable : (prefixWord ++ tailWord_3181689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181689).length < 2 ^ (prefixWord ++ tailWord_3181689).sum := by decide
  have hdescent : baseEnd_3181689 < baseStart_3181689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181706 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_3181706 : Nat := 118140960795 + 3181706 * 2 ^ 59
def prefixEnd_3181706 : Nat := 4983230072969 + 3 ^ 40 * 3181706 * 2
def baseEnd_3181706 : Nat := 363054328732051954298357

theorem tailTrace_3181706 : CollatzResearch.WordTrace tailWord_3181706 prefixEnd_3181706 363054328732051954298357 := by
  unfold tailWord_3181706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29011587852807507242063243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77364234274153352645501981 29011587852807507242063243)
  ·
    refine ⟨43517381779211260863094865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29011587852807507242063243 43517381779211260863094865)
    ·
      refine ⟨32638036334408445647321149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43517381779211260863094865 32638036334408445647321149)
      ·
        refine ⟨12239263625403167117745431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32638036334408445647321149 12239263625403167117745431)
        ·
          refine ⟨18358895438104750676618147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12239263625403167117745431 18358895438104750676618147)
          ·
            refine ⟨27538343157157126014927221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18358895438104750676618147 27538343157157126014927221)
            ·
              refine ⟨2581719670983480563899427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27538343157157126014927221 2581719670983480563899427)
              ·
                refine ⟨3872579506475220845849141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581719670983480563899427 3872579506475220845849141)
                ·
                  refine ⟨363054328732051954298357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3872579506475220845849141 363054328732051954298357)
                  ·
                    rfl

theorem cell22_3181706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_3181706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181706 prefixEnd_3181706 := by exact prefixLift 3181706
  have htrace : WordTrace (prefixWord ++ tailWord_3181706) baseStart_3181706 baseEnd_3181706 := by
    simpa [prefixWord, tailWord_3181706, baseEnd_3181706] using wordTrace_append hprefix tailTrace_3181706
  have hstable : (prefixWord ++ tailWord_3181706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181706).length < 2 ^ (prefixWord ++ tailWord_3181706).sum := by decide
  have hdescent : baseEnd_3181706 < baseStart_3181706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181717 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 8]
def baseStart_3181717 : Nat := 118140960795 + 3181717 * 2 ^ 59
def prefixEnd_3181717 : Nat := 4983230072969 + 3 ^ 40 * 3181717 * 2
def baseEnd_3181717 : Nat := 363055583906985166956679

theorem tailTrace_3181717 : CollatzResearch.WordTrace tailWord_3181717 prefixEnd_3181717 363055583906985166956679 := by
  unfold tailWord_3181717
  simp only [CollatzResearch.WordTrace]
  refine ⟨116046752614190177846903405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77364501742793451897935603 116046752614190177846903405)
  ·
    refine ⟨43517532230321316692588777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116046752614190177846903405 43517532230321316692588777)
    ·
      refine ⟨32638149172740987519441583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43517532230321316692588777 32638149172740987519441583)
      ·
        refine ⟨48957223759111481279162375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32638149172740987519441583 48957223759111481279162375)
        ·
          refine ⟨73435835638667221918743563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48957223759111481279162375 73435835638667221918743563)
          ·
            refine ⟨110153753458000832878115345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73435835638667221918743563 110153753458000832878115345)
            ·
              refine ⟨82615315093500624658586509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110153753458000832878115345 82615315093500624658586509)
              ·
                refine ⟨30980743160062734246969941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82615315093500624658586509 30980743160062734246969941)
                ·
                  refine ⟨363055583906985166956679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30980743160062734246969941 363055583906985166956679)
                  ·
                    rfl

theorem cell22_3181717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_3181717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181717 prefixEnd_3181717 := by exact prefixLift 3181717
  have htrace : WordTrace (prefixWord ++ tailWord_3181717) baseStart_3181717 baseEnd_3181717 := by
    simpa [prefixWord, tailWord_3181717, baseEnd_3181717] using wordTrace_append hprefix tailTrace_3181717
  have hstable : (prefixWord ++ tailWord_3181717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181717).length < 2 ^ (prefixWord ++ tailWord_3181717).sum := by decide
  have hdescent : baseEnd_3181717 < baseStart_3181717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181727 : List Nat := [1, 1, 2, 6, 3, 1, 1, 3, 1, 3]
def baseStart_3181727 : Nat := 118140960795 + 3181727 * 2 ^ 59
def prefixEnd_3181727 : Nat := 4983230072969 + 3 ^ 40 * 3181727 * 2
def baseEnd_3181727 : Nat := 1089170174925318808120007

theorem tailTrace_3181727 : CollatzResearch.WordTrace tailWord_3181727 prefixEnd_3181727 1089170174925318808120007 := by
  unfold tailWord_3181727
  simp only [CollatzResearch.WordTrace]
  refine ⟨116047117344153949554767435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77364744896102633036511623 116047117344153949554767435)
  ·
    refine ⟨174070676016230924332151153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116047117344153949554767435 174070676016230924332151153)
    ·
      refine ⟨130553007012173193249113365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174070676016230924332151153 130553007012173193249113365)
      ·
        refine ⟨6119672203695618433552189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130553007012173193249113365 6119672203695618433552189)
        ·
          refine ⟨2294877076385856912582071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6119672203695618433552189 2294877076385856912582071)
          ·
            refine ⟨3442315614578785368873107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294877076385856912582071 3442315614578785368873107)
            ·
              refine ⟨5163473421868178053309661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442315614578785368873107 5163473421868178053309661)
              ·
                refine ⟨1936302533200566769991123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5163473421868178053309661 1936302533200566769991123)
                ·
                  refine ⟨2904453799800850154986685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936302533200566769991123 2904453799800850154986685)
                  ·
                    refine ⟨1089170174925318808120007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904453799800850154986685 1089170174925318808120007)
                    ·
                      rfl

theorem cell22_3181727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 3].length) (baseStart_3181727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181727 prefixEnd_3181727 := by exact prefixLift 3181727
  have htrace : WordTrace (prefixWord ++ tailWord_3181727) baseStart_3181727 baseEnd_3181727 := by
    simpa [prefixWord, tailWord_3181727, baseEnd_3181727] using wordTrace_append hprefix tailTrace_3181727
  have hstable : (prefixWord ++ tailWord_3181727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181727).length < 2 ^ (prefixWord ++ tailWord_3181727).sum := by decide
  have hdescent : baseEnd_3181727 < baseStart_3181727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181781 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3181781 : Nat := 118140960795 + 3181781 * 2 ^ 59
def prefixEnd_3181781 : Nat := 4983230072969 + 3 ^ 40 * 3181781 * 2
def baseEnd_3181781 : Nat := 1089188660228880667269841

theorem tailTrace_3181781 : CollatzResearch.WordTrace tailWord_3181781 prefixEnd_3181781 1089188660228880667269841 := by
  unfold tailWord_3181781
  simp only [CollatzResearch.WordTrace]
  refine ⟨116049086885958316777233197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77366057923972211184822131 116049086885958316777233197)
  ·
    refine ⟨43518407582234368791462449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116049086885958316777233197 43518407582234368791462449)
    ·
      refine ⟨32638805686675776593596837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43518407582234368791462449 32638805686675776593596837)
      ·
        refine ⟨6119776066251708111299407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32638805686675776593596837 6119776066251708111299407)
        ·
          refine ⟨9179664099377562166949111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119776066251708111299407 9179664099377562166949111)
          ·
            refine ⟨13769496149066343250423667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9179664099377562166949111 13769496149066343250423667)
            ·
              refine ⟨20654244223599514875635501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13769496149066343250423667 20654244223599514875635501)
              ·
                refine ⟨7745341583849818078363313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20654244223599514875635501 7745341583849818078363313)
                ·
                  refine ⟨5809006187887363558772485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745341583849818078363313 5809006187887363558772485)
                  ·
                    refine ⟨1089188660228880667269841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5809006187887363558772485 1089188660228880667269841)
                    ·
                      rfl

theorem cell22_3181781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3181781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181781 prefixEnd_3181781 := by exact prefixLift 3181781
  have htrace : WordTrace (prefixWord ++ tailWord_3181781) baseStart_3181781 baseEnd_3181781 := by
    simpa [prefixWord, tailWord_3181781, baseEnd_3181781] using wordTrace_append hprefix tailTrace_3181781
  have hstable : (prefixWord ++ tailWord_3181781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181781).length < 2 ^ (prefixWord ++ tailWord_3181781).sum := by decide
  have hdescent : baseEnd_3181781 < baseStart_3181781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181828 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_3181828 : Nat := 118140960795 + 3181828 * 2 ^ 59
def prefixEnd_3181828 : Nat := 4983230072969 + 3 ^ 40 * 3181828 * 2
def baseEnd_3181828 : Nat := 1089204749289388211344697

theorem tailTrace_3181828 : CollatzResearch.WordTrace tailWord_3181828 prefixEnd_3181828 1089204749289388211344697 := by
  unfold tailWord_3181828
  simp only [CollatzResearch.WordTrace]
  refine ⟨58025400558394021902097069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77367200744525362536129425 58025400558394021902097069)
  ·
    refine ⟨21759525209397758213286401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58025400558394021902097069 21759525209397758213286401)
    ·
      refine ⟨16319643907048318659964801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21759525209397758213286401 16319643907048318659964801)
      ·
        refine ⟨12239732930286238994973601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16319643907048318659964801 12239732930286238994973601)
        ·
          refine ⟨9179799697714679246230201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12239732930286238994973601 9179799697714679246230201)
          ·
            refine ⟨6884849773286009434672651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9179799697714679246230201 6884849773286009434672651)
            ·
              refine ⟨10327274659929014152008977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884849773286009434672651 10327274659929014152008977)
              ·
                refine ⟨7745455994946760614006733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10327274659929014152008977 7745455994946760614006733)
                ·
                  refine ⟨2904545998105035230252525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7745455994946760614006733 2904545998105035230252525)
                  ·
                    refine ⟨1089204749289388211344697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904545998105035230252525 1089204749289388211344697)
                    ·
                      rfl

theorem cell22_3181828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_3181828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181828 prefixEnd_3181828 := by exact prefixLift 3181828
  have htrace : WordTrace (prefixWord ++ tailWord_3181828) baseStart_3181828 baseEnd_3181828 := by
    simpa [prefixWord, tailWord_3181828, baseEnd_3181828] using wordTrace_append hprefix tailTrace_3181828
  have hstable : (prefixWord ++ tailWord_3181828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181828).length < 2 ^ (prefixWord ++ tailWord_3181828).sum := by decide
  have hdescent : baseEnd_3181828 < baseStart_3181828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181886 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_3181886 : Nat := 118140960795 + 3181886 * 2 ^ 59
def prefixEnd_3181886 : Nat := 4983230072969 + 3 ^ 40 * 3181886 * 2
def baseEnd_3181886 : Nat := 363074867958231797798173

theorem tailTrace_3181886 : CollatzResearch.WordTrace tailWord_3181886 prefixEnd_3181886 363074867958231797798173 := by
  unfold tailWord_3181886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14506614568822239963725689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77368611033718613139870341 14506614568822239963725689)
  ·
    refine ⟨10879960926616679972794267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14506614568822239963725689 10879960926616679972794267)
    ·
      refine ⟨16319941389925019959191401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10879960926616679972794267 16319941389925019959191401)
      ·
        refine ⟨12239956042443764969393551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16319941389925019959191401 12239956042443764969393551)
        ·
          refine ⟨18359934063665647454090327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12239956042443764969393551 18359934063665647454090327)
          ·
            refine ⟨27539901095498471181135491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18359934063665647454090327 27539901095498471181135491)
            ·
              refine ⟨41309851643247706771703237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27539901095498471181135491 41309851643247706771703237)
              ·
                refine ⟨7745597183108945019694357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41309851643247706771703237 7745597183108945019694357)
                ·
                  refine ⟨363074867958231797798173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7745597183108945019694357 363074867958231797798173)
                  ·
                    rfl

theorem cell22_3181886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_3181886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181886 prefixEnd_3181886 := by exact prefixLift 3181886
  have htrace : WordTrace (prefixWord ++ tailWord_3181886) baseStart_3181886 baseEnd_3181886 := by
    simpa [prefixWord, tailWord_3181886, baseEnd_3181886] using wordTrace_append hprefix tailTrace_3181886
  have hstable : (prefixWord ++ tailWord_3181886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181886).length < 2 ^ (prefixWord ++ tailWord_3181886).sum := by decide
  have hdescent : baseEnd_3181886 < baseStart_3181886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181914 : List Nat := [3, 1, 1, 2, 1, 2, 12]
def baseStart_3181914 : Nat := 118140960795 + 3181914 * 2 ^ 59
def prefixEnd_3181914 : Nat := 4983230072969 + 3 ^ 40 * 3181914 * 2
def baseEnd_3181914 : Nat := 40342006994330098284979

theorem tailTrace_3181914 : CollatzResearch.WordTrace tailWord_3181914 prefixEnd_3181914 40342006994330098284979 := by
  unfold tailWord_3181914
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013484448619120122956199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77369291862984320327883197 29013484448619120122956199)
  ·
    refine ⟨43520226672928680184434299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29013484448619120122956199 43520226672928680184434299)
    ·
      refine ⟨65280340009393020276651449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43520226672928680184434299 65280340009393020276651449)
      ·
        refine ⟨48960255007044765207488587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65280340009393020276651449 48960255007044765207488587)
        ·
          refine ⟨73440382510567147811232881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48960255007044765207488587 73440382510567147811232881)
          ·
            refine ⟨55080286882925360858424661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73440382510567147811232881 55080286882925360858424661)
            ·
              refine ⟨40342006994330098284979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 55080286882925360858424661 40342006994330098284979)
              ·
                rfl

theorem cell22_3181914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 12].length) (baseStart_3181914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181914 prefixEnd_3181914 := by exact prefixLift 3181914
  have htrace : WordTrace (prefixWord ++ tailWord_3181914) baseStart_3181914 baseEnd_3181914 := by
    simpa [prefixWord, tailWord_3181914, baseEnd_3181914] using wordTrace_append hprefix tailTrace_3181914
  have hstable : (prefixWord ++ tailWord_3181914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181914).length < 2 ^ (prefixWord ++ tailWord_3181914).sum := by decide
  have hdescent : baseEnd_3181914 < baseStart_3181914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181920 : List Nat := [2, 1, 1, 3, 4, 2, 3, 2, 4]
def baseStart_3181920 : Nat := 118140960795 + 3181920 * 2 ^ 59
def prefixEnd_3181920 : Nat := 4983230072969 + 3 ^ 40 * 3181920 * 2
def baseEnd_3181920 : Nat := 363078747589843546014805

theorem tailTrace_3181920 : CollatzResearch.WordTrace tailWord_3181920 prefixEnd_3181920 363078747589843546014805 := by
  unfold tailWord_3181920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58027078316227371758271607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77369437754969829011028809 58027078316227371758271607)
  ·
    refine ⟨87040617474341057637407411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58027078316227371758271607 87040617474341057637407411)
    ·
      refine ⟨130560926211511586456111117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87040617474341057637407411 130560926211511586456111117)
      ·
        refine ⟨48960347329316844921041669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130560926211511586456111117 48960347329316844921041669)
        ·
          refine ⟨9180065124246908422695313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48960347329316844921041669 9180065124246908422695313)
          ·
            refine ⟨6885048843185181317021485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9180065124246908422695313 6885048843185181317021485)
            ·
              refine ⟨2581893316194442993883057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6885048843185181317021485 2581893316194442993883057)
              ·
                refine ⟨1936419987145832245412293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581893316194442993883057 1936419987145832245412293)
                ·
                  refine ⟨363078747589843546014805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936419987145832245412293 363078747589843546014805)
                  ·
                    rfl

theorem cell22_3181920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_3181920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181920 prefixEnd_3181920 := by exact prefixLift 3181920
  have htrace : WordTrace (prefixWord ++ tailWord_3181920) baseStart_3181920 baseEnd_3181920 := by
    simpa [prefixWord, tailWord_3181920, baseEnd_3181920] using wordTrace_append hprefix tailTrace_3181920
  have hstable : (prefixWord ++ tailWord_3181920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181920).length < 2 ^ (prefixWord ++ tailWord_3181920).sum := by decide
  have hdescent : baseEnd_3181920 < baseStart_3181920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181929 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_3181929 : Nat := 118140960795 + 3181929 * 2 ^ 59
def prefixEnd_3181929 : Nat := 4983230072969 + 3 ^ 40 * 3181929 * 2
def baseEnd_3181929 : Nat := 1089239323653457614569387

theorem tailTrace_3181929 : CollatzResearch.WordTrace tailWord_3181929 prefixEnd_3181929 1089239323653457614569387 := by
  unfold tailWord_3181929
  simp only [CollatzResearch.WordTrace]
  refine ⟨116054484889422138053620841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77369656592948092035747227 116054484889422138053620841)
  ·
    refine ⟨87040863667066603540215631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116054484889422138053620841 87040863667066603540215631)
    ·
      refine ⟨130561295500599905310323447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87040863667066603540215631 130561295500599905310323447)
      ·
        refine ⟨195841943250899857965485171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130561295500599905310323447 195841943250899857965485171)
        ·
          refine ⟨293762914876349786948227757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195841943250899857965485171 293762914876349786948227757)
          ·
            refine ⟨110161093078631170105585409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293762914876349786948227757 110161093078631170105585409)
            ·
              refine ⟨82620819808973377579189057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110161093078631170105585409 82620819808973377579189057)
              ·
                refine ⟨61965614856730033184391793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82620819808973377579189057 61965614856730033184391793)
                ·
                  refine ⟨46474211142547524888293845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61965614856730033184391793 46474211142547524888293845)
                  ·
                    refine ⟨1089239323653457614569387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46474211142547524888293845 1089239323653457614569387)
                    ·
                      rfl

theorem cell22_3181929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_3181929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181929 prefixEnd_3181929 := by exact prefixLift 3181929
  have htrace : WordTrace (prefixWord ++ tailWord_3181929) baseStart_3181929 baseEnd_3181929 := by
    simpa [prefixWord, tailWord_3181929, baseEnd_3181929] using wordTrace_append hprefix tailTrace_3181929
  have hstable : (prefixWord ++ tailWord_3181929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181929).length < 2 ^ (prefixWord ++ tailWord_3181929).sum := by decide
  have hdescent : baseEnd_3181929 < baseStart_3181929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181982 : List Nat := [4, 3, 1, 2, 3, 1, 1, 7]
def baseStart_3181982 : Nat := 118140960795 + 3181982 * 2 ^ 59
def prefixEnd_3181982 : Nat := 4983230072969 + 3 ^ 40 * 3181982 * 2
def baseEnd_3181982 : Nat := 121028607404064793666025

theorem tailTrace_3181982 : CollatzResearch.WordTrace tailWord_3181982 prefixEnd_3181982 121028607404064793666025 := by
  unfold tailWord_3181982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14507052244778766013162525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77370945305486752070200133 14507052244778766013162525)
  ·
    refine ⟨5440144591792037254935947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14507052244778766013162525 5440144591792037254935947)
    ·
      refine ⟨8160216887688055882403921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5440144591792037254935947 8160216887688055882403921)
      ·
        refine ⟨6120162665766041911802941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8160216887688055882403921 6120162665766041911802941)
        ·
          refine ⟨2295060999662265716926103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6120162665766041911802941 2295060999662265716926103)
          ·
            refine ⟨3442591499493398575389155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295060999662265716926103 3442591499493398575389155)
            ·
              refine ⟨5163887249240097863083733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442591499493398575389155 5163887249240097863083733)
              ·
                refine ⟨121028607404064793666025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5163887249240097863083733 121028607404064793666025)
                ·
                  rfl

theorem cell22_3181982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_3181982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3181982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3181982 prefixEnd_3181982 := by exact prefixLift 3181982
  have htrace : WordTrace (prefixWord ++ tailWord_3181982) baseStart_3181982 baseEnd_3181982 := by
    simpa [prefixWord, tailWord_3181982, baseEnd_3181982] using wordTrace_append hprefix tailTrace_3181982
  have hstable : (prefixWord ++ tailWord_3181982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181982).length < 2 ^ (prefixWord ++ tailWord_3181982).sum := by decide
  have hdescent : baseEnd_3181982 < baseStart_3181982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182023 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3182023 : Nat := 118140960795 + 3182023 * 2 ^ 59
def prefixEnd_3182023 : Nat := 4983230072969 + 3 ^ 40 * 3182023 * 2
def baseEnd_3182023 : Nat := 1089271501774472702719099

theorem tailTrace_3182023 : CollatzResearch.WordTrace tailWord_3182023 prefixEnd_3182023 1089271501774472702719099 := by
  unfold tailWord_3182023
  simp only [CollatzResearch.WordTrace]
  refine ⟨116057913351081592107542723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77371942234054394738361815 116057913351081592107542723)
  ·
    refine ⟨174086870026622388161314085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116057913351081592107542723 174086870026622388161314085)
    ·
      refine ⟨32641288129991697780246391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174086870026622388161314085 32641288129991697780246391)
      ·
        refine ⟨48961932194987546670369587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32641288129991697780246391 48961932194987546670369587)
        ·
          refine ⟨73442898292481320005554381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48961932194987546670369587 73442898292481320005554381)
          ·
            refine ⟨27541086859680495002082893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73442898292481320005554381 27541086859680495002082893)
            ·
              refine ⟨10327907572380185625781085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27541086859680495002082893 10327907572380185625781085)
              ·
                refine ⟨3872965339642569609667907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10327907572380185625781085 3872965339642569609667907)
                ·
                  refine ⟨5809448009463854414501861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872965339642569609667907 5809448009463854414501861)
                  ·
                    refine ⟨1089271501774472702719099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5809448009463854414501861 1089271501774472702719099)
                    ·
                      rfl

theorem cell22_3182023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3182023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182023 prefixEnd_3182023 := by exact prefixLift 3182023
  have htrace : WordTrace (prefixWord ++ tailWord_3182023) baseStart_3182023 baseEnd_3182023 := by
    simpa [prefixWord, tailWord_3182023, baseEnd_3182023] using wordTrace_append hprefix tailTrace_3182023
  have hstable : (prefixWord ++ tailWord_3182023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182023).length < 2 ^ (prefixWord ++ tailWord_3182023).sum := by decide
  have hdescent : baseEnd_3182023 < baseStart_3182023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182070 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_3182070 : Nat := 118140960795 + 3182070 * 2 ^ 59
def prefixEnd_3182070 : Nat := 4983230072969 + 3 ^ 40 * 3182070 * 2
def baseEnd_3182070 : Nat := 1089287590834980246793955

theorem tailTrace_3182070 : CollatzResearch.WordTrace tailWord_3182070 prefixEnd_3182070 1089287590834980246793955 := by
  unfold tailWord_3182070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253726723869457445906479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77373085054607546089669109 7253726723869457445906479)
  ·
    refine ⟨10880590085804186168859719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7253726723869457445906479 10880590085804186168859719)
    ·
      refine ⟨16320885128706279253289579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10880590085804186168859719 16320885128706279253289579)
      ·
        refine ⟨24481327693059418879934369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16320885128706279253289579 24481327693059418879934369)
        ·
          refine ⟨18360995769794564159950777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24481327693059418879934369 18360995769794564159950777)
          ·
            refine ⟨13770746827345923119963083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18360995769794564159950777 13770746827345923119963083)
            ·
              refine ⟨20656120241018884679944625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13770746827345923119963083 20656120241018884679944625)
              ·
                refine ⟨15492090180764163509958469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20656120241018884679944625 15492090180764163509958469)
                ·
                  refine ⟨2904766908893280658117213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15492090180764163509958469 2904766908893280658117213)
                  ·
                    refine ⟨1089287590834980246793955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904766908893280658117213 1089287590834980246793955)
                    ·
                      rfl

theorem cell22_3182070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_3182070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182070 prefixEnd_3182070 := by exact prefixLift 3182070
  have htrace : WordTrace (prefixWord ++ tailWord_3182070) baseStart_3182070 baseEnd_3182070 := by
    simpa [prefixWord, tailWord_3182070, baseEnd_3182070] using wordTrace_append hprefix tailTrace_3182070
  have hstable : (prefixWord ++ tailWord_3182070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182070).length < 2 ^ (prefixWord ++ tailWord_3182070).sum := by decide
  have hdescent : baseEnd_3182070 < baseStart_3182070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182104 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 2, 3]
def baseStart_3182104 : Nat := 118140960795 + 3182104 * 2 ^ 59
def prefixEnd_3182104 : Nat := 4983230072969 + 3 ^ 40 * 3182104 * 2
def baseEnd_3182104 : Nat := 1089299229729815491443851

theorem tailTrace_3182104 : CollatzResearch.WordTrace tailWord_3182104 prefixEnd_3182104 1089299229729815491443851 := by
  unfold tailWord_3182104
  simp only [CollatzResearch.WordTrace]
  refine ⟨58030433831894071470620683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77373911775858761960827577 58030433831894071470620683)
  ·
    refine ⟨87045650747841107205931025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58030433831894071470620683 87045650747841107205931025)
    ·
      refine ⟨65284238060880830404448269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87045650747841107205931025 65284238060880830404448269)
      ·
        refine ⟨24481589272830311401668101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65284238060880830404448269 24481589272830311401668101)
        ·
          refine ⟨4590297988655683387812769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24481589272830311401668101 4590297988655683387812769)
          ·
            refine ⟨3442723491491762540859577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4590297988655683387812769 3442723491491762540859577)
            ·
              refine ⟨2582042618618821905644683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3442723491491762540859577 2582042618618821905644683)
              ·
                refine ⟨3873063927928232858467025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582042618618821905644683 3873063927928232858467025)
                ·
                  refine ⟨2904797945946174643850269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3873063927928232858467025 2904797945946174643850269)
                  ·
                    refine ⟨1089299229729815491443851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904797945946174643850269 1089299229729815491443851)
                    ·
                      rfl

theorem cell22_3182104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_3182104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182104 prefixEnd_3182104 := by exact prefixLift 3182104
  have htrace : WordTrace (prefixWord ++ tailWord_3182104) baseStart_3182104 baseEnd_3182104 := by
    simpa [prefixWord, tailWord_3182104, baseEnd_3182104] using wordTrace_append hprefix tailTrace_3182104
  have hstable : (prefixWord ++ tailWord_3182104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182104).length < 2 ^ (prefixWord ++ tailWord_3182104).sum := by decide
  have hdescent : baseEnd_3182104 < baseStart_3182104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182145 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 5]
def baseStart_3182145 : Nat := 118140960795 + 3182145 * 2 ^ 59
def prefixEnd_3182145 : Nat := 4983230072969 + 3 ^ 40 * 3182145 * 2
def baseEnd_3182145 : Nat := 363104421622568350389575

theorem tailTrace_3182145 : CollatzResearch.WordTrace tailWord_3182145 prefixEnd_3182145 363104421622568350389575 := by
  unfold tailWord_3182145
  simp only [CollatzResearch.WordTrace]
  refine ⟨116062363056639606943483889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77374908704426404628989259 116062363056639606943483889)
  ·
    refine ⟨87046772292479705207612917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116062363056639606943483889 87046772292479705207612917)
    ·
      refine ⟨8160634902419972363213711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87046772292479705207612917 8160634902419972363213711)
      ·
        refine ⟨12240952353629958544820567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8160634902419972363213711 12240952353629958544820567)
        ·
          refine ⟨18361428530444937817230851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12240952353629958544820567 18361428530444937817230851)
          ·
            refine ⟨27542142795667406725846277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18361428530444937817230851 27542142795667406725846277)
            ·
              refine ⟨5164151774187638761096177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27542142795667406725846277 5164151774187638761096177)
              ·
                refine ⟨3873113830640729070822133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5164151774187638761096177 3873113830640729070822133)
                ·
                  refine ⟨363104421622568350389575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3873113830640729070822133 363104421622568350389575)
                  ·
                    rfl

theorem cell22_3182145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_3182145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182145 prefixEnd_3182145 := by exact prefixLift 3182145
  have htrace : WordTrace (prefixWord ++ tailWord_3182145) baseStart_3182145 baseEnd_3182145 := by
    simpa [prefixWord, tailWord_3182145, baseEnd_3182145] using wordTrace_append hprefix tailTrace_3182145
  have hstable : (prefixWord ++ tailWord_3182145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182145).length < 2 ^ (prefixWord ++ tailWord_3182145).sum := by decide
  have hdescent : baseEnd_3182145 < baseStart_3182145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182166 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3182166 : Nat := 118140960795 + 3182166 * 2 ^ 59
def prefixEnd_3182166 : Nat := 4983230072969 + 3 ^ 40 * 3182166 * 2
def baseEnd_3182166 : Nat := 1089320453596867996393661

theorem tailTrace_3182166 : CollatzResearch.WordTrace tailWord_3182166 prefixEnd_3182166 1089320453596867996393661 := by
  unfold tailWord_3182166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253945561847720470624897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77375419326375685019998901 7253945561847720470624897)
  ·
    refine ⟨5440459171385790352968673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7253945561847720470624897 5440459171385790352968673)
    ·
      refine ⟨4080344378539342764726505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5440459171385790352968673 4080344378539342764726505)
      ·
        refine ⟨3060258283904507073544879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4080344378539342764726505 3060258283904507073544879)
        ·
          refine ⟨4590387425856760610317319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060258283904507073544879 4590387425856760610317319)
          ·
            refine ⟨6885581138785140915475979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590387425856760610317319 6885581138785140915475979)
            ·
              refine ⟨10328371708177711373213969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6885581138785140915475979 10328371708177711373213969)
              ·
                refine ⟨7746278781133283529910477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10328371708177711373213969 7746278781133283529910477)
                ·
                  refine ⟨2904854542924981323716429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7746278781133283529910477 2904854542924981323716429)
                  ·
                    refine ⟨1089320453596867996393661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904854542924981323716429 1089320453596867996393661)
                    ·
                      rfl

theorem cell22_3182166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3182166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182166 prefixEnd_3182166 := by exact prefixLift 3182166
  have htrace : WordTrace (prefixWord ++ tailWord_3182166) baseStart_3182166 baseEnd_3182166 := by
    simpa [prefixWord, tailWord_3182166, baseEnd_3182166] using wordTrace_append hprefix tailTrace_3182166
  have hstable : (prefixWord ++ tailWord_3182166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182166).length < 2 ^ (prefixWord ++ tailWord_3182166).sum := by decide
  have hdescent : baseEnd_3182166 < baseStart_3182166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182192 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 1, 4]
def baseStart_3182192 : Nat := 118140960795 + 3182192 * 2 ^ 59
def prefixEnd_3182192 : Nat := 4983230072969 + 3 ^ 40 * 3182192 * 2
def baseEnd_3182192 : Nat := 1089329353928212595243581

theorem tailTrace_3182192 : CollatzResearch.WordTrace tailWord_3182192 prefixEnd_3182192 1089329353928212595243581 := by
  unfold tailWord_3182192
  simp only [CollatzResearch.WordTrace]
  refine ⟨58032038643734666985222415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77376051524979555980296553 58032038643734666985222415)
  ·
    refine ⟨87048057965602000477833623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58032038643734666985222415 87048057965602000477833623)
    ·
      refine ⟨130572086948403000716750435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87048057965602000477833623 130572086948403000716750435)
      ·
        refine ⟨195858130422604501075125653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130572086948403000716750435 195858130422604501075125653)
        ·
          refine ⟨9180849863559585987896515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195858130422604501075125653 9180849863559585987896515)
          ·
            refine ⟨13771274795339378981844773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9180849863559585987896515 13771274795339378981844773)
            ·
              refine ⟨2582114024126133559095895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13771274795339378981844773 2582114024126133559095895)
              ·
                refine ⟨3873171036189200338643843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582114024126133559095895 3873171036189200338643843)
                ·
                  refine ⟨5809756554283800507965765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873171036189200338643843 5809756554283800507965765)
                  ·
                    refine ⟨1089329353928212595243581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5809756554283800507965765 1089329353928212595243581)
                    ·
                      rfl

theorem cell22_3182192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_3182192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182192 prefixEnd_3182192 := by exact prefixLift 3182192
  have htrace : WordTrace (prefixWord ++ tailWord_3182192) baseStart_3182192 baseEnd_3182192 := by
    simpa [prefixWord, tailWord_3182192, baseEnd_3182192] using wordTrace_append hprefix tailTrace_3182192
  have hstable : (prefixWord ++ tailWord_3182192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182192).length < 2 ^ (prefixWord ++ tailWord_3182192).sum := by decide
  have hdescent : baseEnd_3182192 < baseStart_3182192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182203 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 4, 4]
def baseStart_3182203 : Nat := 118140960795 + 3182203 * 2 ^ 59
def prefixEnd_3182203 : Nat := 4983230072969 + 3 ^ 40 * 3182203 * 2
def baseEnd_3182203 : Nat := 1089333119453012233218547

theorem tailTrace_3182203 : CollatzResearch.WordTrace tailWord_3182203 prefixEnd_3182203 1089333119453012233218547 := by
  unfold tailWord_3182203
  simp only [CollatzResearch.WordTrace]
  refine ⟨116064478490429482849095263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77376318993619655232730175 116064478490429482849095263)
  ·
    refine ⟨174096717735644224273642895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116064478490429482849095263 174096717735644224273642895)
    ·
      refine ⟨261145076603466336410464343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174096717735644224273642895 261145076603466336410464343)
      ·
        refine ⟨391717614905199504615696515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261145076603466336410464343 391717614905199504615696515)
        ·
          refine ⟨587576422357799256923544773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391717614905199504615696515 587576422357799256923544773)
          ·
            refine ⟨110170579192087360673164645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 587576422357799256923544773 110170579192087360673164645)
            ·
              refine ⟨20656983598516380126218371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110170579192087360673164645 20656983598516380126218371)
              ·
                refine ⟨30985475397774570189327557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20656983598516380126218371 30985475397774570189327557)
                ·
                  refine ⟨5809776637082731910498917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30985475397774570189327557 5809776637082731910498917)
                  ·
                    refine ⟨1089333119453012233218547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5809776637082731910498917 1089333119453012233218547)
                    ·
                      rfl

theorem cell22_3182203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_3182203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182203 prefixEnd_3182203 := by exact prefixLift 3182203
  have htrace : WordTrace (prefixWord ++ tailWord_3182203) baseStart_3182203 baseEnd_3182203 := by
    simpa [prefixWord, tailWord_3182203, baseEnd_3182203] using wordTrace_append hprefix tailTrace_3182203
  have hstable : (prefixWord ++ tailWord_3182203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182203).length < 2 ^ (prefixWord ++ tailWord_3182203).sum := by decide
  have hdescent : baseEnd_3182203 < baseStart_3182203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182222 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_3182222 : Nat := 118140960795 + 3182222 * 2 ^ 59
def prefixEnd_3182222 : Nat := 4983230072969 + 3 ^ 40 * 3182222 * 2
def baseEnd_3182222 : Nat := 1089339623541302516993489

theorem tailTrace_3182222 : CollatzResearch.WordTrace tailWord_3182222 prefixEnd_3182222 1089339623541302516993489 := by
  unfold tailWord_3182222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14508146434670081136754615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77376780984907099396024613 14508146434670081136754615)
  ·
    refine ⟨21762219652005121705131923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14508146434670081136754615 21762219652005121705131923)
    ·
      refine ⟨32643329478007682557697885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21762219652005121705131923 32643329478007682557697885)
      ·
        refine ⟨12241248554252880959136707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32643329478007682557697885 12241248554252880959136707)
        ·
          refine ⟨18361872831379321438705061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12241248554252880959136707 18361872831379321438705061)
          ·
            refine ⟨3442851155883622769757199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18361872831379321438705061 3442851155883622769757199)
            ·
              refine ⟨5164276733825434154635799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442851155883622769757199 5164276733825434154635799)
              ·
                refine ⟨7746415100738151231953699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164276733825434154635799 7746415100738151231953699)
                ·
                  refine ⟨11619622651107226847930549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7746415100738151231953699 11619622651107226847930549)
                  ·
                    refine ⟨1089339623541302516993489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11619622651107226847930549 1089339623541302516993489)
                    ·
                      rfl

theorem cell22_3182222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_3182222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182222 prefixEnd_3182222 := by exact prefixLift 3182222
  have htrace : WordTrace (prefixWord ++ tailWord_3182222) baseStart_3182222 baseEnd_3182222 := by
    simpa [prefixWord, tailWord_3182222, baseEnd_3182222] using wordTrace_append hprefix tailTrace_3182222
  have hstable : (prefixWord ++ tailWord_3182222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182222).length < 2 ^ (prefixWord ++ tailWord_3182222).sum := by decide
  have hdescent : baseEnd_3182222 < baseStart_3182222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182254 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3182254 : Nat := 118140960795 + 3182254 * 2 ^ 59
def prefixEnd_3182254 : Nat := 4983230072969 + 3 ^ 40 * 3182254 * 2
def baseEnd_3182254 : Nat := 1089350577795265100193391

theorem tailTrace_3182254 : CollatzResearch.WordTrace tailWord_3182254 prefixEnd_3182254 1089350577795265100193391 := by
  unfold tailWord_3182254
  simp only [CollatzResearch.WordTrace]
  refine ⟨14508292326655589819900227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77377559075496479039467877 14508292326655589819900227)
  ·
    refine ⟨21762438489983384729850341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14508292326655589819900227 21762438489983384729850341)
    ·
      refine ⟨4080457216871884636846939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21762438489983384729850341 4080457216871884636846939)
      ·
        refine ⟨6120685825307826955270409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080457216871884636846939 6120685825307826955270409)
        ·
          refine ⟨4590514368980870216452807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6120685825307826955270409 4590514368980870216452807)
          ·
            refine ⟨6885771553471305324679211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590514368980870216452807 6885771553471305324679211)
            ·
              refine ⟨10328657330206957987018817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6885771553471305324679211 10328657330206957987018817)
              ·
                refine ⟨7746492997655218490264113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10328657330206957987018817 7746492997655218490264113)
                ·
                  refine ⟨5809869748241413867698085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7746492997655218490264113 5809869748241413867698085)
                  ·
                    refine ⟨1089350577795265100193391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5809869748241413867698085 1089350577795265100193391)
                    ·
                      rfl

theorem cell22_3182254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3182254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182254 prefixEnd_3182254 := by exact prefixLift 3182254
  have htrace : WordTrace (prefixWord ++ tailWord_3182254) baseStart_3182254 baseEnd_3182254 := by
    simpa [prefixWord, tailWord_3182254, baseEnd_3182254] using wordTrace_append hprefix tailTrace_3182254
  have hstable : (prefixWord ++ tailWord_3182254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182254).length < 2 ^ (prefixWord ++ tailWord_3182254).sum := by decide
  have hdescent : baseEnd_3182254 < baseStart_3182254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182267 : List Nat := [1, 1, 1, 1, 1, 2, 3, 8, 1, 3]
def baseStart_3182267 : Nat := 118140960795 + 3182267 * 2 ^ 59
def prefixEnd_3182267 : Nat := 4983230072969 + 3 ^ 40 * 3182267 * 2
def baseEnd_3182267 : Nat := 1089355027960937399618351

theorem tailTrace_3182267 : CollatzResearch.WordTrace tailWord_3182267 prefixEnd_3182267 1089355027960937399618351 := by
  unfold tailWord_3182267
  simp only [CollatzResearch.WordTrace]
  refine ⟨116066812762197621779425055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77377875174798414519616703 116066812762197621779425055)
  ·
    refine ⟨174100219143296432669137583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116066812762197621779425055 174100219143296432669137583)
    ·
      refine ⟨261150328714944649003706375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174100219143296432669137583 261150328714944649003706375)
      ·
        refine ⟨391725493072416973505559563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261150328714944649003706375 391725493072416973505559563)
        ·
          refine ⟨587588239608625460258339345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391725493072416973505559563 587588239608625460258339345)
          ·
            refine ⟨440691179706469095193754509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587588239608625460258339345 440691179706469095193754509)
            ·
              refine ⟨165259192389925910697657941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440691179706469095193754509 165259192389925910697657941)
              ·
                refine ⟨1936631160819444265988179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 165259192389925910697657941 1936631160819444265988179)
                ·
                  refine ⟨2904946741229166398982269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936631160819444265988179 2904946741229166398982269)
                  ·
                    refine ⟨1089355027960937399618351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904946741229166398982269 1089355027960937399618351)
                    ·
                      rfl

theorem cell22_3182267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 3].length) (baseStart_3182267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182267 prefixEnd_3182267 := by exact prefixLift 3182267
  have htrace : WordTrace (prefixWord ++ tailWord_3182267) baseStart_3182267 baseEnd_3182267 := by
    simpa [prefixWord, tailWord_3182267, baseEnd_3182267] using wordTrace_append hprefix tailTrace_3182267
  have hstable : (prefixWord ++ tailWord_3182267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182267).length < 2 ^ (prefixWord ++ tailWord_3182267).sum := by decide
  have hdescent : baseEnd_3182267 < baseStart_3182267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182280 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 5]
def baseStart_3182280 : Nat := 118140960795 + 3182280 * 2 ^ 59
def prefixEnd_3182280 : Nat := 4983230072969 + 3 ^ 40 * 3182280 * 2
def baseEnd_3182280 : Nat := 363119826042203233014437

theorem tailTrace_3182280 : CollatzResearch.WordTrace tailWord_3182280 prefixEnd_3182280 363119826042203233014437 := by
  unfold tailWord_3182280
  simp only [CollatzResearch.WordTrace]
  refine ⟨58033643455575262499824147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77378191274100349999765529 58033643455575262499824147)
  ·
    refine ⟨87050465183362893749736221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58033643455575262499824147 87050465183362893749736221)
    ·
      refine ⟨32643924443761085156151083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87050465183362893749736221 32643924443761085156151083)
      ·
        refine ⟨48965886665641627734226625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32643924443761085156151083 48965886665641627734226625)
        ·
          refine ⟨36724414999231220800669969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48965886665641627734226625 36724414999231220800669969)
          ·
            refine ⟨27543311249423415600502477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36724414999231220800669969 27543311249423415600502477)
            ·
              refine ⟨10328741718533780850188429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27543311249423415600502477 10328741718533780850188429)
              ·
                refine ⟨3873278144450167818820661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10328741718533780850188429 3873278144450167818820661)
                ·
                  refine ⟨363119826042203233014437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3873278144450167818820661 363119826042203233014437)
                  ·
                    rfl

theorem cell22_3182280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_3182280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182280 prefixEnd_3182280 := by exact prefixLift 3182280
  have htrace : WordTrace (prefixWord ++ tailWord_3182280) baseStart_3182280 baseEnd_3182280 := by
    simpa [prefixWord, tailWord_3182280, baseEnd_3182280] using wordTrace_append hprefix tailTrace_3182280
  have hstable : (prefixWord ++ tailWord_3182280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182280).length < 2 ^ (prefixWord ++ tailWord_3182280).sum := by decide
  have hdescent : baseEnd_3182280 < baseStart_3182280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182355 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 2, 4]
def baseStart_3182355 : Nat := 118140960795 + 3182355 * 2 ^ 59
def prefixEnd_3182355 : Nat := 4983230072969 + 3 ^ 40 * 3182355 * 2
def baseEnd_3182355 : Nat := 1089385152159334503418081

theorem tailTrace_3182355 : CollatzResearch.WordTrace tailWord_3182355 prefixEnd_3182355 1089385152159334503418081 := by
  unfold tailWord_3182355
  simp only [CollatzResearch.WordTrace]
  refine ⟨116070022385878812808628519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77380014923919208539085679 116070022385878812808628519)
  ·
    refine ⟨174105033578818219212942779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116070022385878812808628519 174105033578818219212942779)
    ·
      refine ⟨261157550368227328819414169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174105033578818219212942779 261157550368227328819414169)
      ·
        refine ⟨195868162776170496614560627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261157550368227328819414169 195868162776170496614560627)
        ·
          refine ⟨293802244164255744921840941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195868162776170496614560627 293802244164255744921840941)
          ·
            refine ⟨110175841561595904345690353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293802244164255744921840941 110175841561595904345690353)
            ·
              refine ⟨82631881171196928259267765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110175841561595904345690353 82631881171196928259267765)
              ·
                refine ⟨7746738859799712024306353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82631881171196928259267765 7746738859799712024306353)
                ·
                  refine ⟨5810054144849784018229765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7746738859799712024306353 5810054144849784018229765)
                  ·
                    refine ⟨1089385152159334503418081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5810054144849784018229765 1089385152159334503418081)
                    ·
                      rfl

theorem cell22_3182355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_3182355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182355 prefixEnd_3182355 := by exact prefixLift 3182355
  have htrace : WordTrace (prefixWord ++ tailWord_3182355) baseStart_3182355 baseEnd_3182355 := by
    simpa [prefixWord, tailWord_3182355, baseEnd_3182355] using wordTrace_append hprefix tailTrace_3182355
  have hstable : (prefixWord ++ tailWord_3182355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182355).length < 2 ^ (prefixWord ++ tailWord_3182355).sum := by decide
  have hdescent : baseEnd_3182355 < baseStart_3182355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182359 : List Nat := [1, 1, 3, 4, 2, 2, 2, 3, 4]
def baseStart_3182359 : Nat := 118140960795 + 3182359 * 2 ^ 59
def prefixEnd_3182359 : Nat := 4983230072969 + 3 ^ 40 * 3182359 * 2
def baseEnd_3182359 : Nat := 363128840480359942106023

theorem tailTrace_3182359 : CollatzResearch.WordTrace tailWord_3182359 prefixEnd_3182359 363128840480359942106023 := by
  unfold tailWord_3182359
  simp only [CollatzResearch.WordTrace]
  refine ⟨116070168277864321491774131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77380112185242880994516087 116070168277864321491774131)
  ·
    refine ⟨174105252416796482237661197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116070168277864321491774131 174105252416796482237661197)
    ·
      refine ⟨65289469656298680839122949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174105252416796482237661197 65289469656298680839122949)
      ·
        refine ⟨12241775560556002657335553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65289469656298680839122949 12241775560556002657335553)
        ·
          refine ⟨9181331670417001993001665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12241775560556002657335553 9181331670417001993001665)
          ·
            refine ⟨6885998752812751494751249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9181331670417001993001665 6885998752812751494751249)
            ·
              refine ⟨5164499064609563621063437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6885998752812751494751249 5164499064609563621063437)
              ·
                refine ⟨1936687149228586357898789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5164499064609563621063437 1936687149228586357898789)
                ·
                  refine ⟨363128840480359942106023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936687149228586357898789 363128840480359942106023)
                  ·
                    rfl

theorem cell22_3182359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 4].length) (baseStart_3182359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182359 prefixEnd_3182359 := by exact prefixLift 3182359
  have htrace : WordTrace (prefixWord ++ tailWord_3182359) baseStart_3182359 baseEnd_3182359 := by
    simpa [prefixWord, tailWord_3182359, baseEnd_3182359] using wordTrace_append hprefix tailTrace_3182359
  have hstable : (prefixWord ++ tailWord_3182359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182359).length < 2 ^ (prefixWord ++ tailWord_3182359).sum := by decide
  have hdescent : baseEnd_3182359 < baseStart_3182359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182370 : List Nat := [3, 3, 1, 1, 2, 1, 11]
def baseStart_3182370 : Nat := 118140960795 + 3182370 * 2 ^ 59
def prefixEnd_3182370 : Nat := 4983230072969 + 3 ^ 40 * 3182370 * 2
def baseEnd_3182370 : Nat := 40347788406143683862705

theorem tailTrace_3182370 : CollatzResearch.WordTrace tailWord_3182370 prefixEnd_3182370 40347788406143683862705 := by
  unfold tailWord_3182370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29017642370206117592606141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77380379653882980246949709 29017642370206117592606141)
  ·
    refine ⟨10881615888827294097227303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29017642370206117592606141 10881615888827294097227303)
    ·
      refine ⟨16322423833240941145840955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10881615888827294097227303 16322423833240941145840955)
      ·
        refine ⟨24483635749861411718761433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16322423833240941145840955 24483635749861411718761433)
        ·
          refine ⟨18362726812396058789071075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24483635749861411718761433 18362726812396058789071075)
          ·
            refine ⟨27544090218594088183606613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18362726812396058789071075 27544090218594088183606613)
            ·
              refine ⟨40347788406143683862705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27544090218594088183606613 40347788406143683862705)
              ·
                rfl

theorem cell22_3182370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 11].length) (baseStart_3182370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182370 prefixEnd_3182370 := by exact prefixLift 3182370
  have htrace : WordTrace (prefixWord ++ tailWord_3182370) baseStart_3182370 baseEnd_3182370 := by
    simpa [prefixWord, tailWord_3182370, baseEnd_3182370] using wordTrace_append hprefix tailTrace_3182370
  have hstable : (prefixWord ++ tailWord_3182370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182370).length < 2 ^ (prefixWord ++ tailWord_3182370).sum := by decide
  have hdescent : baseEnd_3182370 < baseStart_3182370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182436 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_3182436 : Nat := 118140960795 + 3182436 * 2 ^ 59
def prefixEnd_3182436 : Nat := 4983230072969 + 3 ^ 40 * 3182436 * 2
def baseEnd_3182436 : Nat := 1089412880114677292142833

theorem tailTrace_3182436 : CollatzResearch.WordTrace tailWord_3182436 prefixEnd_3182436 1089412880114677292142833 := by
  unfold tailWord_3182436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58036488349292681821163581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77381984465723575761551441 58036488349292681821163581)
  ·
    refine ⟨21763683130984755682936343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58036488349292681821163581 21763683130984755682936343)
    ·
      refine ⟨32645524696477133524404515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21763683130984755682936343 32645524696477133524404515)
      ·
        refine ⟨48968287044715700286606773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32645524696477133524404515 48968287044715700286606773)
        ·
          refine ⟨4590776910442096901869385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48968287044715700286606773 4590776910442096901869385)
          ·
            refine ⟨3443082682831572676402039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4590776910442096901869385 3443082682831572676402039)
            ·
              refine ⟨5164624024247359014603059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443082682831572676402039 5164624024247359014603059)
              ·
                refine ⟨7746936036371038521904589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164624024247359014603059 7746936036371038521904589)
                ·
                  refine ⟨2905101013639139445714221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7746936036371038521904589 2905101013639139445714221)
                  ·
                    refine ⟨1089412880114677292142833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2905101013639139445714221 1089412880114677292142833)
                    ·
                      rfl

theorem cell22_3182436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_3182436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182436 prefixEnd_3182436 := by exact prefixLift 3182436
  have htrace : WordTrace (prefixWord ++ tailWord_3182436) baseStart_3182436 baseEnd_3182436 := by
    simpa [prefixWord, tailWord_3182436, baseEnd_3182436] using wordTrace_append hprefix tailTrace_3182436
  have hstable : (prefixWord ++ tailWord_3182436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182436).length < 2 ^ (prefixWord ++ tailWord_3182436).sum := by decide
  have hdescent : baseEnd_3182436 < baseStart_3182436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182505 : List Nat := [1, 2, 1, 1, 1, 1, 4, 11]
def baseStart_3182505 : Nat := 118140960795 + 3182505 * 2 ^ 59
def prefixEnd_3182505 : Nat := 4983230072969 + 3 ^ 40 * 3182505 * 2
def baseEnd_3182505 : Nat := 121048500024976012463069

theorem tailTrace_3182505 : CollatzResearch.WordTrace tailWord_3182505 prefixEnd_3182505 121048500024976012463069 := by
  unfold tailWord_3182505
  simp only [CollatzResearch.WordTrace]
  refine ⟨116075493335335388426588969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77383662223556925617725979 116075493335335388426588969)
  ·
    refine ⟨87056620001501541319941727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116075493335335388426588969 87056620001501541319941727)
    ·
      refine ⟨130584930002252311979912591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87056620001501541319941727 130584930002252311979912591)
      ·
        refine ⟨195877395003378467969868887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130584930002252311979912591 195877395003378467969868887)
        ·
          refine ⟨293816092505067701954803331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195877395003378467969868887 293816092505067701954803331)
          ·
            refine ⟨440724138757601552932204997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293816092505067701954803331 440724138757601552932204997)
            ·
              refine ⟨82635776017050291174788437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 440724138757601552932204997 82635776017050291174788437)
              ·
                refine ⟨121048500024976012463069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 82635776017050291174788437 121048500024976012463069)
                ·
                  rfl

theorem cell22_3182505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 11].length) (baseStart_3182505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182505 prefixEnd_3182505 := by exact prefixLift 3182505
  have htrace : WordTrace (prefixWord ++ tailWord_3182505) baseStart_3182505 baseEnd_3182505 := by
    simpa [prefixWord, tailWord_3182505, baseEnd_3182505] using wordTrace_append hprefix tailTrace_3182505
  have hstable : (prefixWord ++ tailWord_3182505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182505).length < 2 ^ (prefixWord ++ tailWord_3182505).sum := by decide
  have hdescent : baseEnd_3182505 < baseStart_3182505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182573 : List Nat := [1, 5, 1, 4, 1, 2, 2, 6]
def baseStart_3182573 : Nat := 118140960795 + 3182573 * 2 ^ 59
def prefixEnd_3182573 : Nat := 4983230072969 + 3 ^ 40 * 3182573 * 2
def baseEnd_3182573 : Nat := 121051086446050511274157

theorem tailTrace_3182573 : CollatzResearch.WordTrace tailWord_3182573 prefixEnd_3182573 121051086446050511274157 := by
  unfold tailWord_3182573
  simp only [CollatzResearch.WordTrace]
  refine ⟨116077973499089036040064373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77385315666059357360042915 116077973499089036040064373)
  ·
    refine ⟨10882310015539597128756035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116077973499089036040064373 10882310015539597128756035)
    ·
      refine ⟨16323465023309395693134053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10882310015539597128756035 16323465023309395693134053)
      ·
        refine ⟨3060649691870511692462635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16323465023309395693134053 3060649691870511692462635)
        ·
          refine ⟨4590974537805767538693953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060649691870511692462635 4590974537805767538693953)
          ·
            refine ⟨3443230903354325654020465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4590974537805767538693953 3443230903354325654020465)
            ·
              refine ⟨2582423177515744240515349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443230903354325654020465 2582423177515744240515349)
              ·
                refine ⟨121051086446050511274157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2582423177515744240515349 121051086446050511274157)
                ·
                  rfl

theorem cell22_3182573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 6].length) (baseStart_3182573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182573 prefixEnd_3182573 := by exact prefixLift 3182573
  have htrace : WordTrace (prefixWord ++ tailWord_3182573) baseStart_3182573 baseEnd_3182573 := by
    simpa [prefixWord, tailWord_3182573, baseEnd_3182573] using wordTrace_append hprefix tailTrace_3182573
  have hstable : (prefixWord ++ tailWord_3182573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182573).length < 2 ^ (prefixWord ++ tailWord_3182573).sum := by decide
  have hdescent : baseEnd_3182573 < baseStart_3182573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182648 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 1, 4]
def baseStart_3182648 : Nat := 118140960795 + 3182648 * 2 ^ 59
def prefixEnd_3182648 : Nat := 4983230072969 + 3 ^ 40 * 3182648 * 2
def baseEnd_3182648 : Nat := 1089485452047179405842183

theorem tailTrace_3182648 : CollatzResearch.WordTrace tailWord_3182648 prefixEnd_3182648 1089485452047179405842183 := by
  unfold tailWord_3182648
  simp only [CollatzResearch.WordTrace]
  refine ⟨58040354486908661924522299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77387139315878215899363065 58040354486908661924522299)
  ·
    refine ⟨87060531730362992886783449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58040354486908661924522299 87060531730362992886783449)
    ·
      refine ⟨65295398797772244665087587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87060531730362992886783449 65295398797772244665087587)
      ·
        refine ⟨97943098196658366997631381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65295398797772244665087587 97943098196658366997631381)
        ·
          refine ⟨4591082727968360953013971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97943098196658366997631381 4591082727968360953013971)
          ·
            refine ⟨6886624091952541429520957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591082727968360953013971 6886624091952541429520957)
            ·
              refine ⟨2582484034482203036070359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6886624091952541429520957 2582484034482203036070359)
              ·
                refine ⟨3873726051723304554105539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582484034482203036070359 3873726051723304554105539)
                ·
                  refine ⟨5810589077584956831158309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873726051723304554105539 5810589077584956831158309)
                  ·
                    refine ⟨1089485452047179405842183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5810589077584956831158309 1089485452047179405842183)
                    ·
                      rfl

theorem cell22_3182648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_3182648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182648 prefixEnd_3182648 := by exact prefixLift 3182648
  have htrace : WordTrace (prefixWord ++ tailWord_3182648) baseStart_3182648 baseEnd_3182648 := by
    simpa [prefixWord, tailWord_3182648, baseEnd_3182648] using wordTrace_append hprefix tailTrace_3182648
  have hstable : (prefixWord ++ tailWord_3182648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182648).length < 2 ^ (prefixWord ++ tailWord_3182648).sum := by decide
  have hdescent : baseEnd_3182648 < baseStart_3182648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182672 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_3182672 : Nat := 118140960795 + 3182672 * 2 ^ 59
def prefixEnd_3182672 : Nat := 4983230072969 + 3 ^ 40 * 3182672 * 2
def baseEnd_3182672 : Nat := 1089493667737651343242109

theorem tailTrace_3182672 : CollatzResearch.WordTrace tailWord_3182672 prefixEnd_3182672 1089493667737651343242109 := by
  unfold tailWord_3182672
  simp only [CollatzResearch.WordTrace]
  refine ⟨58040792162865187973959135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77387722883820250631945513 58040792162865187973959135)
  ·
    refine ⟨87061188244297781960938703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58040792162865187973959135 87061188244297781960938703)
    ·
      refine ⟨130591782366446672941408055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87061188244297781960938703 130591782366446672941408055)
      ·
        refine ⟨195887673549670009412112083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130591782366446672941408055 195887673549670009412112083)
        ·
          refine ⟨293831510324505014118168125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195887673549670009412112083 293831510324505014118168125)
          ·
            refine ⟨110186816371689380294313047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293831510324505014118168125 110186816371689380294313047)
            ·
              refine ⟨165280224557534070441469571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110186816371689380294313047 165280224557534070441469571)
              ·
                refine ⟨247920336836301105662204357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165280224557534070441469571 247920336836301105662204357)
                ·
                  refine ⟨46485063156806457311663317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247920336836301105662204357 46485063156806457311663317)
                  ·
                    refine ⟨1089493667737651343242109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46485063156806457311663317 1089493667737651343242109)
                    ·
                      rfl

theorem cell22_3182672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_3182672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182672 prefixEnd_3182672 := by exact prefixLift 3182672
  have htrace : WordTrace (prefixWord ++ tailWord_3182672) baseStart_3182672 baseEnd_3182672 := by
    simpa [prefixWord, tailWord_3182672, baseEnd_3182672] using wordTrace_append hprefix tailTrace_3182672
  have hstable : (prefixWord ++ tailWord_3182672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182672).length < 2 ^ (prefixWord ++ tailWord_3182672).sum := by decide
  have hdescent : baseEnd_3182672 < baseStart_3182672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182678 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3182678 : Nat := 118140960795 + 3182678 * 2 ^ 59
def prefixEnd_3182678 : Nat := 4983230072969 + 3 ^ 40 * 3182678 * 2
def baseEnd_3182678 : Nat := 1089495721660269327592091

theorem tailTrace_3182678 : CollatzResearch.WordTrace tailWord_3182678 prefixEnd_3182678 1089495721660269327592091 := by
  unfold tailWord_3182678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7255112697731789935789793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77387868775805759315091125 7255112697731789935789793)
  ·
    refine ⟨5441334523298842451842345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7255112697731789935789793 5441334523298842451842345)
    ·
      refine ⟨4081000892474131838881759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5441334523298842451842345 4081000892474131838881759)
      ·
        refine ⟨6121501338711197758322639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081000892474131838881759 6121501338711197758322639)
        ·
          refine ⟨9182252008066796637483959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121501338711197758322639 9182252008066796637483959)
          ·
            refine ⟨13773378012100194956225939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9182252008066796637483959 13773378012100194956225939)
            ·
              refine ⟨20660067018150292434338909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13773378012100194956225939 20660067018150292434338909)
              ·
                refine ⟨7747525131806359662877091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20660067018150292434338909 7747525131806359662877091)
                ·
                  refine ⟨11621287697709539494315637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7747525131806359662877091 11621287697709539494315637)
                  ·
                    refine ⟨1089495721660269327592091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11621287697709539494315637 1089495721660269327592091)
                    ·
                      rfl

theorem cell22_3182678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3182678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182678 prefixEnd_3182678 := by exact prefixLift 3182678
  have htrace : WordTrace (prefixWord ++ tailWord_3182678) baseStart_3182678 baseEnd_3182678 := by
    simpa [prefixWord, tailWord_3182678, baseEnd_3182678] using wordTrace_append hprefix tailTrace_3182678
  have hstable : (prefixWord ++ tailWord_3182678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182678).length < 2 ^ (prefixWord ++ tailWord_3182678).sum := by decide
  have hdescent : baseEnd_3182678 < baseStart_3182678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182723 : List Nat := [1, 1, 1, 3, 3, 3, 2, 4, 1, 3]
def baseStart_3182723 : Nat := 118140960795 + 3182723 * 2 ^ 59
def prefixEnd_3182723 : Nat := 4983230072969 + 3 ^ 40 * 3182723 * 2
def baseEnd_3182723 : Nat := 1089511126079904210216953

theorem tailTrace_3182723 : CollatzResearch.WordTrace tailWord_3182723 prefixEnd_3182723 1089511126079904210216953 := by
  unfold tailWord_3182723
  simp only [CollatzResearch.WordTrace]
  refine ⟨116083444448545611658024823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77388962965697074438683215 116083444448545611658024823)
  ·
    refine ⟨174125166672818417487037235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116083444448545611658024823 174125166672818417487037235)
    ·
      refine ⟨261187750009227626230555853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174125166672818417487037235 261187750009227626230555853)
      ·
        refine ⟨97945406253460359836458445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261187750009227626230555853 97945406253460359836458445)
        ·
          refine ⟨36729527345047634938671917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97945406253460359836458445 36729527345047634938671917)
          ·
            refine ⟨13773572754392863102001969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36729527345047634938671917 13773572754392863102001969)
            ·
              refine ⟨10330179565794647326501477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13773572754392863102001969 10330179565794647326501477)
              ·
                refine ⟨1936908668586496373719027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10330179565794647326501477 1936908668586496373719027)
                ·
                  refine ⟨2905363002879744560578541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936908668586496373719027 2905363002879744560578541)
                  ·
                    refine ⟨1089511126079904210216953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2905363002879744560578541 1089511126079904210216953)
                    ·
                      rfl

theorem cell22_3182723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 3].length) (baseStart_3182723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182723 prefixEnd_3182723 := by exact prefixLift 3182723
  have htrace : WordTrace (prefixWord ++ tailWord_3182723) baseStart_3182723 baseEnd_3182723 := by
    simpa [prefixWord, tailWord_3182723, baseEnd_3182723] using wordTrace_append hprefix tailTrace_3182723
  have hstable : (prefixWord ++ tailWord_3182723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182723).length < 2 ^ (prefixWord ++ tailWord_3182723).sum := by decide
  have hdescent : baseEnd_3182723 < baseStart_3182723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182736 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 5]
def baseStart_3182736 : Nat := 118140960795 + 3182736 * 2 ^ 59
def prefixEnd_3182736 : Nat := 4983230072969 + 3 ^ 40 * 3182736 * 2
def baseEnd_3182736 : Nat := 363171858748525503213971

theorem tailTrace_3182736 : CollatzResearch.WordTrace tailWord_3182736 prefixEnd_3182736 363171858748525503213971 := by
  unfold tailWord_3182736
  simp only [CollatzResearch.WordTrace]
  refine ⟨58041959298749257439124031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77389279064999009918832041 58041959298749257439124031)
  ·
    refine ⟨87062938948123886158686047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58041959298749257439124031 87062938948123886158686047)
    ·
      refine ⟨130594408422185829238029071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87062938948123886158686047 130594408422185829238029071)
      ·
        refine ⟨195891612633278743857043607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130594408422185829238029071 195891612633278743857043607)
        ·
          refine ⟨293837418949918115785565411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195891612633278743857043607 293837418949918115785565411)
          ·
            refine ⟨440756128424877173678348117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293837418949918115785565411 440756128424877173678348117)
            ·
              refine ⟨2582555439989514689521571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 440756128424877173678348117 2582555439989514689521571)
              ·
                refine ⟨3873833159984272034282357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582555439989514689521571 3873833159984272034282357)
                ·
                  refine ⟨363171858748525503213971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3873833159984272034282357 363171858748525503213971)
                  ·
                    rfl

theorem cell22_3182736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_3182736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182736 prefixEnd_3182736 := by exact prefixLift 3182736
  have htrace : WordTrace (prefixWord ++ tailWord_3182736) baseStart_3182736 baseEnd_3182736 := by
    simpa [prefixWord, tailWord_3182736, baseEnd_3182736] using wordTrace_append hprefix tailTrace_3182736
  have hstable : (prefixWord ++ tailWord_3182736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182736).length < 2 ^ (prefixWord ++ tailWord_3182736).sum := by decide
  have hdescent : baseEnd_3182736 < baseStart_3182736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182742 : List Nat := [5, 3, 2, 1, 1, 1, 1, 8]
def baseStart_3182742 : Nat := 118140960795 + 3182742 * 2 ^ 59
def prefixEnd_3182742 : Nat := 4983230072969 + 3 ^ 40 * 3182742 * 2
def baseEnd_3182742 : Nat := 121057514463132721554655

theorem tailTrace_3182742 : CollatzResearch.WordTrace tailWord_3182742 prefixEnd_3182742 121057514463132721554655 := by
  unfold tailWord_3182742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7255258589717298618935405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77389424956984518601977653 7255258589717298618935405)
  ·
    refine ⟨2720721971143986982100777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7255258589717298618935405 2720721971143986982100777)
    ·
      refine ⟨2040541478357990236575583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2720721971143986982100777 2040541478357990236575583)
      ·
        refine ⟨3060812217536985354863375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040541478357990236575583 3060812217536985354863375)
        ·
          refine ⟨4591218326305478032295063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060812217536985354863375 4591218326305478032295063)
          ·
            refine ⟨6886827489458217048442595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591218326305478032295063 6886827489458217048442595)
            ·
              refine ⟨10330241234187325572663893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886827489458217048442595 10330241234187325572663893)
              ·
                refine ⟨121057514463132721554655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10330241234187325572663893 121057514463132721554655)
                ·
                  rfl

theorem cell22_3182742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_3182742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182742 prefixEnd_3182742 := by exact prefixLift 3182742
  have htrace : WordTrace (prefixWord ++ tailWord_3182742) baseStart_3182742 baseEnd_3182742 := by
    simpa [prefixWord, tailWord_3182742, baseEnd_3182742] using wordTrace_append hprefix tailTrace_3182742
  have hstable : (prefixWord ++ tailWord_3182742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182742).length < 2 ^ (prefixWord ++ tailWord_3182742).sum := by decide
  have hdescent : baseEnd_3182742 < baseStart_3182742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182809 : List Nat := [1, 2, 1, 2, 3, 1, 4, 8]
def baseStart_3182809 : Nat := 118140960795 + 3182809 * 2 ^ 59
def prefixEnd_3182809 : Nat := 4983230072969 + 3 ^ 40 * 3182809 * 2
def baseEnd_3182809 : Nat := 121060062848603183618521

theorem tailTrace_3182809 : CollatzResearch.WordTrace tailWord_3182809 prefixEnd_3182809 121060062848603183618521 := by
  unfold tailWord_3182809
  simp only [CollatzResearch.WordTrace]
  refine ⟨116086581126234048345655481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77391054084156032230436987 116086581126234048345655481)
  ·
    refine ⟨87064935844675536259241611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116086581126234048345655481 87064935844675536259241611)
    ·
      refine ⟨130597403767013304388862417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87064935844675536259241611 130597403767013304388862417)
      ·
        refine ⟨97948052825259978291646813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130597403767013304388862417 97948052825259978291646813)
        ·
          refine ⟨36730519809472491859367555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97948052825259978291646813 36730519809472491859367555)
          ·
            refine ⟨55095779714208737789051333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36730519809472491859367555 55095779714208737789051333)
            ·
              refine ⟨10330458696414138335447125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55095779714208737789051333 10330458696414138335447125)
              ·
                refine ⟨121060062848603183618521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10330458696414138335447125 121060062848603183618521)
                ·
                  rfl

theorem cell22_3182809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 8].length) (baseStart_3182809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182809 prefixEnd_3182809 := by exact prefixLift 3182809
  have htrace : WordTrace (prefixWord ++ tailWord_3182809) baseStart_3182809 baseEnd_3182809 := by
    simpa [prefixWord, tailWord_3182809, baseEnd_3182809] using wordTrace_append hprefix tailTrace_3182809
  have hstable : (prefixWord ++ tailWord_3182809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182809).length < 2 ^ (prefixWord ++ tailWord_3182809).sum := by decide
  have hdescent : baseEnd_3182809 < baseStart_3182809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182813 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3182813 : Nat := 118140960795 + 3182813 * 2 ^ 59
def prefixEnd_3182813 : Nat := 4983230072969 + 3 ^ 40 * 3182813 * 2
def baseEnd_3182813 : Nat := 1089541934919173975466677

theorem tailTrace_3182813 : CollatzResearch.WordTrace tailWord_3182813 prefixEnd_3182813 1089541934919173975466677 := by
  unfold tailWord_3182813
  simp only [CollatzResearch.WordTrace]
  refine ⟨116086727018219557028801093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77391151345479704685867395 116086727018219557028801093)
  ·
    refine ⟨21766261315916166942900205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116086727018219557028801093 21766261315916166942900205)
    ·
      refine ⟨8162347993468562603587577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21766261315916166942900205 8162347993468562603587577)
      ·
        refine ⟨6121760995101421952690683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8162347993468562603587577 6121760995101421952690683)
        ·
          refine ⟨9182641492652132929036025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121760995101421952690683 9182641492652132929036025)
          ·
            refine ⟨6886981119489099696777019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9182641492652132929036025 6886981119489099696777019)
            ·
              refine ⟨10330471679233649545165529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886981119489099696777019 10330471679233649545165529)
              ·
                refine ⟨7747853759425237158874147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10330471679233649545165529 7747853759425237158874147)
                ·
                  refine ⟨11621780639137855738311221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7747853759425237158874147 11621780639137855738311221)
                  ·
                    refine ⟨1089541934919173975466677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11621780639137855738311221 1089541934919173975466677)
                    ·
                      rfl

theorem cell22_3182813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3182813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182813 prefixEnd_3182813 := by exact prefixLift 3182813
  have htrace : WordTrace (prefixWord ++ tailWord_3182813) baseStart_3182813 baseEnd_3182813 := by
    simpa [prefixWord, tailWord_3182813, baseEnd_3182813] using wordTrace_append hprefix tailTrace_3182813
  have hstable : (prefixWord ++ tailWord_3182813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182813).length < 2 ^ (prefixWord ++ tailWord_3182813).sum := by decide
  have hdescent : baseEnd_3182813 < baseStart_3182813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182888 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 7]
def baseStart_3182888 : Nat := 118140960795 + 3182888 * 2 ^ 59
def prefixEnd_3182888 : Nat := 4983230072969 + 3 ^ 40 * 3182888 * 2
def baseEnd_3182888 : Nat := 363189202983966259947149

theorem tailTrace_3182888 : CollatzResearch.WordTrace tailWord_3182888 prefixEnd_3182888 363189202983966259947149 := by
  unfold tailWord_3182888
  simp only [CollatzResearch.WordTrace]
  refine ⟨58044731246473922418890659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77392974995298563225187545 58044731246473922418890659)
  ·
    refine ⟨87067096869710883628335989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58044731246473922418890659 87067096869710883628335989)
    ·
      refine ⟨8162540331535395340156499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87067096869710883628335989 8162540331535395340156499)
      ·
        refine ⟨12243810497303093010234749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8162540331535395340156499 12243810497303093010234749)
        ·
          refine ⟨4591428936488659878838031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12243810497303093010234749 4591428936488659878838031)
          ·
            refine ⟨6887143404732989818257047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591428936488659878838031 6887143404732989818257047)
            ·
              refine ⟨10330715107099484727385571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887143404732989818257047 10330715107099484727385571)
              ·
                refine ⟨15496072660649227091078357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10330715107099484727385571 15496072660649227091078357)
                ·
                  refine ⟨363189202983966259947149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15496072660649227091078357 363189202983966259947149)
                  ·
                    rfl

theorem cell22_3182888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_3182888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182888 prefixEnd_3182888 := by exact prefixLift 3182888
  have htrace : WordTrace (prefixWord ++ tailWord_3182888) baseStart_3182888 baseEnd_3182888 := by
    simpa [prefixWord, tailWord_3182888, baseEnd_3182888] using wordTrace_append hprefix tailTrace_3182888
  have hstable : (prefixWord ++ tailWord_3182888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182888).length < 2 ^ (prefixWord ++ tailWord_3182888).sum := by decide
  have hdescent : baseEnd_3182888 < baseStart_3182888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182905 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 5]
def baseStart_3182905 : Nat := 118140960795 + 3182905 * 2 ^ 59
def prefixEnd_3182905 : Nat := 4983230072969 + 3 ^ 40 * 3182905 * 2
def baseEnd_3182905 : Nat := 363191142799772134055465

theorem tailTrace_3182905 : CollatzResearch.WordTrace tailWord_3182905 prefixEnd_3182905 363191142799772134055465 := by
  unfold tailWord_3182905
  simp only [CollatzResearch.WordTrace]
  refine ⟨116090082533886256741150169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77393388355924171160766779 116090082533886256741150169)
  ·
    refine ⟨87067561900414692555862627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116090082533886256741150169 87067561900414692555862627)
    ·
      refine ⟨130601342850622038833793941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87067561900414692555862627 130601342850622038833793941)
      ·
        refine ⟨6121937946122908070334091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130601342850622038833793941 6121937946122908070334091)
        ·
          refine ⟨9182906919184362105501137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121937946122908070334091 9182906919184362105501137)
          ·
            refine ⟨6887180189388271579125853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9182906919184362105501137 6887180189388271579125853)
            ·
              refine ⟨2582692571020601842172195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6887180189388271579125853 2582692571020601842172195)
              ·
                refine ⟨3874038856530902763258293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582692571020601842172195 3874038856530902763258293)
                ·
                  refine ⟨363191142799772134055465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3874038856530902763258293 363191142799772134055465)
                  ·
                    rfl

theorem cell22_3182905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_3182905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182905 prefixEnd_3182905 := by exact prefixLift 3182905
  have htrace : WordTrace (prefixWord ++ tailWord_3182905) baseStart_3182905 baseEnd_3182905 := by
    simpa [prefixWord, tailWord_3182905, baseEnd_3182905] using wordTrace_append hprefix tailTrace_3182905
  have hstable : (prefixWord ++ tailWord_3182905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182905).length < 2 ^ (prefixWord ++ tailWord_3182905).sum := by decide
  have hdescent : baseEnd_3182905 < baseStart_3182905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182948 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_3182948 : Nat := 118140960795 + 3182948 * 2 ^ 59
def prefixEnd_3182948 : Nat := 4983230072969 + 3 ^ 40 * 3182948 * 2
def baseEnd_3182948 : Nat := 1089588148178078623341263

theorem tailTrace_3182948 : CollatzResearch.WordTrace tailWord_3182948 prefixEnd_3182948 1089588148178078623341263 := by
  unfold tailWord_3182948
  simp only [CollatzResearch.WordTrace]
  refine ⟨58045825436365237542482749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77394433915153650056643665 58045825436365237542482749)
  ·
    refine ⟨21767184538636964078431031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58045825436365237542482749 21767184538636964078431031)
    ·
      refine ⟨32650776807955446117646547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21767184538636964078431031 32650776807955446117646547)
      ·
        refine ⟨48976165211933169176469821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32650776807955446117646547 48976165211933169176469821)
        ·
          refine ⟨18366061954474938441176183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48976165211933169176469821 18366061954474938441176183)
          ·
            refine ⟨27549092931712407661764275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366061954474938441176183 27549092931712407661764275)
            ·
              refine ⟨41323639397568611492646413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27549092931712407661764275 41323639397568611492646413)
              ·
                refine ⟨15496364774088229309742405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41323639397568611492646413 15496364774088229309742405)
                ·
                  refine ⟨2905568395141542995576701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15496364774088229309742405 2905568395141542995576701)
                  ·
                    refine ⟨1089588148178078623341263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2905568395141542995576701 1089588148178078623341263)
                    ·
                      rfl

theorem cell22_3182948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_3182948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3182948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3182948 prefixEnd_3182948 := by exact prefixLift 3182948
  have htrace : WordTrace (prefixWord ++ tailWord_3182948) baseStart_3182948 baseEnd_3182948 := by
    simpa [prefixWord, tailWord_3182948, baseEnd_3182948] using wordTrace_append hprefix tailTrace_3182948
  have hstable : (prefixWord ++ tailWord_3182948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182948).length < 2 ^ (prefixWord ++ tailWord_3182948).sum := by decide
  have hdescent : baseEnd_3182948 < baseStart_3182948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183010 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3183010 : Nat := 118140960795 + 3183010 * 2 ^ 59
def prefixEnd_3183010 : Nat := 4983230072969 + 3 ^ 40 * 3183010 * 2
def baseEnd_3183010 : Nat := 1089609372045131128291073

theorem tailTrace_3183010 : CollatzResearch.WordTrace tailWord_3183010 prefixEnd_3183010 1089609372045131128291073 := by
  unfold tailWord_3183010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023478049626464918430621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77395941465670573115814989 29023478049626464918430621)
  ·
    refine ⟨10883804268609924344411483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29023478049626464918430621 10883804268609924344411483)
    ·
      refine ⟨16325706402914886516617225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10883804268609924344411483 16325706402914886516617225)
      ·
        refine ⟨12244279802186164887462919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16325706402914886516617225 12244279802186164887462919)
        ·
          refine ⟨18366419703279247331194379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244279802186164887462919 18366419703279247331194379)
          ·
            refine ⟨27549629554918870996791569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366419703279247331194379 27549629554918870996791569)
            ·
              refine ⟨20662222166189153247593677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27549629554918870996791569 20662222166189153247593677)
              ·
                refine ⟨7748333312320932467847629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20662222166189153247593677 7748333312320932467847629)
                ·
                  refine ⟨2905624992120349675442861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7748333312320932467847629 2905624992120349675442861)
                  ·
                    refine ⟨1089609372045131128291073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2905624992120349675442861 1089609372045131128291073)
                    ·
                      rfl

theorem cell22_3183010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3183010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183010 prefixEnd_3183010 := by exact prefixLift 3183010
  have htrace : WordTrace (prefixWord ++ tailWord_3183010) baseStart_3183010 baseEnd_3183010 := by
    simpa [prefixWord, tailWord_3183010, baseEnd_3183010] using wordTrace_append hprefix tailTrace_3183010
  have hstable : (prefixWord ++ tailWord_3183010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183010).length < 2 ^ (prefixWord ++ tailWord_3183010).sum := by decide
  have hdescent : baseEnd_3183010 < baseStart_3183010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183051 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 10]
def baseStart_3183051 : Nat := 118140960795 + 3183051 * 2 ^ 59
def prefixEnd_3183051 : Nat := 4983230072969 + 3 ^ 40 * 3183051 * 2
def baseEnd_3183051 : Nat := 363207802394340229338649

theorem tailTrace_3183051 : CollatzResearch.WordTrace tailWord_3183051 prefixEnd_3183051 363207802394340229338649 := by
  unfold tailWord_3183051
  simp only [CollatzResearch.WordTrace]
  refine ⟨116095407591357323675965007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77396938394238215783976671 116095407591357323675965007)
  ·
    refine ⟨174143111387035985513947511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116095407591357323675965007 174143111387035985513947511)
    ·
      refine ⟨261214667080553978270921267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174143111387035985513947511 261214667080553978270921267)
      ·
        refine ⟨391822000620830967406381901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261214667080553978270921267 391822000620830967406381901)
        ·
          refine ⟨146933250232811612777393213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391822000620830967406381901 146933250232811612777393213)
          ·
            refine ⟨55099968837304354791522455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146933250232811612777393213 55099968837304354791522455)
            ·
              refine ⟨82649953255956532187283683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55099968837304354791522455 82649953255956532187283683)
              ·
                refine ⟨123974929883934798280925525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82649953255956532187283683 123974929883934798280925525)
                ·
                  refine ⟨363207802394340229338649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123974929883934798280925525 363207802394340229338649)
                  ·
                    rfl

theorem cell22_3183051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_3183051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183051 prefixEnd_3183051 := by exact prefixLift 3183051
  have htrace : WordTrace (prefixWord ++ tailWord_3183051) baseStart_3183051 baseEnd_3183051 := by
    simpa [prefixWord, tailWord_3183051, baseEnd_3183051] using wordTrace_append hprefix tailTrace_3183051
  have hstable : (prefixWord ++ tailWord_3183051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183051).length < 2 ^ (prefixWord ++ tailWord_3183051).sum := by decide
  have hdescent : baseEnd_3183051 < baseStart_3183051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183085 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 6]
def baseStart_3183085 : Nat := 118140960795 + 3183085 * 2 ^ 59
def prefixEnd_3183085 : Nat := 4983230072969 + 3 ^ 40 * 3183085 * 2
def baseEnd_3183085 : Nat := 363211682025951977555281

theorem tailTrace_3183085 : CollatzResearch.WordTrace tailWord_3183085 prefixEnd_3183085 363211682025951977555281 := by
  unfold tailWord_3183085
  simp only [CollatzResearch.WordTrace]
  refine ⟨116096647673234147482702709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77397765115489431655135139 116096647673234147482702709)
  ·
    refine ⟨10884060719365701326503379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116096647673234147482702709 10884060719365701326503379)
    ·
      refine ⟨16326091079048551989755069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10884060719365701326503379 16326091079048551989755069)
      ·
        refine ⟨6122284154643206996158151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16326091079048551989755069 6122284154643206996158151)
        ·
          refine ⟨9183426231964810494237227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6122284154643206996158151 9183426231964810494237227)
          ·
            refine ⟨13775139347947215741355841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9183426231964810494237227 13775139347947215741355841)
            ·
              refine ⟨10331354510960411806016881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13775139347947215741355841 10331354510960411806016881)
              ·
                refine ⟨7748515883220308854512661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10331354510960411806016881 7748515883220308854512661)
                ·
                  refine ⟨363211682025951977555281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7748515883220308854512661 363211682025951977555281)
                  ·
                    rfl

theorem cell22_3183085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_3183085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183085 prefixEnd_3183085 := by exact prefixLift 3183085
  have htrace : WordTrace (prefixWord ++ tailWord_3183085) baseStart_3183085 baseEnd_3183085 := by
    simpa [prefixWord, tailWord_3183085, baseEnd_3183085] using wordTrace_append hprefix tailTrace_3183085
  have hstable : (prefixWord ++ tailWord_3183085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183085).length < 2 ^ (prefixWord ++ tailWord_3183085).sum := by decide
  have hdescent : baseEnd_3183085 < baseStart_3183085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183115 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 2, 4]
def baseStart_3183115 : Nat := 118140960795 + 3183115 * 2 ^ 59
def prefixEnd_3183115 : Nat := 4983230072969 + 3 ^ 40 * 3183115 * 2
def baseEnd_3183115 : Nat := 1089645315690945854415751

theorem tailTrace_3183115 : CollatzResearch.WordTrace tailWord_3183115 prefixEnd_3183115 1089645315690945854415751 := by
  unfold tailWord_3183115
  simp only [CollatzResearch.WordTrace]
  refine ⟨116097741863125462606294799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77398494575416975070863199 116097741863125462606294799)
  ·
    refine ⟨174146612794688193909442199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116097741863125462606294799 174146612794688193909442199)
    ·
      refine ⟨261219919192032290864163299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174146612794688193909442199 261219919192032290864163299)
      ·
        refine ⟨391829878788048436296244949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261219919192032290864163299 391829878788048436296244949)
        ·
          refine ⟨9183512784094885225693241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 391829878788048436296244949 9183512784094885225693241)
          ·
            refine ⟨6887634588071163919269931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9183512784094885225693241 6887634588071163919269931)
            ·
              refine ⟨10331451882106745878904897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887634588071163919269931 10331451882106745878904897)
              ·
                refine ⟨7748588911580059409178673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10331451882106745878904897 7748588911580059409178673)
                ·
                  refine ⟨5811441683685044556884005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7748588911580059409178673 5811441683685044556884005)
                  ·
                    refine ⟨1089645315690945854415751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5811441683685044556884005 1089645315690945854415751)
                    ·
                      rfl

theorem cell22_3183115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_3183115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183115 prefixEnd_3183115 := by exact prefixLift 3183115
  have htrace : WordTrace (prefixWord ++ tailWord_3183115) baseStart_3183115 baseEnd_3183115 := by
    simpa [prefixWord, tailWord_3183115, baseEnd_3183115] using wordTrace_append hprefix tailTrace_3183115
  have hstable : (prefixWord ++ tailWord_3183115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183115).length < 2 ^ (prefixWord ++ tailWord_3183115).sum := by decide
  have hdescent : baseEnd_3183115 < baseStart_3183115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183175 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 5]
def baseStart_3183175 : Nat := 118140960795 + 3183175 * 2 ^ 59
def prefixEnd_3183175 : Nat := 4983230072969 + 3 ^ 40 * 3183175 * 2
def baseEnd_3183175 : Nat := 363221951639041899305189

theorem tailTrace_3183175 : CollatzResearch.WordTrace tailWord_3183175 prefixEnd_3183175 363221951639041899305189 := by
  unfold tailWord_3183175
  simp only [CollatzResearch.WordTrace]
  refine ⟨116099930242908092853478979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77399953495272061902319319 116099930242908092853478979)
  ·
    refine ⟨174149895364362139280218469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116099930242908092853478979 174149895364362139280218469)
    ·
      refine ⟨32653105380817901115040963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174149895364362139280218469 32653105380817901115040963)
      ·
        refine ⟨48979658071226851672561445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32653105380817901115040963 48979658071226851672561445)
        ·
          refine ⟨9183685888355034688605271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48979658071226851672561445 9183685888355034688605271)
          ·
            refine ⟨13775528832532552032907907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9183685888355034688605271 13775528832532552032907907)
            ·
              refine ⟨20663293248798828049361861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13775528832532552032907907 20663293248798828049361861)
              ·
                refine ⟨3874367484149780259255349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20663293248798828049361861 3874367484149780259255349)
                ·
                  refine ⟨363221951639041899305189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3874367484149780259255349 363221951639041899305189)
                  ·
                    rfl

theorem cell22_3183175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 5].length) (baseStart_3183175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183175 prefixEnd_3183175 := by exact prefixLift 3183175
  have htrace : WordTrace (prefixWord ++ tailWord_3183175) baseStart_3183175 baseEnd_3183175 := by
    simpa [prefixWord, tailWord_3183175, baseEnd_3183175] using wordTrace_append hprefix tailTrace_3183175
  have hstable : (prefixWord ++ tailWord_3183175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183175).length < 2 ^ (prefixWord ++ tailWord_3183175).sum := by decide
  have hdescent : baseEnd_3183175 < baseStart_3183175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183179 : List Nat := [1, 1, 1, 1, 3, 1, 8, 2, 1, 3]
def baseStart_3183179 : Nat := 118140960795 + 3183179 * 2 ^ 59
def prefixEnd_3183179 : Nat := 4983230072969 + 3 ^ 40 * 3183179 * 2
def baseEnd_3183179 : Nat := 1089667224198871020815555

theorem tailTrace_3183179 : CollatzResearch.WordTrace tailWord_3183179 prefixEnd_3183179 1089667224198871020815555 := by
  unfold tailWord_3183179
  simp only [CollatzResearch.WordTrace]
  refine ⟨116100076134893601536624591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77400050756595734357749727 116100076134893601536624591)
  ·
    refine ⟨174150114202340402304936887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116100076134893601536624591 174150114202340402304936887)
    ·
      refine ⟨261225171303510603457405331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174150114202340402304936887 261225171303510603457405331)
      ·
        refine ⟨391837756955265905186107997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261225171303510603457405331 391837756955265905186107997)
        ·
          refine ⟨146939158858224714444790499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391837756955265905186107997 146939158858224714444790499)
          ·
            refine ⟨220408738287337071667185749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146939158858224714444790499 220408738287337071667185749)
            ·
              refine ⟨2582914901804731308599833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 220408738287337071667185749 2582914901804731308599833)
              ·
                refine ⟨1937186176353548481449875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2582914901804731308599833 1937186176353548481449875)
                ·
                  refine ⟨2905779264530322722174813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937186176353548481449875 2905779264530322722174813)
                  ·
                    refine ⟨1089667224198871020815555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2905779264530322722174813 1089667224198871020815555)
                    ·
                      rfl

theorem cell22_3183179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 3].length) (baseStart_3183179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183179 prefixEnd_3183179 := by exact prefixLift 3183179
  have htrace : WordTrace (prefixWord ++ tailWord_3183179) baseStart_3183179 baseEnd_3183179 := by
    simpa [prefixWord, tailWord_3183179, baseEnd_3183179] using wordTrace_append hprefix tailTrace_3183179
  have hstable : (prefixWord ++ tailWord_3183179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183179).length < 2 ^ (prefixWord ++ tailWord_3183179).sum := by decide
  have hdescent : baseEnd_3183179 < baseStart_3183179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183237 : List Nat := [1, 3, 1, 1, 4, 2, 2, 4, 4]
def baseStart_3183237 : Nat := 118140960795 + 3183237 * 2 ^ 59
def prefixEnd_3183237 : Nat := 4983230072969 + 3 ^ 40 * 3183237 * 2
def baseEnd_3183237 : Nat := 363229026261392734288459

theorem tailTrace_3183237 : CollatzResearch.WordTrace tailWord_3183237 prefixEnd_3183237 363229026261392734288459 := by
  unfold tailWord_3183237
  simp only [CollatzResearch.WordTrace]
  refine ⟨116102191568683477442235965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77401461045788984961490643 116102191568683477442235965)
  ·
    refine ⟨43538321838256304040838487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116102191568683477442235965 43538321838256304040838487)
    ·
      refine ⟨65307482757384456061257731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43538321838256304040838487 65307482757384456061257731)
      ·
        refine ⟨97961224136076684091886597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65307482757384456061257731 97961224136076684091886597)
        ·
          refine ⟨18367729525514378267228737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97961224136076684091886597 18367729525514378267228737)
          ·
            refine ⟨13775797144135783700421553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18367729525514378267228737 13775797144135783700421553)
            ·
              refine ⟨10331847858101837775316165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13775797144135783700421553 10331847858101837775316165)
              ·
                refine ⟨1937221473394094582871781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10331847858101837775316165 1937221473394094582871781)
                ·
                  refine ⟨363229026261392734288459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937221473394094582871781 363229026261392734288459)
                  ·
                    rfl

theorem cell22_3183237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_3183237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183237 prefixEnd_3183237 := by exact prefixLift 3183237
  have htrace : WordTrace (prefixWord ++ tailWord_3183237) baseStart_3183237 baseEnd_3183237 := by
    simpa [prefixWord, tailWord_3183237, baseEnd_3183237] using wordTrace_append hprefix tailTrace_3183237
  have hstable : (prefixWord ++ tailWord_3183237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183237).length < 2 ^ (prefixWord ++ tailWord_3183237).sum := by decide
  have hdescent : baseEnd_3183237 < baseStart_3183237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183391 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 1, 4]
def baseStart_3183391 : Nat := 118140960795 + 3183391 * 2 ^ 59
def prefixEnd_3183391 : Nat := 4983230072969 + 3 ^ 40 * 3183391 * 2
def baseEnd_3183391 : Nat := 1089739796131373134514905

theorem tailTrace_3183391 : CollatzResearch.WordTrace tailWord_3183391 prefixEnd_3183391 1089739796131373134514905 := by
  unfold tailWord_3183391
  simp only [CollatzResearch.WordTrace]
  refine ⟨116107808410125561743342027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77405205606750374495561351 116107808410125561743342027)
  ·
    refine ⟨174161712615188342615013041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116107808410125561743342027 174161712615188342615013041)
    ·
      refine ⟨130621284461391256961259781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174161712615188342615013041 130621284461391256961259781)
      ·
        refine ⟨24491490836510860680236209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130621284461391256961259781 24491490836510860680236209)
        ·
          refine ⟨18368618127383145510177157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24491490836510860680236209 18368618127383145510177157)
          ·
            refine ⟨3444115898884339783158217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18368618127383145510177157 3444115898884339783158217)
            ·
              refine ⟨2583086924163254837368663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444115898884339783158217 2583086924163254837368663)
              ·
                refine ⟨3874630386244882256052995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583086924163254837368663 3874630386244882256052995)
                ·
                  refine ⟨5811945579367323384079493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3874630386244882256052995 5811945579367323384079493)
                  ·
                    refine ⟨1089739796131373134514905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5811945579367323384079493 1089739796131373134514905)
                    ·
                      rfl

theorem cell22_3183391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_3183391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183391 prefixEnd_3183391 := by exact prefixLift 3183391
  have htrace : WordTrace (prefixWord ++ tailWord_3183391) baseStart_3183391 baseEnd_3183391 := by
    simpa [prefixWord, tailWord_3183391, baseEnd_3183391] using wordTrace_append hprefix tailTrace_3183391
  have hstable : (prefixWord ++ tailWord_3183391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183391).length < 2 ^ (prefixWord ++ tailWord_3183391).sum := by decide
  have hdescent : baseEnd_3183391 < baseStart_3183391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183406 : List Nat := [4, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_3183406 : Nat := 118140960795 + 3183406 * 2 ^ 59
def prefixEnd_3183406 : Nat := 4983230072969 + 3 ^ 40 * 3183406 * 2
def baseEnd_3183406 : Nat := 363248310312639365129953

theorem tailTrace_3183406 : CollatzResearch.WordTrace tailWord_3183406 prefixEnd_3183406 363248310312639365129953 := by
  unfold tailWord_3183406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14513544438133902413142259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77405570336714146203425381 14513544438133902413142259)
  ·
    refine ⟨21770316657200853619713389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14513544438133902413142259 21770316657200853619713389)
    ·
      refine ⟨8163868746450320107392521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21770316657200853619713389 8163868746450320107392521)
      ·
        refine ⟨6122901559837740080544391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8163868746450320107392521 6122901559837740080544391)
        ·
          refine ⟨9184352339756610120816587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6122901559837740080544391 9184352339756610120816587)
          ·
            refine ⟨13776528509634915181224881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184352339756610120816587 13776528509634915181224881)
            ·
              refine ⟨10332396382226186385918661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13776528509634915181224881 10332396382226186385918661)
              ·
                refine ⟨1937324321667409947359749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10332396382226186385918661 1937324321667409947359749)
                ·
                  refine ⟨363248310312639365129953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937324321667409947359749 363248310312639365129953)
                  ·
                    rfl

theorem cell22_3183406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_3183406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183406 prefixEnd_3183406 := by exact prefixLift 3183406
  have htrace : WordTrace (prefixWord ++ tailWord_3183406) baseStart_3183406 baseEnd_3183406 := by
    simpa [prefixWord, tailWord_3183406, baseEnd_3183406] using wordTrace_append hprefix tailTrace_3183406
  have hstable : (prefixWord ++ tailWord_3183406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183406).length < 2 ^ (prefixWord ++ tailWord_3183406).sum := by decide
  have hdescent : baseEnd_3183406 < baseStart_3183406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183421 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_3183421 : Nat := 118140960795 + 3183421 * 2 ^ 59
def prefixEnd_3183421 : Nat := 4983230072969 + 3 ^ 40 * 3183421 * 2
def baseEnd_3183421 : Nat := 1089750065744463056264813

theorem tailTrace_3183421 : CollatzResearch.WordTrace tailWord_3183421 prefixEnd_3183421 1089750065744463056264813 := by
  unfold tailWord_3183421
  simp only [CollatzResearch.WordTrace]
  refine ⟨116108902600016876866934117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77405935066677917911289411 116108902600016876866934117)
  ·
    refine ⟨21770419237503164412550147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116108902600016876866934117 21770419237503164412550147)
    ·
      refine ⟨32655628856254746618825221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21770419237503164412550147 32655628856254746618825221)
      ·
        refine ⟨6122930410547764991029729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32655628856254746618825221 6122930410547764991029729)
        ·
          refine ⟨4592197807910823743272297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122930410547764991029729 4592197807910823743272297)
          ·
            refine ⟨3444148355933117807454223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4592197807910823743272297 3444148355933117807454223)
            ·
              refine ⟨5166222533899676711181335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444148355933117807454223 5166222533899676711181335)
              ·
                refine ⟨7749333800849515066772003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166222533899676711181335 7749333800849515066772003)
                ·
                  refine ⟨11624000701274272600158005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749333800849515066772003 11624000701274272600158005)
                  ·
                    refine ⟨1089750065744463056264813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11624000701274272600158005 1089750065744463056264813)
                    ·
                      rfl

theorem cell22_3183421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_3183421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183421 prefixEnd_3183421 := by exact prefixLift 3183421
  have htrace : WordTrace (prefixWord ++ tailWord_3183421) baseStart_3183421 baseEnd_3183421 := by
    simpa [prefixWord, tailWord_3183421, baseEnd_3183421] using wordTrace_append hprefix tailTrace_3183421
  have hstable : (prefixWord ++ tailWord_3183421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183421).length < 2 ^ (prefixWord ++ tailWord_3183421).sum := by decide
  have hdescent : baseEnd_3183421 < baseStart_3183421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183560 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 1, 4]
def baseStart_3183560 : Nat := 118140960795 + 3183560 * 2 ^ 59
def prefixEnd_3183560 : Nat := 4983230072969 + 3 ^ 40 * 3183560 * 2
def baseEnd_3183560 : Nat := 1089797648285113027039387

theorem tailTrace_3183560 : CollatzResearch.WordTrace tailWord_3183560 prefixEnd_3183560 1089797648285113027039387 := by
  unfold tailWord_3183560
  simp only [CollatzResearch.WordTrace]
  refine ⟨58056986173256651803122067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77409314897675535737496089 58056986173256651803122067)
  ·
    refine ⟨87085479259884977704683101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58056986173256651803122067 87085479259884977704683101)
    ·
      refine ⟨32657054722456866639256163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87085479259884977704683101 32657054722456866639256163)
      ·
        refine ⟨48985582083685299958884245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32657054722456866639256163 48985582083685299958884245)
        ·
          refine ⟨2296199160172748435572699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48985582083685299958884245 2296199160172748435572699)
          ·
            refine ⟨3444298740259122653359049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296199160172748435572699 3444298740259122653359049)
            ·
              refine ⟨2583224055194341990019287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444298740259122653359049 2583224055194341990019287)
              ·
                refine ⟨3874836082791512985028931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583224055194341990019287 3874836082791512985028931)
                ·
                  refine ⟨5812254124187269477543397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3874836082791512985028931 5812254124187269477543397)
                  ·
                    refine ⟨1089797648285113027039387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812254124187269477543397 1089797648285113027039387)
                    ·
                      rfl

theorem cell22_3183560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_3183560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183560 prefixEnd_3183560 := by exact prefixLift 3183560
  have htrace : WordTrace (prefixWord ++ tailWord_3183560) baseStart_3183560 baseEnd_3183560 := by
    simpa [prefixWord, tailWord_3183560, baseEnd_3183560] using wordTrace_append hprefix tailTrace_3183560
  have hstable : (prefixWord ++ tailWord_3183560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183560).length < 2 ^ (prefixWord ++ tailWord_3183560).sum := by decide
  have hdescent : baseEnd_3183560 < baseStart_3183560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183601 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 3, 3]
def baseStart_3183601 : Nat := 118140960795 + 3183601 * 2 ^ 59
def prefixEnd_3183601 : Nat := 4983230072969 + 3 ^ 40 * 3183601 * 2
def baseEnd_3183601 : Nat := 1089811683423002586764261

theorem tailTrace_3183601 : CollatzResearch.WordTrace tailWord_3183601 prefixEnd_3183601 1089811683423002586764261 := by
  unfold tailWord_3183601
  simp only [CollatzResearch.WordTrace]
  refine ⟨116115467739364767608486657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77410311826243178405657771 116115467739364767608486657)
  ·
    refine ⟨87086600804523575706364993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116115467739364767608486657 87086600804523575706364993)
    ·
      refine ⟨65314950603392681779773745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87086600804523575706364993 65314950603392681779773745)
      ·
        refine ⟨48986212952544511334830309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65314950603392681779773745 48986212952544511334830309)
        ·
          refine ⟨9184914928602095875280683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48986212952544511334830309 9184914928602095875280683)
          ·
            refine ⟨13777372392903143812921025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184914928602095875280683 13777372392903143812921025)
            ·
              refine ⟨10333029294677357859690769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13777372392903143812921025 10333029294677357859690769)
              ·
                refine ⟨7749771971008018394768077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10333029294677357859690769 7749771971008018394768077)
                ·
                  refine ⟨2906164489128006898038029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7749771971008018394768077 2906164489128006898038029)
                  ·
                    refine ⟨1089811683423002586764261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906164489128006898038029 1089811683423002586764261)
                    ·
                      rfl

theorem cell22_3183601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_3183601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183601 prefixEnd_3183601 := by exact prefixLift 3183601
  have htrace : WordTrace (prefixWord ++ tailWord_3183601) baseStart_3183601 baseEnd_3183601 := by
    simpa [prefixWord, tailWord_3183601, baseEnd_3183601] using wordTrace_append hprefix tailTrace_3183601
  have hstable : (prefixWord ++ tailWord_3183601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183601).length < 2 ^ (prefixWord ++ tailWord_3183601).sum := by decide
  have hdescent : baseEnd_3183601 < baseStart_3183601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183648 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 5]
def baseStart_3183648 : Nat := 118140960795 + 3183648 * 2 ^ 59
def prefixEnd_3183648 : Nat := 4983230072969 + 3 ^ 40 * 3183648 * 2
def baseEnd_3183648 : Nat := 363275924161170043613039

theorem tailTrace_3183648 : CollatzResearch.WordTrace tailWord_3183648 prefixEnd_3183648 363275924161170043613039 := by
  unfold tailWord_3183648
  simp only [CollatzResearch.WordTrace]
  refine ⟨58058590985097247317723799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77411454646796329756965065 58058590985097247317723799)
  ·
    refine ⟨87087886477645870976585699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58058590985097247317723799 87087886477645870976585699)
    ·
      refine ⟨130631829716468806464878549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87087886477645870976585699 130631829716468806464878549)
      ·
        refine ⟨3061683508979737651520591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 130631829716468806464878549 3061683508979737651520591)
        ·
          refine ⟨4592525263469606477280887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061683508979737651520591 4592525263469606477280887)
          ·
            refine ⟨6888787895204409715921331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592525263469606477280887 6888787895204409715921331)
            ·
              refine ⟨10333181842806614573881997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888787895204409715921331 10333181842806614573881997)
              ·
                refine ⟨3874943191052480465205749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10333181842806614573881997 3874943191052480465205749)
                ·
                  refine ⟨363275924161170043613039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3874943191052480465205749 363275924161170043613039)
                  ·
                    rfl

theorem cell22_3183648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_3183648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183648 prefixEnd_3183648 := by exact prefixLift 3183648
  have htrace : WordTrace (prefixWord ++ tailWord_3183648) baseStart_3183648 baseEnd_3183648 := by
    simpa [prefixWord, tailWord_3183648, baseEnd_3183648] using wordTrace_append hprefix tailTrace_3183648
  have hstable : (prefixWord ++ tailWord_3183648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183648).length < 2 ^ (prefixWord ++ tailWord_3183648).sum := by decide
  have hdescent : baseEnd_3183648 < baseStart_3183648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183674 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_3183674 : Nat := 118140960795 + 3183674 * 2 ^ 59
def prefixEnd_3183674 : Nat := 4983230072969 + 3 ^ 40 * 3183674 * 2
def baseEnd_3183674 : Nat := 1089836672814854729689037

theorem tailTrace_3183674 : CollatzResearch.WordTrace tailWord_3183674 prefixEnd_3183674 1089836672814854729689037 := by
  unfold tailWord_3183674
  simp only [CollatzResearch.WordTrace]
  refine ⟨29029532567025075268973519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77412086845400200717262717 29029532567025075268973519)
  ·
    refine ⟨43544298850537612903460279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29029532567025075268973519 43544298850537612903460279)
    ·
      refine ⟨65316448275806419355190419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43544298850537612903460279 65316448275806419355190419)
      ·
        refine ⟨97974672413709629032785629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65316448275806419355190419 97974672413709629032785629)
        ·
          refine ⟨36740502155141110887294611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97974672413709629032785629 36740502155141110887294611)
          ·
            refine ⟨55110753232711666330941917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36740502155141110887294611 55110753232711666330941917)
            ·
              refine ⟨20666532462266874874103219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55110753232711666330941917 20666532462266874874103219)
              ·
                refine ⟨30999798693400312311154829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20666532462266874874103219 30999798693400312311154829)
                ·
                  refine ⟨11624924510025117116683061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30999798693400312311154829 11624924510025117116683061)
                  ·
                    refine ⟨1089836672814854729689037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11624924510025117116683061 1089836672814854729689037)
                    ·
                      rfl

theorem cell22_3183674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_3183674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183674 prefixEnd_3183674 := by exact prefixLift 3183674
  have htrace : WordTrace (prefixWord ++ tailWord_3183674) baseStart_3183674 baseEnd_3183674 := by
    simpa [prefixWord, tailWord_3183674, baseEnd_3183674] using wordTrace_append hprefix tailTrace_3183674
  have hstable : (prefixWord ++ tailWord_3183674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183674).length < 2 ^ (prefixWord ++ tailWord_3183674).sum := by decide
  have hdescent : baseEnd_3183674 < baseStart_3183674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183689 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_3183689 : Nat := 118140960795 + 3183689 * 2 ^ 59
def prefixEnd_3183689 : Nat := 4983230072969 + 3 ^ 40 * 3183689 * 2
def baseEnd_3183689 : Nat := 1089841807621399690563991

theorem tailTrace_3183689 : CollatzResearch.WordTrace tailWord_3183689 prefixEnd_3183689 1089841807621399690563991 := by
  unfold tailWord_3183689
  simp only [CollatzResearch.WordTrace]
  refine ⟨116118677363045958637690121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77412451575363972425126747 116118677363045958637690121)
  ·
    refine ⟨87089008022284468978267591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116118677363045958637690121 87089008022284468978267591)
    ·
      refine ⟨130633512033426703467401387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87089008022284468978267591 130633512033426703467401387)
      ·
        refine ⟨195950268050140055201102081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130633512033426703467401387 195950268050140055201102081)
        ·
          refine ⟨146962701037605041400826561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195950268050140055201102081 146962701037605041400826561)
          ·
            refine ⟨110222025778203781050619921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146962701037605041400826561 110222025778203781050619921)
            ·
              refine ⟨82666519333652835787964941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110222025778203781050619921 82666519333652835787964941)
              ·
                refine ⟨30999944750119813420486853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82666519333652835787964941 30999944750119813420486853)
                ·
                  refine ⟨5812489640647465016341285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30999944750119813420486853 5812489640647465016341285)
                  ·
                    refine ⟨1089841807621399690563991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812489640647465016341285 1089841807621399690563991)
                    ·
                      rfl

theorem cell22_3183689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_3183689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183689 prefixEnd_3183689 := by exact prefixLift 3183689
  have htrace : WordTrace (prefixWord ++ tailWord_3183689) baseStart_3183689 baseEnd_3183689 := by
    simpa [prefixWord, tailWord_3183689, baseEnd_3183689] using wordTrace_append hprefix tailTrace_3183689
  have hstable : (prefixWord ++ tailWord_3183689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183689).length < 2 ^ (prefixWord ++ tailWord_3183689).sum := by decide
  have hdescent : baseEnd_3183689 < baseStart_3183689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183708 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3183708 : Nat := 118140960795 + 3183708 * 2 ^ 59
def prefixEnd_3183708 : Nat := 4983230072969 + 3 ^ 40 * 3183708 * 2
def baseEnd_3183708 : Nat := 1089848311709689974338933

theorem tailTrace_3183708 : CollatzResearch.WordTrace tailWord_3183708 prefixEnd_3183708 1089848311709689974338933 := by
  unfold tailWord_3183708
  simp only [CollatzResearch.WordTrace]
  refine ⟨58059685174988562441315889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77412913566651416588421185 58059685174988562441315889)
  ·
    refine ⟨43544763881241421830986917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58059685174988562441315889 43544763881241421830986917)
    ·
      refine ⟨8164643227732766593310047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43544763881241421830986917 8164643227732766593310047)
      ·
        refine ⟨12246964841599149889965071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8164643227732766593310047 12246964841599149889965071)
        ·
          refine ⟨18370447262398724834947607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12246964841599149889965071 18370447262398724834947607)
          ·
            refine ⟨27555670893598087252421411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18370447262398724834947607 27555670893598087252421411)
            ·
              refine ⟨41333506340397130878632117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27555670893598087252421411 41333506340397130878632117)
              ·
                refine ⟨3875016219412231019871761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41333506340397130878632117 3875016219412231019871761)
                ·
                  refine ⟨2906262164559173264903821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875016219412231019871761 2906262164559173264903821)
                  ·
                    refine ⟨1089848311709689974338933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906262164559173264903821 1089848311709689974338933)
                    ·
                      rfl

theorem cell22_3183708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3183708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183708 prefixEnd_3183708 := by exact prefixLift 3183708
  have htrace : WordTrace (prefixWord ++ tailWord_3183708) baseStart_3183708 baseEnd_3183708 := by
    simpa [prefixWord, tailWord_3183708, baseEnd_3183708] using wordTrace_append hprefix tailTrace_3183708
  have hstable : (prefixWord ++ tailWord_3183708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183708).length < 2 ^ (prefixWord ++ tailWord_3183708).sum := by decide
  have hdescent : baseEnd_3183708 < baseStart_3183708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183710 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3183710 : Nat := 118140960795 + 3183710 * 2 ^ 59
def prefixEnd_3183710 : Nat := 4983230072969 + 3 ^ 40 * 3183710 * 2
def baseEnd_3183710 : Nat := 363282998783520878596309

theorem tailTrace_3183710 : CollatzResearch.WordTrace tailWord_3183710 prefixEnd_3183710 363282998783520878596309 := by
  unfold tailWord_3183710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14514930411996234903025573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77412962197313252816136389 14514930411996234903025573)
  ·
    refine ⟨2721549452249294044317295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14514930411996234903025573 2721549452249294044317295)
    ·
      refine ⟨4082324178373941066475943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721549452249294044317295 4082324178373941066475943)
      ·
        refine ⟨6123486267560911599713915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082324178373941066475943 6123486267560911599713915)
        ·
          refine ⟨9185229401341367399570873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123486267560911599713915 9185229401341367399570873)
          ·
            refine ⟨6888922051006025549678155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9185229401341367399570873 6888922051006025549678155)
            ·
              refine ⟨10333383076509038324517233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888922051006025549678155 10333383076509038324517233)
              ·
                refine ⟨7750037307381778743387925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10333383076509038324517233 7750037307381778743387925)
                ·
                  refine ⟨363282998783520878596309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7750037307381778743387925 363282998783520878596309)
                  ·
                    rfl

theorem cell22_3183710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3183710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183710 prefixEnd_3183710 := by exact prefixLift 3183710
  have htrace : WordTrace (prefixWord ++ tailWord_3183710) baseStart_3183710 baseEnd_3183710 := by
    simpa [prefixWord, tailWord_3183710, baseEnd_3183710] using wordTrace_append hprefix tailTrace_3183710
  have hstable : (prefixWord ++ tailWord_3183710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183710).length < 2 ^ (prefixWord ++ tailWord_3183710).sum := by decide
  have hdescent : baseEnd_3183710 < baseStart_3183710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183721 : List Nat := [1, 2, 1, 1, 1, 7, 3, 6]
def baseStart_3183721 : Nat := 118140960795 + 3183721 * 2 ^ 59
def prefixEnd_3183721 : Nat := 4983230072969 + 3 ^ 40 * 3183721 * 2
def baseEnd_3183721 : Nat := 121094751319484697084877

theorem tailTrace_3183721 : CollatzResearch.WordTrace tailWord_3183721 prefixEnd_3183721 121094751319484697084877 := by
  unfold tailWord_3183721
  simp only [CollatzResearch.WordTrace]
  refine ⟨116119844498930028102855017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77413229665953352068570011 116119844498930028102855017)
  ·
    refine ⟨87089883374197521077141263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116119844498930028102855017 87089883374197521077141263)
    ·
      refine ⟨130634825061296281615711895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87089883374197521077141263 130634825061296281615711895)
      ·
        refine ⟨195952237591944422423567843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130634825061296281615711895 195952237591944422423567843)
        ·
          refine ⟨293928356387916633635351765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195952237591944422423567843 293928356387916633635351765)
          ·
            refine ⟨6888945852841796100828557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 293928356387916633635351765 6888945852841796100828557)
            ·
              refine ⟨2583354694815673537810709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6888945852841796100828557 2583354694815673537810709)
              ·
                refine ⟨121094751319484697084877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2583354694815673537810709 121094751319484697084877)
                ·
                  rfl

theorem cell22_3183721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 6].length) (baseStart_3183721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183721 prefixEnd_3183721 := by exact prefixLift 3183721
  have htrace : WordTrace (prefixWord ++ tailWord_3183721) baseStart_3183721 baseEnd_3183721 := by
    simpa [prefixWord, tailWord_3183721, baseEnd_3183721] using wordTrace_append hprefix tailTrace_3183721
  have hstable : (prefixWord ++ tailWord_3183721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183721).length < 2 ^ (prefixWord ++ tailWord_3183721).sum := by decide
  have hdescent : baseEnd_3183721 < baseStart_3183721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183753 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 3, 3]
def baseStart_3183753 : Nat := 118140960795 + 3183753 * 2 ^ 59
def prefixEnd_3183753 : Nat := 4983230072969 + 3 ^ 40 * 3183753 * 2
def baseEnd_3183753 : Nat := 1089863716129324856963795

theorem tailTrace_3183753 : CollatzResearch.WordTrace tailWord_3183753 prefixEnd_3183753 1089863716129324856963795 := by
  unfold tailWord_3183753
  simp only [CollatzResearch.WordTrace]
  refine ⟨116121011634814097568019913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77414007756542731712013275 116121011634814097568019913)
  ·
    refine ⟨87090758726110573176014935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116121011634814097568019913 87090758726110573176014935)
    ·
      refine ⟨130636138089165859764022403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87090758726110573176014935 130636138089165859764022403)
      ·
        refine ⟨195954207133748789646033605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130636138089165859764022403 195954207133748789646033605)
        ·
          refine ⟨36741413837577898058631301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195954207133748789646033605 36741413837577898058631301)
          ·
            refine ⟨6889015094545855885993369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36741413837577898058631301 6889015094545855885993369)
            ·
              refine ⟨5166761320909391914495027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6889015094545855885993369 5166761320909391914495027)
              ·
                refine ⟨7750141981364087871742541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166761320909391914495027 7750141981364087871742541)
                ·
                  refine ⟨2906303243011532951903453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7750141981364087871742541 2906303243011532951903453)
                  ·
                    refine ⟨1089863716129324856963795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906303243011532951903453 1089863716129324856963795)
                    ·
                      rfl

theorem cell22_3183753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_3183753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183753 prefixEnd_3183753 := by exact prefixLift 3183753
  have htrace : WordTrace (prefixWord ++ tailWord_3183753) baseStart_3183753 baseEnd_3183753 := by
    simpa [prefixWord, tailWord_3183753, baseEnd_3183753] using wordTrace_append hprefix tailTrace_3183753
  have hstable : (prefixWord ++ tailWord_3183753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183753).length < 2 ^ (prefixWord ++ tailWord_3183753).sum := by decide
  have hdescent : baseEnd_3183753 < baseStart_3183753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183779 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 8]
def baseStart_3183779 : Nat := 118140960795 + 3183779 * 2 ^ 59
def prefixEnd_3183779 : Nat := 4983230072969 + 3 ^ 40 * 3183779 * 2
def baseEnd_3183779 : Nat := 1089872616460669455813715

theorem tailTrace_3183779 : CollatzResearch.WordTrace tailWord_3183779 prefixEnd_3183779 1089872616460669455813715 := by
  unfold tailWord_3183779
  simp only [CollatzResearch.WordTrace]
  refine ⟨116121959932719904008466391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77414639955146602672310927 116121959932719904008466391)
  ·
    refine ⟨174182939899079856012699587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116121959932719904008466391 174182939899079856012699587)
    ·
      refine ⟨261274409848619784019049381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174182939899079856012699587 261274409848619784019049381)
      ·
        refine ⟨48988951846616209503571759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261274409848619784019049381 48988951846616209503571759)
        ·
          refine ⟨73483427769924314255357639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48988951846616209503571759 73483427769924314255357639)
          ·
            refine ⟨110225141654886471383036459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73483427769924314255357639 110225141654886471383036459)
            ·
              refine ⟨165337712482329707074554689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110225141654886471383036459 165337712482329707074554689)
              ·
                refine ⟨124003284361747280305916017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165337712482329707074554689 124003284361747280305916017)
                ·
                  refine ⟨93002463271310460229437013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124003284361747280305916017 93002463271310460229437013)
                  ·
                    refine ⟨1089872616460669455813715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93002463271310460229437013 1089872616460669455813715)
                    ·
                      rfl

theorem cell22_3183779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_3183779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183779 prefixEnd_3183779 := by exact prefixLift 3183779
  have htrace : WordTrace (prefixWord ++ tailWord_3183779) baseStart_3183779 baseEnd_3183779 := by
    simpa [prefixWord, tailWord_3183779, baseEnd_3183779] using wordTrace_append hprefix tailTrace_3183779
  have hstable : (prefixWord ++ tailWord_3183779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183779).length < 2 ^ (prefixWord ++ tailWord_3183779).sum := by decide
  have hdescent : baseEnd_3183779 < baseStart_3183779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183847 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3183847 : Nat := 118140960795 + 3183847 * 2 ^ 59
def prefixEnd_3183847 : Nat := 4983230072969 + 3 ^ 40 * 3183847 * 2
def baseEnd_3183847 : Nat := 1089895894250339945113507

theorem tailTrace_3183847 : CollatzResearch.WordTrace tailWord_3183847 prefixEnd_3183847 1089895894250339945113507 := by
  unfold tailWord_3183847
  simp only [CollatzResearch.WordTrace]
  refine ⟨116124440096473551621941795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77416293397649034414627863 116124440096473551621941795)
  ·
    refine ⟨174186660144710327432912693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116124440096473551621941795 174186660144710327432912693)
    ·
      refine ⟨16329999388566593196835565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174186660144710327432912693 16329999388566593196835565)
      ·
        refine ⟨6123749770712472448813337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16329999388566593196835565 6123749770712472448813337)
        ·
          refine ⟨4592812328034354336610003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6123749770712472448813337 4592812328034354336610003)
          ·
            refine ⟨6889218492051531504915005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592812328034354336610003 6889218492051531504915005)
            ·
              refine ⟨2583456934519324314343127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6889218492051531504915005 2583456934519324314343127)
              ·
                refine ⟨3875185401778986471514691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583456934519324314343127 3875185401778986471514691)
                ·
                  refine ⟨5812778102668479707272037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875185401778986471514691 5812778102668479707272037)
                  ·
                    refine ⟨1089895894250339945113507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5812778102668479707272037 1089895894250339945113507)
                    ·
                      rfl

theorem cell22_3183847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3183847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183847 prefixEnd_3183847 := by exact prefixLift 3183847
  have htrace : WordTrace (prefixWord ++ tailWord_3183847) baseStart_3183847 baseEnd_3183847 := by
    simpa [prefixWord, tailWord_3183847, baseEnd_3183847] using wordTrace_append hprefix tailTrace_3183847
  have hstable : (prefixWord ++ tailWord_3183847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183847).length < 2 ^ (prefixWord ++ tailWord_3183847).sum := by decide
  have hdescent : baseEnd_3183847 < baseStart_3183847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183873 : List Nat := [1, 2, 4, 1, 1, 5, 1, 7]
def baseStart_3183873 : Nat := 118140960795 + 3183873 * 2 ^ 59
def prefixEnd_3183873 : Nat := 4983230072969 + 3 ^ 40 * 3183873 * 2
def baseEnd_3183873 : Nat := 121100532731298282662603

theorem tailTrace_3183873 : CollatzResearch.WordTrace tailWord_3183873 prefixEnd_3183873 121100532731298282662603 := by
  unfold tailWord_3183873
  simp only [CollatzResearch.WordTrace]
  refine ⟨116125388394379358062388273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77416925596252905374925515 116125388394379358062388273)
  ·
    refine ⟨87094041295784518546791205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116125388394379358062388273 87094041295784518546791205)
    ·
      refine ⟨16330132742959597227523351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87094041295784518546791205 16330132742959597227523351)
      ·
        refine ⟨24495199114439395841285027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16330132742959597227523351 24495199114439395841285027)
        ·
          refine ⟨36742798671659093761927541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24495199114439395841285027 36742798671659093761927541)
          ·
            refine ⟨3444637375468040040180707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36742798671659093761927541 3444637375468040040180707)
            ·
              refine ⟨5166956063202060060271061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444637375468040040180707 5166956063202060060271061)
              ·
                refine ⟨121100532731298282662603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5166956063202060060271061 121100532731298282662603)
                ·
                  rfl

theorem cell22_3183873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 7].length) (baseStart_3183873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183873 prefixEnd_3183873 := by exact prefixLift 3183873
  have htrace : WordTrace (prefixWord ++ tailWord_3183873) baseStart_3183873 baseEnd_3183873 := by
    simpa [prefixWord, tailWord_3183873, baseEnd_3183873] using wordTrace_append hprefix tailTrace_3183873
  have hstable : (prefixWord ++ tailWord_3183873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183873).length < 2 ^ (prefixWord ++ tailWord_3183873).sum := by decide
  have hdescent : baseEnd_3183873 < baseStart_3183873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183922 : List Nat := [3, 2, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_3183922 : Nat := 118140960795 + 3183922 * 2 ^ 59
def prefixEnd_3183922 : Nat := 4983230072969 + 3 ^ 40 * 3183922 * 2
def baseEnd_3183922 : Nat := 1089921568283064749488277

theorem tailTrace_3183922 : CollatzResearch.WordTrace tailWord_3183922 prefixEnd_3183922 1089921568283064749488277 := by
  unfold tailWord_3183922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29031793892800459857730505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77418117047467892953948013 29031793892800459857730505)
  ·
    refine ⟨21773845419600344893297879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29031793892800459857730505 21773845419600344893297879)
    ·
      refine ⟨32660768129400517339946819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21773845419600344893297879 32660768129400517339946819)
      ·
        refine ⟨48991152194100776009920229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32660768129400517339946819 48991152194100776009920229)
        ·
          refine ⟨9185841036393895501860043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48991152194100776009920229 9185841036393895501860043)
          ·
            refine ⟨13778761554590843252790065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9185841036393895501860043 13778761554590843252790065)
            ·
              refine ⟨10334071165943132439592549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13778761554590843252790065 10334071165943132439592549)
              ·
                refine ⟨1937638343614337332423603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10334071165943132439592549 1937638343614337332423603)
                ·
                  refine ⟨2906457515421505998635405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937638343614337332423603 2906457515421505998635405)
                  ·
                    refine ⟨1089921568283064749488277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906457515421505998635405 1089921568283064749488277)
                    ·
                      rfl

theorem cell22_3183922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_3183922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183922 prefixEnd_3183922 := by exact prefixLift 3183922
  have htrace : WordTrace (prefixWord ++ tailWord_3183922) baseStart_3183922 baseEnd_3183922 := by
    simpa [prefixWord, tailWord_3183922, baseEnd_3183922] using wordTrace_append hprefix tailTrace_3183922
  have hstable : (prefixWord ++ tailWord_3183922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183922).length < 2 ^ (prefixWord ++ tailWord_3183922).sum := by decide
  have hdescent : baseEnd_3183922 < baseStart_3183922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183935 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 5]
def baseStart_3183935 : Nat := 118140960795 + 3183935 * 2 ^ 59
def prefixEnd_3183935 : Nat := 4983230072969 + 3 ^ 40 * 3183935 * 2
def baseEnd_3183935 : Nat := 363308672816245682971079

theorem tailTrace_3183935 : CollatzResearch.WordTrace tailWord_3183935 prefixEnd_3183935 363308672816245682971079 := by
  unfold tailWord_3183935
  simp only [CollatzResearch.WordTrace]
  refine ⟨116127649720154742651145259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77418433146769828434096839 116127649720154742651145259)
  ·
    refine ⟨174191474580232113976717889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116127649720154742651145259 174191474580232113976717889)
    ·
      refine ⟨130643605935174085482538417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174191474580232113976717889 130643605935174085482538417)
      ·
        refine ⟨97982704451380564111903813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130643605935174085482538417 97982704451380564111903813)
        ·
          refine ⟨18371757084633855770981965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97982704451380564111903813 18371757084633855770981965)
          ·
            refine ⟨6889408906737695914118237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18371757084633855770981965 6889408906737695914118237)
            ·
              refine ⟨2583528340026635967794339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6889408906737695914118237 2583528340026635967794339)
              ·
                refine ⟨3875292510039953951691509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583528340026635967794339 3875292510039953951691509)
                ·
                  refine ⟨363308672816245682971079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3875292510039953951691509 363308672816245682971079)
                  ·
                    rfl

theorem cell22_3183935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 5].length) (baseStart_3183935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183935 prefixEnd_3183935 := by exact prefixLift 3183935
  have htrace : WordTrace (prefixWord ++ tailWord_3183935) baseStart_3183935 baseEnd_3183935 := by
    simpa [prefixWord, tailWord_3183935, baseEnd_3183935] using wordTrace_append hprefix tailTrace_3183935
  have hstable : (prefixWord ++ tailWord_3183935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183935).length < 2 ^ (prefixWord ++ tailWord_3183935).sum := by decide
  have hdescent : baseEnd_3183935 < baseStart_3183935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183980 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 6]
def baseStart_3183980 : Nat := 118140960795 + 3183980 * 2 ^ 59
def prefixEnd_3183980 : Nat := 4983230072969 + 3 ^ 40 * 3183980 * 2
def baseEnd_3183980 : Nat := 363313807622790643846033

theorem tailTrace_3183980 : CollatzResearch.WordTrace tailWord_3183980 prefixEnd_3183980 363313807622790643846033 := by
  unfold tailWord_3183980
  simp only [CollatzResearch.WordTrace]
  refine ⟨58064645502495857668266697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77419527336661143557688929 58064645502495857668266697)
  ·
    refine ⟨43548484126871893251200023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58064645502495857668266697 43548484126871893251200023)
    ·
      refine ⟨65322726190307839876800035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43548484126871893251200023 65322726190307839876800035)
      ·
        refine ⟨97984089285461759815200053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65322726190307839876800035 97984089285461759815200053)
        ·
          refine ⟨9186008370512039982675005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97984089285461759815200053 9186008370512039982675005)
          ·
            refine ⟨3444753138942014993503127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9186008370512039982675005 3444753138942014993503127)
            ·
              refine ⟨5167129708413022490254691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444753138942014993503127 5167129708413022490254691)
              ·
                refine ⟨7750694562619533735382037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167129708413022490254691 7750694562619533735382037)
                ·
                  refine ⟨363313807622790643846033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7750694562619533735382037 363313807622790643846033)
                  ·
                    rfl

theorem cell22_3183980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_3183980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183980 prefixEnd_3183980 := by exact prefixLift 3183980
  have htrace : WordTrace (prefixWord ++ tailWord_3183980) baseStart_3183980 baseEnd_3183980 := by
    simpa [prefixWord, tailWord_3183980, baseEnd_3183980] using wordTrace_append hprefix tailTrace_3183980
  have hstable : (prefixWord ++ tailWord_3183980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183980).length < 2 ^ (prefixWord ++ tailWord_3183980).sum := by decide
  have hdescent : baseEnd_3183980 < baseStart_3183980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183995 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 2, 3]
def baseStart_3183995 : Nat := 118140960795 + 3183995 * 2 ^ 59
def prefixEnd_3183995 : Nat := 4983230072969 + 3 ^ 40 * 3183995 * 2
def baseEnd_3183995 : Nat := 1089946557674916892413053

theorem tailTrace_3183995 : CollatzResearch.WordTrace tailWord_3183995 prefixEnd_3183995 1089946557674916892413053 := by
  unfold tailWord_3183995
  simp only [CollatzResearch.WordTrace]
  refine ⟨116129838099937372898329439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77419892066624915265552959 116129838099937372898329439)
  ·
    refine ⟨174194757149906059347494159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116129838099937372898329439 174194757149906059347494159)
    ·
      refine ⟨261292135724859089021241239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174194757149906059347494159 261292135724859089021241239)
      ·
        refine ⟨391938203587288633531861859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261292135724859089021241239 391938203587288633531861859)
        ·
          refine ⟨587907305380932950297792789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391938203587288633531861859 587907305380932950297792789)
          ·
            refine ⟨27558154939731232045209037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 587907305380932950297792789 27558154939731232045209037)
            ·
              refine ⟨10334308102399212016953389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27558154939731232045209037 10334308102399212016953389)
              ·
                refine ⟨3875365538399704506357521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10334308102399212016953389 3875365538399704506357521)
                ·
                  refine ⟨2906524153799778379768141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875365538399704506357521 2906524153799778379768141)
                  ·
                    refine ⟨1089946557674916892413053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906524153799778379768141 1089946557674916892413053)
                    ·
                      rfl

theorem cell22_3183995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 3].length) (baseStart_3183995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3183995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3183995 prefixEnd_3183995 := by exact prefixLift 3183995
  have htrace : WordTrace (prefixWord ++ tailWord_3183995) baseStart_3183995 baseEnd_3183995 := by
    simpa [prefixWord, tailWord_3183995, baseEnd_3183995] using wordTrace_append hprefix tailTrace_3183995
  have hstable : (prefixWord ++ tailWord_3183995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183995).length < 2 ^ (prefixWord ++ tailWord_3183995).sum := by decide
  have hdescent : baseEnd_3183995 < baseStart_3183995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184008 : List Nat := [2, 1, 3, 3, 1, 2, 2, 8]
def baseStart_3184008 : Nat := 118140960795 + 3184008 * 2 ^ 59
def prefixEnd_3184008 : Nat := 4983230072969 + 3 ^ 40 * 3184008 * 2
def baseEnd_3184008 : Nat := 121105667537843243537557

theorem tailTrace_3184008 : CollatzResearch.WordTrace tailWord_3184008 prefixEnd_3184008 121105667537843243537557 := by
  unfold tailWord_3184008
  simp only [CollatzResearch.WordTrace]
  refine ⟨58065156124445138059276339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77420208165926850745701785 58065156124445138059276339)
  ·
    refine ⟨87097734186667707088914509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58065156124445138059276339 87097734186667707088914509)
    ·
      refine ⟨32661650320000390158342941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87097734186667707088914509 32661650320000390158342941)
      ·
        refine ⟨12248118870000146309378603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32661650320000390158342941 12248118870000146309378603)
        ·
          refine ⟨18372178305000219464067905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12248118870000146309378603 18372178305000219464067905)
          ·
            refine ⟨13779133728750164598050929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18372178305000219464067905 13779133728750164598050929)
            ·
              refine ⟨10334350296562623448538197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13779133728750164598050929 10334350296562623448538197)
              ·
                refine ⟨121105667537843243537557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10334350296562623448538197 121105667537843243537557)
                ·
                  rfl

theorem cell22_3184008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_3184008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184008 prefixEnd_3184008 := by exact prefixLift 3184008
  have htrace : WordTrace (prefixWord ++ tailWord_3184008) baseStart_3184008 baseEnd_3184008 := by
    simpa [prefixWord, tailWord_3184008, baseEnd_3184008] using wordTrace_append hprefix tailTrace_3184008
  have hstable : (prefixWord ++ tailWord_3184008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184008).length < 2 ^ (prefixWord ++ tailWord_3184008).sum := by decide
  have hdescent : baseEnd_3184008 < baseStart_3184008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184057 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 3, 3]
def baseStart_3184057 : Nat := 118140960795 + 3184057 * 2 ^ 59
def prefixEnd_3184057 : Nat := 4983230072969 + 3 ^ 40 * 3184057 * 2
def baseEnd_3184057 : Nat := 1089967781541969397362863

theorem tailTrace_3184057 : CollatzResearch.WordTrace tailWord_3184057 prefixEnd_3184057 1089967781541969397362863 := by
  unfold tailWord_3184057
  simp only [CollatzResearch.WordTrace]
  refine ⟨116132099425712757487086425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77421399617141838324724283 116132099425712757487086425)
  ·
    refine ⟨87099074569284568115314819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116132099425712757487086425 87099074569284568115314819)
    ·
      refine ⟨130648611853926852172972229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87099074569284568115314819 130648611853926852172972229)
      ·
        refine ⟨24496614722611284782432293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130648611853926852172972229 24496614722611284782432293)
        ·
          refine ⟨4593115260489615896706055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24496614722611284782432293 4593115260489615896706055)
          ·
            refine ⟨6889672890734423845059083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593115260489615896706055 6889672890734423845059083)
            ·
              refine ⟨10334509336101635767588625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889672890734423845059083 10334509336101635767588625)
              ·
                refine ⟨7750882002076226825691469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10334509336101635767588625 7750882002076226825691469)
                ·
                  refine ⟨2906580750778585059634301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7750882002076226825691469 2906580750778585059634301)
                  ·
                    refine ⟨1089967781541969397362863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906580750778585059634301 1089967781541969397362863)
                    ·
                      rfl

theorem cell22_3184057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_3184057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184057 prefixEnd_3184057 := by exact prefixLift 3184057
  have htrace : WordTrace (prefixWord ++ tailWord_3184057) baseStart_3184057 baseEnd_3184057 := by
    simpa [prefixWord, tailWord_3184057, baseEnd_3184057] using wordTrace_append hprefix tailTrace_3184057
  have hstable : (prefixWord ++ tailWord_3184057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184057).length < 2 ^ (prefixWord ++ tailWord_3184057).sum := by decide
  have hdescent : baseEnd_3184057 < baseStart_3184057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184074 : List Nat := [3, 1, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_3184074 : Nat := 118140960795 + 3184074 * 2 ^ 59
def prefixEnd_3184074 : Nat := 4983230072969 + 3 ^ 40 * 3184074 * 2
def baseEnd_3184074 : Nat := 1089973600989387019687811

theorem tailTrace_3184074 : CollatzResearch.WordTrace tailWord_3184074 prefixEnd_3184074 1089973600989387019687811 := by
  unfold tailWord_3184074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29033179866662792347613819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77421812977767446260303517 29033179866662792347613819)
  ·
    refine ⟨43549769799994188521420729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29033179866662792347613819 43549769799994188521420729)
    ·
      refine ⟨32662327349995641391065547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43549769799994188521420729 32662327349995641391065547)
      ·
        refine ⟨48993491024993462086598321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32662327349995641391065547 48993491024993462086598321)
        ·
          refine ⟨36745118268745096564948741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48993491024993462086598321 36745118268745096564948741)
          ·
            refine ⟨6889709675389705605927889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36745118268745096564948741 6889709675389705605927889)
            ·
              refine ⟨5167282256542279204445917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6889709675389705605927889 5167282256542279204445917)
              ·
                refine ⟨1937730846203354701667219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5167282256542279204445917 1937730846203354701667219)
                ·
                  refine ⟨2906596269305032052500829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937730846203354701667219 2906596269305032052500829)
                  ·
                    refine ⟨1089973600989387019687811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906596269305032052500829 1089973600989387019687811)
                    ·
                      rfl

theorem cell22_3184074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_3184074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184074 prefixEnd_3184074 := by exact prefixLift 3184074
  have htrace : WordTrace (prefixWord ++ tailWord_3184074) baseStart_3184074 baseEnd_3184074 := by
    simpa [prefixWord, tailWord_3184074, baseEnd_3184074] using wordTrace_append hprefix tailTrace_3184074
  have hstable : (prefixWord ++ tailWord_3184074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184074).length < 2 ^ (prefixWord ++ tailWord_3184074).sum := by decide
  have hdescent : baseEnd_3184074 < baseStart_3184074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184145 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3184145 : Nat := 118140960795 + 3184145 * 2 ^ 59
def prefixEnd_3184145 : Nat := 4983230072969 + 3 ^ 40 * 3184145 * 2
def baseEnd_3184145 : Nat := 1089997905740366501162593

theorem tailTrace_3184145 : CollatzResearch.WordTrace tailWord_3184145 prefixEnd_3184145 1089997905740366501162593 := by
  unfold tailWord_3184145
  simp only [CollatzResearch.WordTrace]
  refine ⟨116135309049393948516289889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77423539366262632344193259 116135309049393948516289889)
  ·
    refine ⟨87101481787045461387217417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116135309049393948516289889 87101481787045461387217417)
    ·
      refine ⟨65326111340284096040413063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87101481787045461387217417 65326111340284096040413063)
      ·
        refine ⟨97989167010426144060619595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65326111340284096040413063 97989167010426144060619595)
        ·
          refine ⟨146983750515639216090929393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97989167010426144060619595 146983750515639216090929393)
          ·
            refine ⟨110237812886729412068197045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146983750515639216090929393 110237812886729412068197045)
            ·
              refine ⟨10334794958130882381393473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110237812886729412068197045 10334794958130882381393473)
              ·
                refine ⟨7751096218598161786045105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10334794958130882381393473 7751096218598161786045105)
                ·
                  refine ⟨5813322163948621339533829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7751096218598161786045105 5813322163948621339533829)
                  ·
                    refine ⟨1089997905740366501162593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5813322163948621339533829 1089997905740366501162593)
                    ·
                      rfl

theorem cell22_3184145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3184145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184145 prefixEnd_3184145 := by exact prefixLift 3184145
  have htrace : WordTrace (prefixWord ++ tailWord_3184145) baseStart_3184145 baseEnd_3184145 := by
    simpa [prefixWord, tailWord_3184145, baseEnd_3184145] using wordTrace_append hprefix tailTrace_3184145
  have hstable : (prefixWord ++ tailWord_3184145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184145).length < 2 ^ (prefixWord ++ tailWord_3184145).sum := by decide
  have hdescent : baseEnd_3184145 < baseStart_3184145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184149 : List Nat := [1, 3, 2, 1, 3, 3, 3, 2, 4]
def baseStart_3184149 : Nat := 118140960795 + 3184149 * 2 ^ 59
def prefixEnd_3184149 : Nat := 4983230072969 + 3 ^ 40 * 3184149 * 2
def baseEnd_3184149 : Nat := 363333091674037274687527

theorem tailTrace_3184149 : CollatzResearch.WordTrace tailWord_3184149 prefixEnd_3184149 363333091674037274687527 := by
  unfold tailWord_3184149
  simp only [CollatzResearch.WordTrace]
  refine ⟨116135454941379457199435501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77423636627586304799623667 116135454941379457199435501)
  ·
    refine ⟨43550795603017296449788313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116135454941379457199435501 43550795603017296449788313)
    ·
      refine ⟨32663096702262972337341235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43550795603017296449788313 32663096702262972337341235)
      ·
        refine ⟨48994645053394458506011853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32663096702262972337341235 48994645053394458506011853)
        ·
          refine ⟨18372991895022921939754445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48994645053394458506011853 18372991895022921939754445)
          ·
            refine ⟨6889871960633595727407917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18372991895022921939754445 6889871960633595727407917)
            ·
              refine ⟨2583701985237598397777969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6889871960633595727407917 2583701985237598397777969)
              ·
                refine ⟨1937776488928198798333477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583701985237598397777969 1937776488928198798333477)
                ·
                  refine ⟨363333091674037274687527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937776488928198798333477 363333091674037274687527)
                  ·
                    rfl

theorem cell22_3184149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_3184149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184149 prefixEnd_3184149 := by exact prefixLift 3184149
  have htrace : WordTrace (prefixWord ++ tailWord_3184149) baseStart_3184149 baseEnd_3184149 := by
    simpa [prefixWord, tailWord_3184149, baseEnd_3184149] using wordTrace_append hprefix tailTrace_3184149
  have hstable : (prefixWord ++ tailWord_3184149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184149).length < 2 ^ (prefixWord ++ tailWord_3184149).sum := by decide
  have hdescent : baseEnd_3184149 < baseStart_3184149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184160 : List Nat := [2, 1, 1, 6, 1, 1, 1, 9]
def baseStart_3184160 : Nat := 118140960795 + 3184160 * 2 ^ 59
def prefixEnd_3184160 : Nat := 4983230072969 + 3 ^ 40 * 3184160 * 2
def baseEnd_3184160 : Nat := 121111448949656829115283

theorem tailTrace_3184160 : CollatzResearch.WordTrace tailWord_3184160 prefixEnd_3184160 121111448949656829115283 := by
  unfold tailWord_3184160
  simp only [CollatzResearch.WordTrace]
  refine ⟨58067928072169803039042967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77423904096226404052057289 58067928072169803039042967)
  ·
    refine ⟨87101892108254704558564451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58067928072169803039042967 87101892108254704558564451)
    ·
      refine ⟨130652838162382056837846677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87101892108254704558564451 130652838162382056837846677)
      ·
        refine ⟨6124351788861658914274063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130652838162382056837846677 6124351788861658914274063)
        ·
          refine ⟨9186527683292488371411095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6124351788861658914274063 9186527683292488371411095)
          ·
            refine ⟨13779791524938732557116643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9186527683292488371411095 13779791524938732557116643)
            ·
              refine ⟨20669687287408098835674965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13779791524938732557116643 20669687287408098835674965)
              ·
                refine ⟨121111448949656829115283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20669687287408098835674965 121111448949656829115283)
                ·
                  rfl

theorem cell22_3184160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_3184160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184160 prefixEnd_3184160 := by exact prefixLift 3184160
  have htrace : WordTrace (prefixWord ++ tailWord_3184160) baseStart_3184160 baseEnd_3184160 := by
    simpa [prefixWord, tailWord_3184160, baseEnd_3184160] using wordTrace_append hprefix tailTrace_3184160
  have hstable : (prefixWord ++ tailWord_3184160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184160).length < 2 ^ (prefixWord ++ tailWord_3184160).sum := by decide
  have hdescent : baseEnd_3184160 < baseStart_3184160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184198 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3184198 : Nat := 118140960795 + 3184198 * 2 ^ 59
def prefixEnd_3184198 : Nat := 4983230072969 + 3 ^ 40 * 3184198 * 2
def baseEnd_3184198 : Nat := 1090016048723492029587431

theorem tailTrace_3184198 : CollatzResearch.WordTrace tailWord_3184198 prefixEnd_3184198 1090016048723492029587431 := by
  unfold tailWord_3184198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629288816193810580249039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77424828078801292378646165 3629288816193810580249039)
  ·
    refine ⟨5443933224290715870373559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629288816193810580249039 5443933224290715870373559)
    ·
      refine ⟨8165899836436073805560339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5443933224290715870373559 8165899836436073805560339)
      ·
        refine ⟨12248849754654110708340509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8165899836436073805560339 12248849754654110708340509)
        ·
          refine ⟨4593318657995291515627691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12248849754654110708340509 4593318657995291515627691)
          ·
            refine ⟨6889977986992937273441537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593318657995291515627691 6889977986992937273441537)
            ·
              refine ⟨5167483490244702955081153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6889977986992937273441537 5167483490244702955081153)
              ·
                refine ⟨3875612617683527216310865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5167483490244702955081153 3875612617683527216310865)
                ·
                  refine ⟨2906709463262645412233149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875612617683527216310865 2906709463262645412233149)
                  ·
                    refine ⟨1090016048723492029587431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906709463262645412233149 1090016048723492029587431)
                    ·
                      rfl

theorem cell22_3184198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3184198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184198 prefixEnd_3184198 := by exact prefixLift 3184198
  have htrace : WordTrace (prefixWord ++ tailWord_3184198) baseStart_3184198 baseEnd_3184198 := by
    simpa [prefixWord, tailWord_3184198, baseEnd_3184198] using wordTrace_append hprefix tailTrace_3184198
  have hstable : (prefixWord ++ tailWord_3184198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184198).length < 2 ^ (prefixWord ++ tailWord_3184198).sum := by decide
  have hdescent : baseEnd_3184198 < baseStart_3184198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184209 : List Nat := [1, 2, 2, 1, 3, 2, 3, 4, 1, 3]
def baseStart_3184209 : Nat := 118140960795 + 3184209 * 2 ^ 59
def prefixEnd_3184209 : Nat := 4983230072969 + 3 ^ 40 * 3184209 * 2
def baseEnd_3184209 : Nat := 1090019814248291667562397

theorem tailTrace_3184209 : CollatzResearch.WordTrace tailWord_3184209 prefixEnd_3184209 1090019814248291667562397 := by
  unfold tailWord_3184209
  simp only [CollatzResearch.WordTrace]
  refine ⟨116137643321162087446619681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77425095547441391631079787 116137643321162087446619681)
  ·
    refine ⟨87103232490871565584964761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116137643321162087446619681 87103232490871565584964761)
    ·
      refine ⟨65327424368153674188723571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87103232490871565584964761 65327424368153674188723571)
      ·
        refine ⟨97991136552230511283085357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65327424368153674188723571 97991136552230511283085357)
        ·
          refine ⟨36746676207086441731157009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97991136552230511283085357 36746676207086441731157009)
          ·
            refine ⟨27560007155314831298367757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36746676207086441731157009 27560007155314831298367757)
            ·
              refine ⟨10335002683243061736887909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27560007155314831298367757 10335002683243061736887909)
              ·
                refine ⟨1937813003108074075666483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10335002683243061736887909 1937813003108074075666483)
                ·
                  refine ⟨2906719504662111113499725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937813003108074075666483 2906719504662111113499725)
                  ·
                    refine ⟨1090019814248291667562397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906719504662111113499725 1090019814248291667562397)
                    ·
                      rfl

theorem cell22_3184209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_3184209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184209 prefixEnd_3184209 := by exact prefixLift 3184209
  have htrace : WordTrace (prefixWord ++ tailWord_3184209) baseStart_3184209 baseEnd_3184209 := by
    simpa [prefixWord, tailWord_3184209, baseEnd_3184209] using wordTrace_append hprefix tailTrace_3184209
  have hstable : (prefixWord ++ tailWord_3184209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184209).length < 2 ^ (prefixWord ++ tailWord_3184209).sum := by decide
  have hdescent : baseEnd_3184209 < baseStart_3184209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184265 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_3184265 : Nat := 118140960795 + 3184265 * 2 ^ 59
def prefixEnd_3184265 : Nat := 4983230072969 + 3 ^ 40 * 3184265 * 2
def baseEnd_3184265 : Nat := 1090038984192726188162225

theorem tailTrace_3184265 : CollatzResearch.WordTrace tailWord_3184265 prefixEnd_3184265 1090038984192726188162225 := by
  unfold tailWord_3184265
  simp only [CollatzResearch.WordTrace]
  refine ⟨116139685808959209010658249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77426457205972806007105499 116139685808959209010658249)
  ·
    refine ⟨87104764356719406757993687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116139685808959209010658249 87104764356719406757993687)
    ·
      refine ⟨130657146535079110136990531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87104764356719406757993687 130657146535079110136990531)
      ·
        refine ⟨195985719802618665205485797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130657146535079110136990531 195985719802618665205485797)
        ·
          refine ⟨36747322462990999726028587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195985719802618665205485797 36747322462990999726028587)
          ·
            refine ⟨55120983694486499589042881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36747322462990999726028587 55120983694486499589042881)
            ·
              refine ⟨41340737770864874691782161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55120983694486499589042881 41340737770864874691782161)
              ·
                refine ⟨31005553328148656018836621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41340737770864874691782161 31005553328148656018836621)
                ·
                  refine ⟨11627082498055746007063733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31005553328148656018836621 11627082498055746007063733)
                  ·
                    refine ⟨1090038984192726188162225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11627082498055746007063733 1090038984192726188162225)
                    ·
                      rfl

theorem cell22_3184265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_3184265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184265 prefixEnd_3184265 := by exact prefixLift 3184265
  have htrace : WordTrace (prefixWord ++ tailWord_3184265) baseStart_3184265 baseEnd_3184265 := by
    simpa [prefixWord, tailWord_3184265, baseEnd_3184265] using wordTrace_append hprefix tailTrace_3184265
  have hstable : (prefixWord ++ tailWord_3184265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184265).length < 2 ^ (prefixWord ++ tailWord_3184265).sum := by decide
  have hdescent : baseEnd_3184265 < baseStart_3184265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184267 : List Nat := [1, 1, 1, 1, 4, 1, 3, 6, 4]
def baseStart_3184267 : Nat := 118140960795 + 3184267 * 2 ^ 59
def prefixEnd_3184267 : Nat := 4983230072969 + 3 ^ 40 * 3184267 * 2
def baseEnd_3184267 : Nat := 363346556277866283204073

theorem tailTrace_3184267 : CollatzResearch.WordTrace tailWord_3184267 prefixEnd_3184267 363346556277866283204073 := by
  unfold tailWord_3184267
  simp only [CollatzResearch.WordTrace]
  refine ⟨116139758754951963352231055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77426505836634642234820703 116139758754951963352231055)
  ·
    refine ⟨174209638132427945028346583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116139758754951963352231055 174209638132427945028346583)
    ·
      refine ⟨261314457198641917542519875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174209638132427945028346583 261314457198641917542519875)
      ·
        refine ⟨391971685797962876313779813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261314457198641917542519875 391971685797962876313779813)
        ·
          refine ⟨73494691087118039308833715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391971685797962876313779813 73494691087118039308833715)
          ·
            refine ⟨110242036630677058963250573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73494691087118039308833715 110242036630677058963250573)
            ·
              refine ⟨41340763736503897111218965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110242036630677058963250573 41340763736503897111218965)
              ·
                refine ⟨1937848300148620177088389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41340763736503897111218965 1937848300148620177088389)
                ·
                  refine ⟨363346556277866283204073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937848300148620177088389 363346556277866283204073)
                  ·
                    rfl

theorem cell22_3184267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 4].length) (baseStart_3184267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184267 prefixEnd_3184267 := by exact prefixLift 3184267
  have htrace : WordTrace (prefixWord ++ tailWord_3184267) baseStart_3184267 baseEnd_3184267 := by
    simpa [prefixWord, tailWord_3184267, baseEnd_3184267] using wordTrace_append hprefix tailTrace_3184267
  have hstable : (prefixWord ++ tailWord_3184267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184267).length < 2 ^ (prefixWord ++ tailWord_3184267).sum := by decide
  have hdescent : baseEnd_3184267 < baseStart_3184267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184286 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3184286 : Nat := 118140960795 + 3184286 * 2 ^ 59
def prefixEnd_3184286 : Nat := 4983230072969 + 3 ^ 40 * 3184286 * 2
def baseEnd_3184286 : Nat := 1090046172921889133387161

theorem tailTrace_3184286 : CollatzResearch.WordTrace tailWord_3184286 prefixEnd_3184286 1090046172921889133387161 := by
  unfold tailWord_3184286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14517556467735391199646589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77426967827922086398115141 14517556467735391199646589)
  ·
    refine ⟨5444083675400771699867471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14517556467735391199646589 5444083675400771699867471)
    ·
      refine ⟨8166125513101157549801207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444083675400771699867471 8166125513101157549801207)
      ·
        refine ⟨12249188269651736324701811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8166125513101157549801207 12249188269651736324701811)
        ·
          refine ⟨18373782404477604487052717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12249188269651736324701811 18373782404477604487052717)
          ·
            refine ⟨6890168401679101682644769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18373782404477604487052717 6890168401679101682644769)
            ·
              refine ⟨5167626301259326261983577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6890168401679101682644769 5167626301259326261983577)
              ·
                refine ⟨3875719725944494696487683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5167626301259326261983577 3875719725944494696487683)
                ·
                  refine ⟨5813579588916742044731525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875719725944494696487683 5813579588916742044731525)
                  ·
                    refine ⟨1090046172921889133387161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5813579588916742044731525 1090046172921889133387161)
                    ·
                      rfl

theorem cell22_3184286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3184286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184286 prefixEnd_3184286 := by exact prefixLift 3184286
  have htrace : WordTrace (prefixWord ++ tailWord_3184286) baseStart_3184286 baseEnd_3184286 := by
    simpa [prefixWord, tailWord_3184286, baseEnd_3184286] using wordTrace_append hprefix tailTrace_3184286
  have hstable : (prefixWord ++ tailWord_3184286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184286).length < 2 ^ (prefixWord ++ tailWord_3184286).sum := by decide
  have hdescent : baseEnd_3184286 < baseStart_3184286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184325 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_3184325 : Nat := 118140960795 + 3184325 * 2 ^ 59
def prefixEnd_3184325 : Nat := 4983230072969 + 3 ^ 40 * 3184325 * 2
def baseEnd_3184325 : Nat := 1090059523418906031662041

theorem tailTrace_3184325 : CollatzResearch.WordTrace tailWord_3184325 prefixEnd_3184325 1090059523418906031662041 := by
  unfold tailWord_3184325
  simp only [CollatzResearch.WordTrace]
  refine ⟨116141874188741839257842429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77427916125827892838561619 116141874188741839257842429)
  ·
    refine ⟨43553202820778189721690911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116141874188741839257842429 43553202820778189721690911)
    ·
      refine ⟨65329804231167284582536367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43553202820778189721690911 65329804231167284582536367)
      ·
        refine ⟨97994706346750926873804551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65329804231167284582536367 97994706346750926873804551)
        ·
          refine ⟨146992059520126390310706827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97994706346750926873804551 146992059520126390310706827)
          ·
            refine ⟨220488089280189585466060241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146992059520126390310706827 220488089280189585466060241)
            ·
              refine ⟨165366066960142189099545181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220488089280189585466060241 165366066960142189099545181)
              ·
                refine ⟨62012275110053320912329443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165366066960142189099545181 62012275110053320912329443)
                ·
                  refine ⟨93018412665079981368494165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62012275110053320912329443 93018412665079981368494165)
                  ·
                    refine ⟨1090059523418906031662041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93018412665079981368494165 1090059523418906031662041)
                    ·
                      rfl

theorem cell22_3184325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_3184325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184325 prefixEnd_3184325 := by exact prefixLift 3184325
  have htrace : WordTrace (prefixWord ++ tailWord_3184325) baseStart_3184325 baseEnd_3184325 := by
    simpa [prefixWord, tailWord_3184325, baseEnd_3184325] using wordTrace_append hprefix tailTrace_3184325
  have hstable : (prefixWord ++ tailWord_3184325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184325).length < 2 ^ (prefixWord ++ tailWord_3184325).sum := by decide
  have hdescent : baseEnd_3184325 < baseStart_3184325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184333 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3184333 : Nat := 118140960795 + 3184333 * 2 ^ 59
def prefixEnd_3184333 : Nat := 4983230072969 + 3 ^ 40 * 3184333 * 2
def baseEnd_3184333 : Nat := 1090062261982396677462017

theorem tailTrace_3184333 : CollatzResearch.WordTrace tailWord_3184333 prefixEnd_3184333 1090062261982396677462017 := by
  unfold tailWord_3184333
  simp only [CollatzResearch.WordTrace]
  refine ⟨116142165972712856624133653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77428110648475237749422435 116142165972712856624133653)
  ·
    refine ⟨5444164029970915154256265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116142165972712856624133653 5444164029970915154256265)
    ·
      refine ⟨4083123022478186365692199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5444164029970915154256265 4083123022478186365692199)
      ·
        refine ⟨6124684533717279548538299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083123022478186365692199 6124684533717279548538299)
        ·
          refine ⟨9187026800575919322807449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6124684533717279548538299 9187026800575919322807449)
          ·
            refine ⟨6890270100431939492105587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9187026800575919322807449 6890270100431939492105587)
            ·
              refine ⟨10335405150647909238158381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890270100431939492105587 10335405150647909238158381)
              ·
                refine ⟨3875776931492965964309393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10335405150647909238158381 3875776931492965964309393)
                ·
                  refine ⟨2906832698619724473232045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875776931492965964309393 2906832698619724473232045)
                  ·
                    refine ⟨1090062261982396677462017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906832698619724473232045 1090062261982396677462017)
                    ·
                      rfl

theorem cell22_3184333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3184333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184333 prefixEnd_3184333 := by exact prefixLift 3184333
  have htrace : WordTrace (prefixWord ++ tailWord_3184333) baseStart_3184333 baseEnd_3184333 := by
    simpa [prefixWord, tailWord_3184333, baseEnd_3184333] using wordTrace_append hprefix tailTrace_3184333
  have hstable : (prefixWord ++ tailWord_3184333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184333).length < 2 ^ (prefixWord ++ tailWord_3184333).sum := by decide
  have hdescent : baseEnd_3184333 < baseStart_3184333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184374 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3184374 : Nat := 118140960795 + 3184374 * 2 ^ 59
def prefixEnd_3184374 : Nat := 4983230072969 + 3 ^ 40 * 3184374 * 2
def baseEnd_3184374 : Nat := 363358765706762079062297

theorem tailTrace_3184374 : CollatzResearch.WordTrace tailWord_3184374 prefixEnd_3184374 363358765706762079062297 := by
  unfold tailWord_3184374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258978835347770039148511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77429107577042880417584117 7258978835347770039148511)
  ·
    refine ⟨10888468253021655058722767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7258978835347770039148511 10888468253021655058722767)
    ·
      refine ⟨16332702379532482588084151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10888468253021655058722767 16332702379532482588084151)
      ·
        refine ⟨24499053569298723882126227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16332702379532482588084151 24499053569298723882126227)
        ·
          refine ⟨36748580353948085823189341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24499053569298723882126227 36748580353948085823189341)
          ·
            refine ⟨13780717632730532183696003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36748580353948085823189341 13780717632730532183696003)
            ·
              refine ⟨20671076449095798275544005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13780717632730532183696003 20671076449095798275544005)
              ·
                refine ⟨3875826834205462176664501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20671076449095798275544005 3875826834205462176664501)
                ·
                  refine ⟨363358765706762079062297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3875826834205462176664501 363358765706762079062297)
                  ·
                    rfl

theorem cell22_3184374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3184374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184374 prefixEnd_3184374 := by exact prefixLift 3184374
  have htrace : WordTrace (prefixWord ++ tailWord_3184374) baseStart_3184374 baseEnd_3184374 := by
    simpa [prefixWord, tailWord_3184374, baseEnd_3184374] using wordTrace_append hprefix tailTrace_3184374
  have hstable : (prefixWord ++ tailWord_3184374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184374).length < 2 ^ (prefixWord ++ tailWord_3184374).sum := by decide
  have hdescent : baseEnd_3184374 < baseStart_3184374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184387 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 3, 4]
def baseStart_3184387 : Nat := 118140960795 + 3184387 * 2 ^ 59
def prefixEnd_3184387 : Nat := 4983230072969 + 3 ^ 40 * 3184387 * 2
def baseEnd_3184387 : Nat := 1090080747285958536611851

theorem tailTrace_3184387 : CollatzResearch.WordTrace tailWord_3184387 prefixEnd_3184387 1090080747285958536611851 := by
  unfold tailWord_3184387
  simp only [CollatzResearch.WordTrace]
  refine ⟨116144135514517223846599415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77429423676344815897732943 116144135514517223846599415)
  ·
    refine ⟨174216203271775835769899123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116144135514517223846599415 174216203271775835769899123)
    ·
      refine ⟨261324304907663753654848685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174216203271775835769899123 261324304907663753654848685)
      ·
        refine ⟨97996614340373907620568257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261324304907663753654848685 97996614340373907620568257)
        ·
          refine ⟨73497460755280430715426193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97996614340373907620568257 73497460755280430715426193)
          ·
            refine ⟨55123095566460323036569645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73497460755280430715426193 55123095566460323036569645)
            ·
              refine ⟨20671160837422621138713617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55123095566460323036569645 20671160837422621138713617)
              ·
                refine ⟨15503370628066965854035213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20671160837422621138713617 15503370628066965854035213)
                ·
                  refine ⟨5813763985525112195263205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15503370628066965854035213 5813763985525112195263205)
                  ·
                    refine ⟨1090080747285958536611851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5813763985525112195263205 1090080747285958536611851)
                    ·
                      rfl

theorem cell22_3184387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_3184387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184387 prefixEnd_3184387 := by exact prefixLift 3184387
  have htrace : WordTrace (prefixWord ++ tailWord_3184387) baseStart_3184387 baseEnd_3184387 := by
    simpa [prefixWord, tailWord_3184387, baseEnd_3184387] using wordTrace_append hprefix tailTrace_3184387
  have hstable : (prefixWord ++ tailWord_3184387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184387).length < 2 ^ (prefixWord ++ tailWord_3184387).sum := by decide
  have hdescent : baseEnd_3184387 < baseStart_3184387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184419 : List Nat := [1, 1, 1, 4, 2, 1, 3, 5, 4]
def baseStart_3184419 : Nat := 118140960795 + 3184419 * 2 ^ 59
def prefixEnd_3184419 : Nat := 4983230072969 + 3 ^ 40 * 3184419 * 2
def baseEnd_3184419 : Nat := 363363900513307039937251

theorem tailTrace_3184419 : CollatzResearch.WordTrace tailWord_3184419 prefixEnd_3184419 363363900513307039937251 := by
  unfold tailWord_3184419
  simp only [CollatzResearch.WordTrace]
  refine ⟨116145302650401293311764311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77430201766934195541176207 116145302650401293311764311)
  ·
    refine ⟨174217953975601939967646467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116145302650401293311764311 174217953975601939967646467)
    ·
      refine ⟨261326930963402909951469701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174217953975601939967646467 261326930963402909951469701)
      ·
        refine ⟨48998799555638045615900569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261326930963402909951469701 48998799555638045615900569)
        ·
          refine ⟨36749099666728534211925427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48998799555638045615900569 36749099666728534211925427)
          ·
            refine ⟨55123649500092801317888141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36749099666728534211925427 55123649500092801317888141)
            ·
              refine ⟨20671368562534800494208053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55123649500092801317888141 20671368562534800494208053)
              ·
                refine ⟨1937940802737637546332005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20671368562534800494208053 1937940802737637546332005)
                ·
                  refine ⟨363363900513307039937251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937940802737637546332005 363363900513307039937251)
                  ·
                    rfl

theorem cell22_3184419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 4].length) (baseStart_3184419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184419 prefixEnd_3184419 := by exact prefixLift 3184419
  have htrace : WordTrace (prefixWord ++ tailWord_3184419) baseStart_3184419 baseEnd_3184419 := by
    simpa [prefixWord, tailWord_3184419, baseEnd_3184419] using wordTrace_append hprefix tailTrace_3184419
  have hstable : (prefixWord ++ tailWord_3184419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184419).length < 2 ^ (prefixWord ++ tailWord_3184419).sum := by decide
  have hdescent : baseEnd_3184419 < baseStart_3184419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184421 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_3184421 : Nat := 118140960795 + 3184421 * 2 ^ 59
def prefixEnd_3184421 : Nat := 4983230072969 + 3 ^ 40 * 3184421 * 2
def baseEnd_3184421 : Nat := 1090092386180793781261747

theorem tailTrace_3184421 : CollatzResearch.WordTrace tailWord_3184421 prefixEnd_3184421 1090092386180793781261747 := by
  unfold tailWord_3184421
  simp only [CollatzResearch.WordTrace]
  refine ⟨116145375596394047653337117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77430250397596031768891411 116145375596394047653337117)
  ·
    refine ⟨43554515848647767870001419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116145375596394047653337117 43554515848647767870001419)
    ·
      refine ⟨65331773772971651805002129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43554515848647767870001419 65331773772971651805002129)
      ·
        refine ⟨48998830329728738853751597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65331773772971651805002129 48998830329728738853751597)
        ·
          refine ⟨18374561373648277070156849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48998830329728738853751597 18374561373648277070156849)
          ·
            refine ⟨13780921030236207802617637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18374561373648277070156849 13780921030236207802617637)
            ·
              refine ⟨2583922693169288962990807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13780921030236207802617637 2583922693169288962990807)
              ·
                refine ⟨3875884039753933444486211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583922693169288962990807 3875884039753933444486211)
                ·
                  refine ⟨5813826059630900166729317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875884039753933444486211 5813826059630900166729317)
                  ·
                    refine ⟨1090092386180793781261747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5813826059630900166729317 1090092386180793781261747)
                    ·
                      rfl

theorem cell22_3184421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_3184421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184421 prefixEnd_3184421 := by exact prefixLift 3184421
  have htrace : WordTrace (prefixWord ++ tailWord_3184421) baseStart_3184421 baseEnd_3184421 := by
    simpa [prefixWord, tailWord_3184421, baseEnd_3184421] using wordTrace_append hprefix tailTrace_3184421
  have hstable : (prefixWord ++ tailWord_3184421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184421).length < 2 ^ (prefixWord ++ tailWord_3184421).sum := by decide
  have hdescent : baseEnd_3184421 < baseStart_3184421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184436 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3184436 : Nat := 118140960795 + 3184436 * 2 ^ 59
def prefixEnd_3184436 : Nat := 4983230072969 + 3 ^ 40 * 3184436 * 2
def baseEnd_3184436 : Nat := 363365840329112914045567

theorem tailTrace_3184436 : CollatzResearch.WordTrace tailWord_3184436 prefixEnd_3184436 363365840329112914045567 := by
  unfold tailWord_3184436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58072961345669852607566581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77430615127559803476755441 58072961345669852607566581)
  ·
    refine ⟨5444340126156548681959367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58072961345669852607566581 5444340126156548681959367)
    ·
      refine ⟨8166510189234823022939051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444340126156548681959367 8166510189234823022939051)
      ·
        refine ⟨12249765283852234534408577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8166510189234823022939051 12249765283852234534408577)
        ·
          refine ⟨9187323962889175900806433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12249765283852234534408577 9187323962889175900806433)
          ·
            refine ⟨6890492972166881925604825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9187323962889175900806433 6890492972166881925604825)
            ·
              refine ⟨5167869729125161444203619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6890492972166881925604825 5167869729125161444203619)
              ·
                refine ⟨7751804593687742166305429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167869729125161444203619 7751804593687742166305429)
                ·
                  refine ⟨363365840329112914045567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7751804593687742166305429 363365840329112914045567)
                  ·
                    rfl

theorem cell22_3184436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3184436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184436 prefixEnd_3184436 := by exact prefixLift 3184436
  have htrace : WordTrace (prefixWord ++ tailWord_3184436) baseStart_3184436 baseEnd_3184436 := by
    simpa [prefixWord, tailWord_3184436, baseEnd_3184436] using wordTrace_append hprefix tailTrace_3184436
  have hstable : (prefixWord ++ tailWord_3184436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184436).length < 2 ^ (prefixWord ++ tailWord_3184436).sum := by decide
  have hdescent : baseEnd_3184436 < baseStart_3184436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184502 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_3184502 : Nat := 118140960795 + 3184502 * 2 ^ 59
def prefixEnd_3184502 : Nat := 4983230072969 + 3 ^ 40 * 3184502 * 2
def baseEnd_3184502 : Nat := 1090120114136136569986499

theorem tailTrace_3184502 : CollatzResearch.WordTrace tailWord_3184502 prefixEnd_3184502 1090120114136136569986499 := by
  unfold tailWord_3184502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259270619318787405439735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77432219939400398991357173 7259270619318787405439735)
  ·
    refine ⟨10888905928978181108159603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7259270619318787405439735 10888905928978181108159603)
    ·
      refine ⟨16333358893467271662239405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10888905928978181108159603 16333358893467271662239405)
      ·
        refine ⟨6125009585050226873339777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16333358893467271662239405 6125009585050226873339777)
        ·
          refine ⟨4593757188787670155004833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6125009585050226873339777 4593757188787670155004833)
          ·
            refine ⟨3445317891590752616253625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4593757188787670155004833 3445317891590752616253625)
            ·
              refine ⟨2583988418693064462190219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445317891590752616253625 2583988418693064462190219)
              ·
                refine ⟨3875982628039596693285329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583988418693064462190219 3875982628039596693285329)
                ·
                  refine ⟨2906986971029697519963997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875982628039596693285329 2906986971029697519963997)
                  ·
                    refine ⟨1090120114136136569986499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906986971029697519963997 1090120114136136569986499)
                    ·
                      rfl

theorem cell22_3184502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_3184502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184502 prefixEnd_3184502 := by exact prefixLift 3184502
  have htrace : WordTrace (prefixWord ++ tailWord_3184502) baseStart_3184502 baseEnd_3184502 := by
    simpa [prefixWord, tailWord_3184502, baseEnd_3184502] using wordTrace_append hprefix tailTrace_3184502
  have hstable : (prefixWord ++ tailWord_3184502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184502).length < 2 ^ (prefixWord ++ tailWord_3184502).sum := by decide
  have hdescent : baseEnd_3184502 < baseStart_3184502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184507 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 1, 7]
def baseStart_3184507 : Nat := 118140960795 + 3184507 * 2 ^ 59
def prefixEnd_3184507 : Nat := 4983230072969 + 3 ^ 40 * 3184507 * 2
def baseEnd_3184507 : Nat := 1090121825738318223611483

theorem tailTrace_3184507 : CollatzResearch.WordTrace tailWord_3184507 prefixEnd_3184507 1090121825738318223611483 := by
  unfold tailWord_3184507
  simp only [CollatzResearch.WordTrace]
  refine ⟨116148512274082484340967775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77432341516054989560645183 116148512274082484340967775)
  ·
    refine ⟨174222768411123726511451663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116148512274082484340967775 174222768411123726511451663)
    ·
      refine ⟨261334152616685589767177495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174222768411123726511451663 261334152616685589767177495)
      ·
        refine ⟨392001228925028384650766243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261334152616685589767177495 392001228925028384650766243)
        ·
          refine ⟨588001843387542576976149365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392001228925028384650766243 588001843387542576976149365)
          ·
            refine ⟨55125172817582116591514003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 588001843387542576976149365 55125172817582116591514003)
            ·
              refine ⟨82687759226373174887271005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55125172817582116591514003 82687759226373174887271005)
              ·
                refine ⟨31007909709889940582726627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82687759226373174887271005 31007909709889940582726627)
                ·
                  refine ⟨46511864564834910874089941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31007909709889940582726627 46511864564834910874089941)
                  ·
                    refine ⟨1090121825738318223611483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46511864564834910874089941 1090121825738318223611483)
                    ·
                      rfl

theorem cell22_3184507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_3184507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184507 prefixEnd_3184507 := by exact prefixLift 3184507
  have htrace : WordTrace (prefixWord ++ tailWord_3184507) baseStart_3184507 baseEnd_3184507 := by
    simpa [prefixWord, tailWord_3184507, baseEnd_3184507] using wordTrace_append hprefix tailTrace_3184507
  have hstable : (prefixWord ++ tailWord_3184507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184507).length < 2 ^ (prefixWord ++ tailWord_3184507).sum := by decide
  have hdescent : baseEnd_3184507 < baseStart_3184507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184588 : List Nat := [2, 2, 1, 4, 1, 3, 2, 3, 4]
def baseStart_3184588 : Nat := 118140960795 + 3184588 * 2 ^ 59
def prefixEnd_3184588 : Nat := 4983230072969 + 3 ^ 40 * 3184588 * 2
def baseEnd_3184588 : Nat := 363383184564553670778745

theorem tailTrace_3184588 : CollatzResearch.WordTrace tailWord_3184588 prefixEnd_3184588 363383184564553670778745 := by
  unfold tailWord_3184588
  simp only [CollatzResearch.WordTrace]
  refine ⟨58075733293394517587333209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77434311057859356783110945 58075733293394517587333209)
  ·
    refine ⟨43556799970045888190499907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58075733293394517587333209 43556799970045888190499907)
    ·
      refine ⟨65335199955068832285749861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43556799970045888190499907 65335199955068832285749861)
      ·
        refine ⟨12250349991575406053578099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65335199955068832285749861 12250349991575406053578099)
        ·
          refine ⟨18375524987363109080367149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12250349991575406053578099 18375524987363109080367149)
          ·
            refine ⟨6890821870261165905137681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18375524987363109080367149 6890821870261165905137681)
            ·
              refine ⟨5168116402695874428853261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6890821870261165905137681 5168116402695874428853261)
              ·
                refine ⟨1938043651010952910819973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5168116402695874428853261 1938043651010952910819973)
                ·
                  refine ⟨363383184564553670778745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938043651010952910819973 363383184564553670778745)
                  ·
                    rfl

theorem cell22_3184588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_3184588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184588 prefixEnd_3184588 := by exact prefixLift 3184588
  have htrace : WordTrace (prefixWord ++ tailWord_3184588) baseStart_3184588 baseEnd_3184588 := by
    simpa [prefixWord, tailWord_3184588, baseEnd_3184588] using wordTrace_append hprefix tailTrace_3184588
  have hstable : (prefixWord ++ tailWord_3184588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184588).length < 2 ^ (prefixWord ++ tailWord_3184588).sum := by decide
  have hdescent : baseEnd_3184588 < baseStart_3184588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184659 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 4, 5]
def baseStart_3184659 : Nat := 118140960795 + 3184659 * 2 ^ 59
def prefixEnd_3184659 : Nat := 4983230072969 + 3 ^ 40 * 3184659 * 2
def baseEnd_3184659 : Nat := 1090173858444640493811017

theorem tailTrace_3184659 : CollatzResearch.WordTrace tailWord_3184659 prefixEnd_3184659 1090173858444640493811017 := by
  unfold tailWord_3184659
  simp only [CollatzResearch.WordTrace]
  refine ⟨116154056169531814300501031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77436037446354542867000687 116154056169531814300501031)
  ·
    refine ⟨174231084254297721450751547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116154056169531814300501031 174231084254297721450751547)
    ·
      refine ⟨261346626381446582176127321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174231084254297721450751547 261346626381446582176127321)
      ·
        refine ⟨196009969786084936632095491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261346626381446582176127321 196009969786084936632095491)
        ·
          refine ⟨294014954679127404948143237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196009969786084936632095491 294014954679127404948143237)
          ·
            refine ⟨55127804002336388427776857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294014954679127404948143237 55127804002336388427776857)
            ·
              refine ⟨41345853001752291320832643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55127804002336388427776857 41345853001752291320832643)
              ·
                refine ⟨62018779502628436981248965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41345853001752291320832643 62018779502628436981248965)
                ·
                  refine ⟨11628521156742831933984181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62018779502628436981248965 11628521156742831933984181)
                  ·
                    refine ⟨1090173858444640493811017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11628521156742831933984181 1090173858444640493811017)
                    ·
                      rfl

theorem cell22_3184659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_3184659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184659 prefixEnd_3184659 := by exact prefixLift 3184659
  have htrace : WordTrace (prefixWord ++ tailWord_3184659) baseStart_3184659 baseEnd_3184659 := by
    simpa [prefixWord, tailWord_3184659, baseEnd_3184659] using wordTrace_append hprefix tailTrace_3184659
  have hstable : (prefixWord ++ tailWord_3184659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184659).length < 2 ^ (prefixWord ++ tailWord_3184659).sum := by decide
  have hdescent : baseEnd_3184659 < baseStart_3184659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184813 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 7]
def baseStart_3184813 : Nat := 118140960795 + 3184813 * 2 ^ 59
def prefixEnd_3184813 : Nat := 4983230072969 + 3 ^ 40 * 3184813 * 2
def baseEnd_3184813 : Nat := 363408858597278475153515

theorem tailTrace_3184813 : CollatzResearch.WordTrace tailWord_3184813 prefixEnd_3184813 363408858597278475153515 := by
  unfold tailWord_3184813
  simp only [CollatzResearch.WordTrace]
  refine ⟨116159673010973898601607093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77439782007315932401071395 116159673010973898601607093)
  ·
    refine ⟨10889969344778802993900665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116159673010973898601607093 10889969344778802993900665)
    ·
      refine ⟨8167477008584102245425499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10889969344778802993900665 8167477008584102245425499)
      ·
        refine ⟨12251215512876153368138249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167477008584102245425499 12251215512876153368138249)
        ·
          refine ⟨9188411634657115026103687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12251215512876153368138249 9188411634657115026103687)
          ·
            refine ⟨13782617451985672539155531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9188411634657115026103687 13782617451985672539155531)
            ·
              refine ⟨20673926177978508808733297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13782617451985672539155531 20673926177978508808733297)
              ·
                refine ⟨15505444633483881606549973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20673926177978508808733297 15505444633483881606549973)
                ·
                  refine ⟨363408858597278475153515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15505444633483881606549973 363408858597278475153515)
                  ·
                    rfl

theorem cell22_3184813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_3184813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184813 prefixEnd_3184813 := by exact prefixLift 3184813
  have htrace : WordTrace (prefixWord ++ tailWord_3184813) baseStart_3184813 baseEnd_3184813 := by
    simpa [prefixWord, tailWord_3184813, baseEnd_3184813] using wordTrace_append hprefix tailTrace_3184813
  have hstable : (prefixWord ++ tailWord_3184813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184813).length < 2 ^ (prefixWord ++ tailWord_3184813).sum := by decide
  have hdescent : baseEnd_3184813 < baseStart_3184813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184834 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3184834 : Nat := 118140960795 + 3184834 * 2 ^ 59
def prefixEnd_3184834 : Nat := 4983230072969 + 3 ^ 40 * 3184834 * 2
def baseEnd_3184834 : Nat := 1090233764520998370685481

theorem tailTrace_3184834 : CollatzResearch.WordTrace tailWord_3184834 prefixEnd_3184834 1090233764520998370685481 := by
  unfold tailWord_3184834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040109735974454797030389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77440292629265212792081037 29040109735974454797030389)
  ·
    refine ⟨2722510287747605137221599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29040109735974454797030389 2722510287747605137221599)
    ·
      refine ⟨4083765431621407705832399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722510287747605137221599 4083765431621407705832399)
      ·
        refine ⟨6125648147432111558748599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083765431621407705832399 6125648147432111558748599)
        ·
          refine ⟨9188472221148167338122899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125648147432111558748599 9188472221148167338122899)
          ·
            refine ⟨13782708331722251007184349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9188472221148167338122899 13782708331722251007184349)
            ·
              refine ⟨5168515624395844127694131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13782708331722251007184349 5168515624395844127694131)
              ·
                refine ⟨7752773436593766191541197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168515624395844127694131 7752773436593766191541197)
                ·
                  refine ⟨2907290038722662321827949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7752773436593766191541197 2907290038722662321827949)
                  ·
                    refine ⟨1090233764520998370685481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907290038722662321827949 1090233764520998370685481)
                    ·
                      rfl

theorem cell22_3184834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3184834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184834 prefixEnd_3184834 := by exact prefixLift 3184834
  have htrace : WordTrace (prefixWord ++ tailWord_3184834) baseStart_3184834 baseEnd_3184834 := by
    simpa [prefixWord, tailWord_3184834, baseEnd_3184834] using wordTrace_append hprefix tailTrace_3184834
  have hstable : (prefixWord ++ tailWord_3184834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184834).length < 2 ^ (prefixWord ++ tailWord_3184834).sum := by decide
  have hdescent : baseEnd_3184834 < baseStart_3184834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184841 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 6]
def baseStart_3184841 : Nat := 118140960795 + 3184841 * 2 ^ 59
def prefixEnd_3184841 : Nat := 4983230072969 + 3 ^ 40 * 3184841 * 2
def baseEnd_3184841 : Nat := 363412053588017561920153

theorem tailTrace_3184841 : CollatzResearch.WordTrace tailWord_3184841 prefixEnd_3184841 363412053588017561920153 := by
  unfold tailWord_3184841
  simp only [CollatzResearch.WordTrace]
  refine ⟨116160694254872459383626377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77440462836581639589084251 116160694254872459383626377)
  ·
    refine ⟨87120520691154344537719783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116160694254872459383626377 87120520691154344537719783)
    ·
      refine ⟨130680781036731516806579675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87120520691154344537719783 130680781036731516806579675)
      ·
        refine ⟨196021171555097275209869513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130680781036731516806579675 196021171555097275209869513)
        ·
          refine ⟨147015878666322956407402135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196021171555097275209869513 147015878666322956407402135)
          ·
            refine ⟨220523817999484434611103203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147015878666322956407402135 220523817999484434611103203)
            ·
              refine ⟨330785726999226651916654805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220523817999484434611103203 330785726999226651916654805)
              ·
                refine ⟨7752790476544374654296597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 330785726999226651916654805 7752790476544374654296597)
                ·
                  refine ⟨363412053588017561920153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7752790476544374654296597 363412053588017561920153)
                  ·
                    rfl

theorem cell22_3184841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_3184841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184841 prefixEnd_3184841 := by exact prefixLift 3184841
  have htrace : WordTrace (prefixWord ++ tailWord_3184841) baseStart_3184841 baseEnd_3184841 := by
    simpa [prefixWord, tailWord_3184841, baseEnd_3184841] using wordTrace_append hprefix tailTrace_3184841
  have hstable : (prefixWord ++ tailWord_3184841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184841).length < 2 ^ (prefixWord ++ tailWord_3184841).sum := by decide
  have hdescent : baseEnd_3184841 < baseStart_3184841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184890 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_3184890 : Nat := 118140960795 + 3184890 * 2 ^ 59
def prefixEnd_3184890 : Nat := 4983230072969 + 3 ^ 40 * 3184890 * 2
def baseEnd_3184890 : Nat := 1090252934465432891285309

theorem tailTrace_3184890 : CollatzResearch.WordTrace tailWord_3184890 prefixEnd_3184890 1090252934465432891285309 := by
  unfold tailWord_3184890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040620357923735188040031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77441654287796627168106749 29040620357923735188040031)
  ·
    refine ⟨43560930536885602782060047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29040620357923735188040031 43560930536885602782060047)
    ·
      refine ⟨65341395805328404173090071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43560930536885602782060047 65341395805328404173090071)
      ·
        refine ⟨98012093707992606259635107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65341395805328404173090071 98012093707992606259635107)
        ·
          refine ⟨147018140561988909389452661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98012093707992606259635107 147018140561988909389452661)
          ·
            refine ⟨13782950677686460255261187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147018140561988909389452661 13782950677686460255261187)
            ·
              refine ⟨20674426016529690382891781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13782950677686460255261187 20674426016529690382891781)
              ·
                refine ⟨3876454878099316946792209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20674426016529690382891781 3876454878099316946792209)
                ·
                  refine ⟨2907341158574487710094157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876454878099316946792209 2907341158574487710094157)
                  ·
                    refine ⟨1090252934465432891285309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907341158574487710094157 1090252934465432891285309)
                    ·
                      rfl

theorem cell22_3184890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_3184890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184890 prefixEnd_3184890 := by exact prefixLift 3184890
  have htrace : WordTrace (prefixWord ++ tailWord_3184890) baseStart_3184890 baseEnd_3184890 := by
    simpa [prefixWord, tailWord_3184890, baseEnd_3184890] using wordTrace_append hprefix tailTrace_3184890
  have hstable : (prefixWord ++ tailWord_3184890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184890).length < 2 ^ (prefixWord ++ tailWord_3184890).sum := by decide
  have hdescent : baseEnd_3184890 < baseStart_3184890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184892 : List Nat := [2, 2, 2, 1, 4, 1, 4, 2, 4]
def baseStart_3184892 : Nat := 118140960795 + 3184892 * 2 ^ 59
def prefixEnd_3184892 : Nat := 4983230072969 + 3 ^ 40 * 3184892 * 2
def baseEnd_3184892 : Nat := 363417873035435184245101

theorem tailTrace_3184892 : CollatzResearch.WordTrace tailWord_3184892 prefixEnd_3184892 363417873035435184245101 := by
  unfold tailWord_3184892
  simp only [CollatzResearch.WordTrace]
  refine ⟨58081277188843847546866465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77441702918458463395821953 58081277188843847546866465)
  ·
    refine ⟨43560957891632885660149849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58081277188843847546866465 43560957891632885660149849)
    ·
      refine ⟨32670718418724664245112387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43560957891632885660149849 32670718418724664245112387)
      ·
        refine ⟨49006077628086996367668581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32670718418724664245112387 49006077628086996367668581)
        ·
          refine ⟨9188639555266311818937859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49006077628086996367668581 9188639555266311818937859)
          ·
            refine ⟨13782959332899467728406789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9188639555266311818937859 13782959332899467728406789)
            ·
              refine ⟨2584304874918650199076273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13782959332899467728406789 2584304874918650199076273)
              ·
                refine ⟨1938228656188987649307205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584304874918650199076273 1938228656188987649307205)
                ·
                  refine ⟨363417873035435184245101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938228656188987649307205 363417873035435184245101)
                  ·
                    rfl

theorem cell22_3184892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_3184892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184892 prefixEnd_3184892 := by exact prefixLift 3184892
  have htrace : WordTrace (prefixWord ++ tailWord_3184892) baseStart_3184892 baseEnd_3184892 := by
    simpa [prefixWord, tailWord_3184892, baseEnd_3184892] using wordTrace_append hprefix tailTrace_3184892
  have hstable : (prefixWord ++ tailWord_3184892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184892).length < 2 ^ (prefixWord ++ tailWord_3184892).sum := by decide
  have hdescent : baseEnd_3184892 < baseStart_3184892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184922 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_3184922 : Nat := 118140960795 + 3184922 * 2 ^ 59
def prefixEnd_3184922 : Nat := 4983230072969 + 3 ^ 40 * 3184922 * 2
def baseEnd_3184922 : Nat := 1090263888719395474485211

theorem tailTrace_3184922 : CollatzResearch.WordTrace tailWord_3184922 prefixEnd_3184922 1090263888719395474485211 := by
  unfold tailWord_3184922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040912141894752554331255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77442432378386006811550013 29040912141894752554331255)
  ·
    refine ⟨43561368212842128831496883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29040912141894752554331255 43561368212842128831496883)
    ·
      refine ⟨65342052319263193247245325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43561368212842128831496883 65342052319263193247245325)
      ·
        refine ⟨24503269619723697467716997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65342052319263193247245325 24503269619723697467716997)
        ·
          refine ⟨4594363053698193275196937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24503269619723697467716997 4594363053698193275196937)
          ·
            refine ⟨3445772290273644956397703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594363053698193275196937 3445772290273644956397703)
            ·
              refine ⟨5168658435410467434596555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445772290273644956397703 5168658435410467434596555)
              ·
                refine ⟨7752987653115701151894833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168658435410467434596555 7752987653115701151894833)
                ·
                  refine ⟨5814740739836775863921125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7752987653115701151894833 5814740739836775863921125)
                  ·
                    refine ⟨1090263888719395474485211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5814740739836775863921125 1090263888719395474485211)
                    ·
                      rfl

theorem cell22_3184922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_3184922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184922 prefixEnd_3184922 := by exact prefixLift 3184922
  have htrace : WordTrace (prefixWord ++ tailWord_3184922) baseStart_3184922 baseEnd_3184922 := by
    simpa [prefixWord, tailWord_3184922, baseEnd_3184922] using wordTrace_append hprefix tailTrace_3184922
  have hstable : (prefixWord ++ tailWord_3184922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184922).length < 2 ^ (prefixWord ++ tailWord_3184922).sum := by decide
  have hdescent : baseEnd_3184922 < baseStart_3184922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184941 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3184941 : Nat := 118140960795 + 3184941 * 2 ^ 59
def prefixEnd_3184941 : Nat := 4983230072969 + 3 ^ 40 * 3184941 * 2
def baseEnd_3184941 : Nat := 1090270392807685758260153

theorem tailTrace_3184941 : CollatzResearch.WordTrace tailWord_3184941 prefixEnd_3184941 1090270392807685758260153 := by
  unfold tailWord_3184941
  simp only [CollatzResearch.WordTrace]
  refine ⟨116164341554510176462266677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77442894369673450974844451 116164341554510176462266677)
  ·
    refine ⟨10890407020735329043337501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116164341554510176462266677 10890407020735329043337501)
    ·
      refine ⟨4083902632775748391251563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10890407020735329043337501 4083902632775748391251563)
      ·
        refine ⟨6125853949163622586877345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083902632775748391251563 6125853949163622586877345)
        ·
          refine ⟨4594390461872716940158009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6125853949163622586877345 4594390461872716940158009)
          ·
            refine ⟨3445792846404537705118507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594390461872716940158009 3445792846404537705118507)
            ·
              refine ⟨5168689269606806557677761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445792846404537705118507 5168689269606806557677761)
              ·
                refine ⟨3876516952205104918258321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5168689269606806557677761 3876516952205104918258321)
                ·
                  refine ⟨2907387714153828688693741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876516952205104918258321 2907387714153828688693741)
                  ·
                    refine ⟨1090270392807685758260153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907387714153828688693741 1090270392807685758260153)
                    ·
                      rfl

theorem cell22_3184941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3184941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184941 prefixEnd_3184941 := by exact prefixLift 3184941
  have htrace : WordTrace (prefixWord ++ tailWord_3184941) baseStart_3184941 baseEnd_3184941 := by
    simpa [prefixWord, tailWord_3184941, baseEnd_3184941] using wordTrace_append hprefix tailTrace_3184941
  have hstable : (prefixWord ++ tailWord_3184941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184941).length < 2 ^ (prefixWord ++ tailWord_3184941).sum := by decide
  have hdescent : baseEnd_3184941 < baseStart_3184941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184952 : List Nat := [2, 1, 2, 1, 3, 1, 4, 4, 1, 3]
def baseStart_3184952 : Nat := 118140960795 + 3184952 * 2 ^ 59
def prefixEnd_3184952 : Nat := 4983230072969 + 3 ^ 40 * 3184952 * 2
def baseEnd_3184952 : Nat := 1090274158332485396235119

theorem tailTrace_3184952 : CollatzResearch.WordTrace tailWord_3184952 prefixEnd_3184952 1090274158332485396235119 := by
  unfold tailWord_3184952
  simp only [CollatzResearch.WordTrace]
  refine ⟨58082371378735162670458555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77443161838313550227278073 58082371378735162670458555)
  ·
    refine ⟨87123557068102744005687833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58082371378735162670458555 87123557068102744005687833)
    ·
      refine ⟨65342667801077058004265875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87123557068102744005687833 65342667801077058004265875)
      ·
        refine ⟨98014001701615587006398813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65342667801077058004265875 98014001701615587006398813)
        ·
          refine ⟨36755250638105845127399555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98014001701615587006398813 36755250638105845127399555)
          ·
            refine ⟨55132875957158767691099333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36755250638105845127399555 55132875957158767691099333)
            ·
              refine ⟨10337414241967268942081125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55132875957158767691099333 10337414241967268942081125)
              ·
                refine ⟨1938265170368862926640211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10337414241967268942081125 1938265170368862926640211)
                ·
                  refine ⟨2907397755553294389960317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938265170368862926640211 2907397755553294389960317)
                  ·
                    refine ⟨1090274158332485396235119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907397755553294389960317 1090274158332485396235119)
                    ·
                      rfl

theorem cell22_3184952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_3184952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184952 prefixEnd_3184952 := by exact prefixLift 3184952
  have htrace : WordTrace (prefixWord ++ tailWord_3184952) baseStart_3184952 baseEnd_3184952 := by
    simpa [prefixWord, tailWord_3184952, baseEnd_3184952] using wordTrace_append hprefix tailTrace_3184952
  have hstable : (prefixWord ++ tailWord_3184952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184952).length < 2 ^ (prefixWord ++ tailWord_3184952).sum := by decide
  have hdescent : baseEnd_3184952 < baseStart_3184952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184963 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 2, 5]
def baseStart_3184963 : Nat := 118140960795 + 3184963 * 2 ^ 59
def prefixEnd_3184963 : Nat := 4983230072969 + 3 ^ 40 * 3184963 * 2
def baseEnd_3184963 : Nat := 1090277923857285034210085

theorem tailTrace_3184963 : CollatzResearch.WordTrace tailWord_3184963 prefixEnd_3184963 1090277923857285034210085 := by
  unfold tailWord_3184963
  simp only [CollatzResearch.WordTrace]
  refine ⟨116165143960430474219567543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77443429306953649479711695 116165143960430474219567543)
  ·
    refine ⟨174247715940645711329351315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116165143960430474219567543 174247715940645711329351315)
    ·
      refine ⟨261371573910968566994026973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174247715940645711329351315 261371573910968566994026973)
      ·
        refine ⟨98014340216613212622760115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261371573910968566994026973 98014340216613212622760115)
        ·
          refine ⟨147021510324919818934140173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98014340216613212622760115 147021510324919818934140173)
          ·
            refine ⟨55133066371844932100302565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147021510324919818934140173 55133066371844932100302565)
            ·
              refine ⟨10337449944720924768806731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55133066371844932100302565 10337449944720924768806731)
              ·
                refine ⟨15506174917081387153210097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10337449944720924768806731 15506174917081387153210097)
                ·
                  refine ⟨11629631187811040364907573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15506174917081387153210097 11629631187811040364907573)
                  ·
                    refine ⟨1090277923857285034210085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11629631187811040364907573 1090277923857285034210085)
                    ·
                      rfl

theorem cell22_3184963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_3184963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184963 prefixEnd_3184963 := by exact prefixLift 3184963
  have htrace : WordTrace (prefixWord ++ tailWord_3184963) baseStart_3184963 baseEnd_3184963 := by
    simpa [prefixWord, tailWord_3184963, baseEnd_3184963] using wordTrace_append hprefix tailTrace_3184963
  have hstable : (prefixWord ++ tailWord_3184963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184963).length < 2 ^ (prefixWord ++ tailWord_3184963).sum := by decide
  have hdescent : baseEnd_3184963 < baseStart_3184963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184995 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 1, 4]
def baseStart_3184995 : Nat := 118140960795 + 3184995 * 2 ^ 59
def prefixEnd_3184995 : Nat := 4983230072969 + 3 ^ 40 * 3184995 * 2
def baseEnd_3184995 : Nat := 1090288878111247617409987

theorem tailTrace_3184995 : CollatzResearch.WordTrace tailWord_3184995 prefixEnd_3184995 1090288878111247617409987 := by
  unfold tailWord_3184995
  simp only [CollatzResearch.WordTrace]
  refine ⟨116166311096314543684732439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77444207397543029123154959 116166311096314543684732439)
  ·
    refine ⟨174249466644471815527098659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116166311096314543684732439 174249466644471815527098659)
    ·
      refine ⟨261374199966707723290647989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174249466644471815527098659 261374199966707723290647989)
      ·
        refine ⟨24503831246878849058498249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261374199966707723290647989 24503831246878849058498249)
        ·
          refine ⟨18377873435159136793873687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24503831246878849058498249 18377873435159136793873687)
          ·
            refine ⟨27566810152738705190810531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18377873435159136793873687 27566810152738705190810531)
            ·
              refine ⟨41350215229108057786215797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27566810152738705190810531 41350215229108057786215797)
              ·
                refine ⟨3876582677728880417457731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41350215229108057786215797 3876582677728880417457731)
                ·
                  refine ⟨5814874016593320626186597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876582677728880417457731 5814874016593320626186597)
                  ·
                    refine ⟨1090288878111247617409987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5814874016593320626186597 1090288878111247617409987)
                    ·
                      rfl

theorem cell22_3184995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 4].length) (baseStart_3184995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3184995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3184995 prefixEnd_3184995 := by exact prefixLift 3184995
  have htrace : WordTrace (prefixWord ++ tailWord_3184995) baseStart_3184995 baseEnd_3184995 := by
    simpa [prefixWord, tailWord_3184995, baseEnd_3184995] using wordTrace_append hprefix tailTrace_3184995
  have hstable : (prefixWord ++ tailWord_3184995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184995).length < 2 ^ (prefixWord ++ tailWord_3184995).sum := by decide
  have hdescent : baseEnd_3184995 < baseStart_3184995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185010 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_3185010 : Nat := 118140960795 + 3185010 * 2 ^ 59
def prefixEnd_3185010 : Nat := 4983230072969 + 3 ^ 40 * 3185010 * 2
def baseEnd_3185010 : Nat := 363431337639264192761647

theorem tailTrace_3185010 : CollatzResearch.WordTrace tailWord_3185010 prefixEnd_3185010 363431337639264192761647 := by
  unfold tailWord_3185010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29041714547815050311632121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77444572127506800831018989 29041714547815050311632121)
  ·
    refine ⟨21781285910861287733724091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29041714547815050311632121 21781285910861287733724091)
    ·
      refine ⟨32671928866291931600586137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21781285910861287733724091 32671928866291931600586137)
      ·
        refine ⟨24503946649718948700439603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32671928866291931600586137 24503946649718948700439603)
        ·
          refine ⟨36755919974578423050659405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24503946649718948700439603 36755919974578423050659405)
          ·
            refine ⟨13783469990466908643997277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36755919974578423050659405 13783469990466908643997277)
            ·
              refine ⟨5168801246425090741498979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13783469990466908643997277 5168801246425090741498979)
              ·
                refine ⟨7753201869637636112248469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168801246425090741498979 7753201869637636112248469)
                ·
                  refine ⟨363431337639264192761647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7753201869637636112248469 363431337639264192761647)
                  ·
                    rfl

theorem cell22_3185010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_3185010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185010 prefixEnd_3185010 := by exact prefixLift 3185010
  have htrace : WordTrace (prefixWord ++ tailWord_3185010) baseStart_3185010 baseEnd_3185010 := by
    simpa [prefixWord, tailWord_3185010, baseEnd_3185010] using wordTrace_append hprefix tailTrace_3185010
  have hstable : (prefixWord ++ tailWord_3185010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185010).length < 2 ^ (prefixWord ++ tailWord_3185010).sum := by decide
  have hdescent : baseEnd_3185010 < baseStart_3185010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185076 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3185076 : Nat := 118140960795 + 3185076 * 2 ^ 59
def prefixEnd_3185076 : Nat := 4983230072969 + 3 ^ 40 * 3185076 * 2
def baseEnd_3185076 : Nat := 1090316606066590406134739

theorem tailTrace_3185076 : CollatzResearch.WordTrace tailWord_3185076 prefixEnd_3185076 1090316606066590406134739 := by
  unfold tailWord_3185076
  simp only [CollatzResearch.WordTrace]
  refine ⟨58084632704510547259215541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77446176939347396345620721 58084632704510547259215541)
  ·
    refine ⟨5445434316047863805551457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58084632704510547259215541 5445434316047863805551457)
    ·
      refine ⟨4084075737035897854163593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5445434316047863805551457 4084075737035897854163593)
      ·
        refine ⟨3063056802776923390622695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4084075737035897854163593 3063056802776923390622695)
        ·
          refine ⟨4594585204165385085934043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3063056802776923390622695 4594585204165385085934043)
          ·
            refine ⟨6891877806248077628901065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594585204165385085934043 6891877806248077628901065)
            ·
              refine ⟨5168908354686058221675799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6891877806248077628901065 5168908354686058221675799)
              ·
                refine ⟨7753362532029087332513699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168908354686058221675799 7753362532029087332513699)
                ·
                  refine ⟨11630043798043630998770549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7753362532029087332513699 11630043798043630998770549)
                  ·
                    refine ⟨1090316606066590406134739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11630043798043630998770549 1090316606066590406134739)
                    ·
                      rfl

theorem cell22_3185076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3185076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185076 prefixEnd_3185076 := by exact prefixLift 3185076
  have htrace : WordTrace (prefixWord ++ tailWord_3185076) baseStart_3185076 baseEnd_3185076 := by
    simpa [prefixWord, tailWord_3185076, baseEnd_3185076] using wordTrace_append hprefix tailTrace_3185076
  have hstable : (prefixWord ++ tailWord_3185076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185076).length < 2 ^ (prefixWord ++ tailWord_3185076).sum := by decide
  have hdescent : baseEnd_3185076 < baseStart_3185076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185134 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_3185134 : Nat := 118140960795 + 3185134 * 2 ^ 59
def prefixEnd_3185134 : Nat := 4983230072969 + 3 ^ 40 * 3185134 * 2
def baseEnd_3185134 : Nat := 363445486883965862728187

theorem tailTrace_3185134 : CollatzResearch.WordTrace tailWord_3185134 prefixEnd_3185134 363445486883965862728187 := by
  unfold tailWord_3185134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521422605351371303005307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77447587228540646949361637 14521422605351371303005307)
  ·
    refine ⟨21782133908027056954507961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14521422605351371303005307 21782133908027056954507961)
    ·
      refine ⟨16336600431020292715880971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21782133908027056954507961 16336600431020292715880971)
      ·
        refine ⟨24504900646530439073821457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16336600431020292715880971 24504900646530439073821457)
        ·
          refine ⟨18378675484897829305366093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24504900646530439073821457 18378675484897829305366093)
          ·
            refine ⟨6892003306836685989512285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18378675484897829305366093 6892003306836685989512285)
            ·
              refine ⟨2584501240063757246067107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6892003306836685989512285 2584501240063757246067107)
              ·
                refine ⟨3876751860095635869100661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584501240063757246067107 3876751860095635869100661)
                ·
                  refine ⟨363445486883965862728187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3876751860095635869100661 363445486883965862728187)
                  ·
                    rfl

theorem cell22_3185134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_3185134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185134 prefixEnd_3185134 := by exact prefixLift 3185134
  have htrace : WordTrace (prefixWord ++ tailWord_3185134) baseStart_3185134 baseEnd_3185134 := by
    simpa [prefixWord, tailWord_3185134, baseEnd_3185134] using wordTrace_append hprefix tailTrace_3185134
  have hstable : (prefixWord ++ tailWord_3185134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185134).length < 2 ^ (prefixWord ++ tailWord_3185134).sum := by decide
  have hdescent : baseEnd_3185134 < baseStart_3185134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185145 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 6]
def baseStart_3185145 : Nat := 118140960795 + 3185145 * 2 ^ 59
def prefixEnd_3185145 : Nat := 4983230072969 + 3 ^ 40 * 3185145 * 2
def baseEnd_3185145 : Nat := 363446742058899075386509

theorem tailTrace_3185145 : CollatzResearch.WordTrace tailWord_3185145 prefixEnd_3185145 363446742058899075386509 := by
  unfold tailWord_3185145
  simp only [CollatzResearch.WordTrace]
  refine ⟨116171782045771119302692889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77447854697180746201795259 116171782045771119302692889)
  ·
    refine ⟨87128836534328339477019667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116171782045771119302692889 87128836534328339477019667)
    ·
      refine ⟨130693254801492509215529501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87128836534328339477019667 130693254801492509215529501)
      ·
        refine ⟨49009970550559690955823563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130693254801492509215529501 49009970550559690955823563)
        ·
          refine ⟨73514955825839536433735345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49009970550559690955823563 73514955825839536433735345)
          ·
            refine ⟨55136216869379652325301509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73514955825839536433735345 55136216869379652325301509)
            ·
              refine ⟨10338040663008684810994033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55136216869379652325301509 10338040663008684810994033)
              ·
                refine ⟨7753530497256513608245525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10338040663008684810994033 7753530497256513608245525)
                ·
                  refine ⟨363446742058899075386509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7753530497256513608245525 363446742058899075386509)
                  ·
                    rfl

theorem cell22_3185145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_3185145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185145 prefixEnd_3185145 := by exact prefixLift 3185145
  have htrace : WordTrace (prefixWord ++ tailWord_3185145) baseStart_3185145 baseEnd_3185145 := by
    simpa [prefixWord, tailWord_3185145, baseEnd_3185145] using wordTrace_append hprefix tailTrace_3185145
  have hstable : (prefixWord ++ tailWord_3185145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185145).length < 2 ^ (prefixWord ++ tailWord_3185145).sum := by decide
  have hdescent : baseEnd_3185145 < baseStart_3185145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185160 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3185160 : Nat := 118140960795 + 3185160 * 2 ^ 59
def prefixEnd_3185160 : Nat := 4983230072969 + 3 ^ 40 * 3185160 * 2
def baseEnd_3185160 : Nat := 1090345360983242187034481

theorem tailTrace_3185160 : CollatzResearch.WordTrace tailWord_3185160 prefixEnd_3185160 1090345360983242187034481 := by
  unfold tailWord_3185160
  simp only [CollatzResearch.WordTrace]
  refine ⟨58086164570358388432244467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77448219427144517909659289 58086164570358388432244467)
  ·
    refine ⟨87129246855537582648366701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58086164570358388432244467 87129246855537582648366701)
    ·
      refine ⟨32673467570826593493137513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87129246855537582648366701 32673467570826593493137513)
      ·
        refine ⟨24505100678119945119853135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32673467570826593493137513 24505100678119945119853135)
        ·
          refine ⟨36757651017179917679779703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24505100678119945119853135 36757651017179917679779703)
          ·
            refine ⟨55136476525769876519669555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36757651017179917679779703 55136476525769876519669555)
            ·
              refine ⟨82704714788654814779504333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55136476525769876519669555 82704714788654814779504333)
              ·
                refine ⟨31014268045745555542314125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82704714788654814779504333 31014268045745555542314125)
                ·
                  refine ⟨11630350517154583328367797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31014268045745555542314125 11630350517154583328367797)
                  ·
                    refine ⟨1090345360983242187034481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11630350517154583328367797 1090345360983242187034481)
                    ·
                      rfl

theorem cell22_3185160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3185160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185160 prefixEnd_3185160 := by exact prefixLift 3185160
  have htrace : WordTrace (prefixWord ++ tailWord_3185160) baseStart_3185160 baseEnd_3185160 := by
    simpa [prefixWord, tailWord_3185160, baseEnd_3185160] using wordTrace_append hprefix tailTrace_3185160
  have hstable : (prefixWord ++ tailWord_3185160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185160).length < 2 ^ (prefixWord ++ tailWord_3185160).sum := by decide
  have hdescent : baseEnd_3185160 < baseStart_3185160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185198 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3185198 : Nat := 118140960795 + 3185198 * 2 ^ 59
def prefixEnd_3185198 : Nat := 4983230072969 + 3 ^ 40 * 3185198 * 2
def baseEnd_3185198 : Nat := 1090358369159822754584365

theorem tailTrace_3185198 : CollatzResearch.WordTrace tailWord_3185198 prefixEnd_3185198 1090358369159822754584365 := by
  unfold tailWord_3185198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521714389322388669296531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77449143409719406236248165 14521714389322388669296531)
  ·
    refine ⟨21782571583983583003944797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14521714389322388669296531 21782571583983583003944797)
    ·
      refine ⟨8168464343993843626479299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21782571583983583003944797 8168464343993843626479299)
      ·
        refine ⟨12252696515990765439718949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8168464343993843626479299 12252696515990765439718949)
        ·
          refine ⟨2297380596748268519947303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12252696515990765439718949 2297380596748268519947303)
          ·
            refine ⟨3446070895122402779920955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297380596748268519947303 3446070895122402779920955)
            ·
              refine ⟨5169106342683604169881433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446070895122402779920955 5169106342683604169881433)
              ·
                refine ⟨3876829757012703127411075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5169106342683604169881433 3876829757012703127411075)
                ·
                  refine ⟨5815244635519054691116613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876829757012703127411075 5815244635519054691116613)
                  ·
                    refine ⟨1090358369159822754584365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815244635519054691116613 1090358369159822754584365)
                    ·
                      rfl

theorem cell22_3185198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3185198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185198 prefixEnd_3185198 := by exact prefixLift 3185198
  have htrace : WordTrace (prefixWord ++ tailWord_3185198) baseStart_3185198 baseEnd_3185198 := by
    simpa [prefixWord, tailWord_3185198, baseEnd_3185198] using wordTrace_append hprefix tailTrace_3185198
  have hstable : (prefixWord ++ tailWord_3185198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185198).length < 2 ^ (prefixWord ++ tailWord_3185198).sum := by decide
  have hdescent : baseEnd_3185198 < baseStart_3185198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185252 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 5]
def baseStart_3185252 : Nat := 118140960795 + 3185252 * 2 ^ 59
def prefixEnd_3185252 : Nat := 4983230072969 + 3 ^ 40 * 3185252 * 2
def baseEnd_3185252 : Nat := 363458951487794871244733

theorem tailTrace_3185252 : CollatzResearch.WordTrace tailWord_3185252 prefixEnd_3185252 363458951487794871244733 := by
  unfold tailWord_3185252
  simp only [CollatzResearch.WordTrace]
  refine ⟨58087842328191738288419005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77450456437588984384558673 58087842328191738288419005)
  ·
    refine ⟨21782940873071901858157127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58087842328191738288419005 21782940873071901858157127)
    ·
      refine ⟨32674411309607852787235691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21782940873071901858157127 32674411309607852787235691)
      ·
        refine ⟨49011616964411779180853537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32674411309607852787235691 49011616964411779180853537)
        ·
          refine ⟨36758712723308834385640153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49011616964411779180853537 36758712723308834385640153)
          ·
            refine ⟨27569034542481625789230115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36758712723308834385640153 27569034542481625789230115)
            ·
              refine ⟨41353551813722438683845173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27569034542481625789230115 41353551813722438683845173)
              ·
                refine ⟨3876895482536478626610485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41353551813722438683845173 3876895482536478626610485)
                ·
                  refine ⟨363458951487794871244733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3876895482536478626610485 363458951487794871244733)
                  ·
                    rfl

theorem cell22_3185252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_3185252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185252 prefixEnd_3185252 := by exact prefixLift 3185252
  have htrace : WordTrace (prefixWord ++ tailWord_3185252) baseStart_3185252 baseEnd_3185252 := by
    simpa [prefixWord, tailWord_3185252, baseEnd_3185252] using wordTrace_append hprefix tailTrace_3185252
  have hstable : (prefixWord ++ tailWord_3185252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185252).length < 2 ^ (prefixWord ++ tailWord_3185252).sum := by decide
  have hdescent : baseEnd_3185252 < baseStart_3185252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185256 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 3, 3]
def baseStart_3185256 : Nat := 118140960795 + 3185256 * 2 ^ 59
def prefixEnd_3185256 : Nat := 4983230072969 + 3 ^ 40 * 3185256 * 2
def baseEnd_3185256 : Nat := 1090378223745129936634187

theorem tailTrace_3185256 : CollatzResearch.WordTrace tailWord_3185256 prefixEnd_3185256 1090378223745129936634187 := by
  unfold tailWord_3185256
  simp only [CollatzResearch.WordTrace]
  refine ⟨58087915274184492629991811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77450553698912656839989081 58087915274184492629991811)
  ·
    refine ⟨87131872911276738944987717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58087915274184492629991811 87131872911276738944987717)
    ·
      refine ⟨16337226170864388552185197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87131872911276738944987717 16337226170864388552185197)
      ·
        refine ⟨6126459814074145707069449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16337226170864388552185197 6126459814074145707069449)
        ·
          refine ⟨4594844860555609280302087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6126459814074145707069449 4594844860555609280302087)
          ·
            refine ⟨6892267290833413920453131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594844860555609280302087 6892267290833413920453131)
            ·
              refine ⟨10338400936250120880679697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892267290833413920453131 10338400936250120880679697)
              ·
                refine ⟨7753800702187590660509773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10338400936250120880679697 7753800702187590660509773)
                ·
                  refine ⟨2907675263320346497691165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7753800702187590660509773 2907675263320346497691165)
                  ·
                    refine ⟨1090378223745129936634187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907675263320346497691165 1090378223745129936634187)
                    ·
                      rfl

theorem cell22_3185256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_3185256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185256 prefixEnd_3185256 := by exact prefixLift 3185256
  have htrace : WordTrace (prefixWord ++ tailWord_3185256) baseStart_3185256 baseEnd_3185256 := by
    simpa [prefixWord, tailWord_3185256, baseEnd_3185256] using wordTrace_append hprefix tailTrace_3185256
  have hstable : (prefixWord ++ tailWord_3185256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185256).length < 2 ^ (prefixWord ++ tailWord_3185256).sum := by decide
  have hdescent : baseEnd_3185256 < baseStart_3185256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185327 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 1, 6]
def baseStart_3185327 : Nat := 118140960795 + 3185327 * 2 ^ 59
def prefixEnd_3185327 : Nat := 4983230072969 + 3 ^ 40 * 3185327 * 2
def baseEnd_3185327 : Nat := 1090402528496109418108969

theorem tailTrace_3185327 : CollatzResearch.WordTrace tailWord_3185327 prefixEnd_3185327 1090402528496109418108969 := by
  unfold tailWord_3185327
  simp only [CollatzResearch.WordTrace]
  refine ⟨116178420131111764385818235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77452280087407842923878823 116178420131111764385818235)
  ·
    refine ⟨174267630196667646578727353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116178420131111764385818235 174267630196667646578727353)
    ·
      refine ⟨130700722647500734934045515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174267630196667646578727353 130700722647500734934045515)
      ·
        refine ⟨196051083971251102401068273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130700722647500734934045515 196051083971251102401068273)
        ·
          refine ⟨147038312978438326800801205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196051083971251102401068273 147038312978438326800801205)
          ·
            refine ⟨13784841841728593137575113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147038312978438326800801205 13784841841728593137575113)
            ·
              refine ⟨10338631381296444853181335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13784841841728593137575113 10338631381296444853181335)
              ·
                refine ⟨15507947071944667279772003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10338631381296444853181335 15507947071944667279772003)
                ·
                  refine ⟨23261920607917000919658005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15507947071944667279772003 23261920607917000919658005)
                  ·
                    refine ⟨1090402528496109418108969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23261920607917000919658005 1090402528496109418108969)
                    ·
                      rfl

theorem cell22_3185327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_3185327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185327 prefixEnd_3185327 := by exact prefixLift 3185327
  have htrace : WordTrace (prefixWord ++ tailWord_3185327) baseStart_3185327 baseEnd_3185327 := by
    simpa [prefixWord, tailWord_3185327, baseEnd_3185327] using wordTrace_append hprefix tailTrace_3185327
  have hstable : (prefixWord ++ tailWord_3185327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185327).length < 2 ^ (prefixWord ++ tailWord_3185327).sum := by decide
  have hdescent : baseEnd_3185327 < baseStart_3185327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185331 : List Nat := [1, 1, 1, 2, 3, 6, 1, 3, 4]
def baseStart_3185331 : Nat := 118140960795 + 3185331 * 2 ^ 59
def prefixEnd_3185331 : Nat := 4983230072969 + 3 ^ 40 * 3185331 * 2
def baseEnd_3185331 : Nat := 363467965925951580336319

theorem tailTrace_3185331 : CollatzResearch.WordTrace tailWord_3185331 prefixEnd_3185331 363467965925951580336319 := by
  unfold tailWord_3185331
  simp only [CollatzResearch.WordTrace]
  refine ⟨116178566023097273068963847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77452377348731515379309231 116178566023097273068963847)
  ·
    refine ⟨174267849034645909603445771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116178566023097273068963847 174267849034645909603445771)
    ·
      refine ⟨261401773551968864405168657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174267849034645909603445771 261401773551968864405168657)
      ·
        refine ⟨196051330163976648303876493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261401773551968864405168657 196051330163976648303876493)
        ·
          refine ⟨73519248811491243113953685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196051330163976648303876493 73519248811491243113953685)
          ·
            refine ⟨3446214788038652020966579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73519248811491243113953685 3446214788038652020966579)
            ·
              refine ⟨5169322182057978031449869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446214788038652020966579 5169322182057978031449869)
              ·
                refine ⟨1938495818271741761793701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5169322182057978031449869 1938495818271741761793701)
                ·
                  refine ⟨363467965925951580336319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938495818271741761793701 363467965925951580336319)
                  ·
                    rfl

theorem cell22_3185331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 4].length) (baseStart_3185331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3185331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3185331 prefixEnd_3185331 := by exact prefixLift 3185331
  have htrace : WordTrace (prefixWord ++ tailWord_3185331) baseStart_3185331 baseEnd_3185331 := by
    simpa [prefixWord, tailWord_3185331, baseEnd_3185331] using wordTrace_append hprefix tailTrace_3185331
  have hstable : (prefixWord ++ tailWord_3185331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185331).length < 2 ^ (prefixWord ++ tailWord_3185331).sum := by decide
  have hdescent : baseEnd_3185331 < baseStart_3185331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
