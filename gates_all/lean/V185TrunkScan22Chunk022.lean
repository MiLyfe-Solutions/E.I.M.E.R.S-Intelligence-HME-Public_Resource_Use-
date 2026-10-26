import V185TrunkScan22Chunk021

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_195970 : List Nat := [3, 4, 2, 1, 1, 3, 8]
def baseStart_195970 : Nat := 118140960795 + 195970 * 2 ^ 59
def prefixEnd_195970 : Nat := 4983230072969 + 3 ^ 40 * 195970 * 2
def baseEnd_195970 : Nat := 2484612441029716053673

theorem tailTrace_195970 : CollatzResearch.WordTrace tailWord_195970 prefixEnd_195970 2484612441029716053673 := by
  unfold tailWord_195970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786903275010408464126341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4765075400027755904336909 1786903275010408464126341)
  ·
    refine ⟨335044364064451587023689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1786903275010408464126341 335044364064451587023689)
    ·
      refine ⟨251283273048338690267767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335044364064451587023689 251283273048338690267767)
      ·
        refine ⟨376924909572508035401651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251283273048338690267767 376924909572508035401651)
        ·
          refine ⟨565387364358762053102477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376924909572508035401651 565387364358762053102477)
          ·
            refine ⟨212020261634535769913429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565387364358762053102477 212020261634535769913429)
            ·
              refine ⟨2484612441029716053673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 212020261634535769913429 2484612441029716053673)
              ·
                rfl

theorem cell22_195970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 8].length) (baseStart_195970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_195970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_195970 prefixEnd_195970 := by exact prefixLift 195970
  have htrace : WordTrace (prefixWord ++ tailWord_195970) baseStart_195970 baseEnd_195970 := by
    simpa [prefixWord, tailWord_195970, baseEnd_195970] using wordTrace_append hprefix tailTrace_195970
  have hstable : (prefixWord ++ tailWord_195970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195970).length < 2 ^ (prefixWord ++ tailWord_195970).sum := by decide
  have hdescent : baseEnd_195970 < baseStart_195970 := by decide
  rcases family_descends (prefixWord ++ tailWord_195970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196036 : List Nat := [2, 3, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_196036 : Nat := 118140960795 + 196036 * 2 ^ 59
def prefixEnd_196036 : Nat := 4983230072969 + 3 ^ 40 * 196036 * 2
def baseEnd_196036 : Nat := 67107129056600161298969

theorem tailTrace_196036 : CollatzResearch.WordTrace tailWord_196036 prefixEnd_196036 67107129056600161298969 := by
  unfold tailWord_196036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575010158901263564203981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4766680211868351418938641 3575010158901263564203981)
  ·
    refine ⟨1340628809587973836576493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3575010158901263564203981 1340628809587973836576493)
    ·
      refine ⟨502735803595490188716185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1340628809587973836576493 502735803595490188716185)
      ·
        refine ⟨377051852696617641537139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502735803595490188716185 377051852696617641537139)
        ·
          refine ⟨565577779044926462305709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377051852696617641537139 565577779044926462305709)
          ·
            refine ⟨212091667141847423364641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565577779044926462305709 212091667141847423364641)
            ·
              refine ⟨159068750356385567523481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212091667141847423364641 159068750356385567523481)
              ·
                refine ⟨119301562767289175642611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159068750356385567523481 119301562767289175642611)
                ·
                  refine ⟨178952344150933763463917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119301562767289175642611 178952344150933763463917)
                  ·
                    refine ⟨67107129056600161298969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178952344150933763463917 67107129056600161298969)
                    ·
                      rfl

theorem cell22_196036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_196036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196036 prefixEnd_196036 := by exact prefixLift 196036
  have htrace : WordTrace (prefixWord ++ tailWord_196036) baseStart_196036 baseEnd_196036 := by
    simpa [prefixWord, tailWord_196036, baseEnd_196036] using wordTrace_append hprefix tailTrace_196036
  have hstable : (prefixWord ++ tailWord_196036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196036).length < 2 ^ (prefixWord ++ tailWord_196036).sum := by decide
  have hdescent : baseEnd_196036 < baseStart_196036 := by decide
  rcases family_descends (prefixWord ++ tailWord_196036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196041 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_196041 : Nat := 118140960795 + 196041 * 2 ^ 59
def prefixEnd_196041 : Nat := 4983230072969 + 3 ^ 40 * 196041 * 2
def baseEnd_196041 : Nat := 67108840658781814923953

theorem tailTrace_196041 : CollatzResearch.WordTrace tailWord_196041 prefixEnd_196041 67108840658781814923953 := by
  unfold tailWord_196041
  simp only [CollatzResearch.WordTrace]
  refine ⟨7150202682784412982339977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4766801788522941988226651 7150202682784412982339977)
  ·
    refine ⟨5362652012088309736754983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7150202682784412982339977 5362652012088309736754983)
    ·
      refine ⟨8043978018132464605132475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362652012088309736754983 8043978018132464605132475)
      ·
        refine ⟨12065967027198696907698713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043978018132464605132475 12065967027198696907698713)
        ·
          refine ⟨9049475270399022680774035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12065967027198696907698713 9049475270399022680774035)
          ·
            refine ⟨13574212905598534021161053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9049475270399022680774035 13574212905598534021161053)
            ·
              refine ⟨5090329839599450257935395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13574212905598534021161053 5090329839599450257935395)
              ·
                refine ⟨7635494759399175386903093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090329839599450257935395 7635494759399175386903093)
                ·
                  refine ⟨715827633693672692522165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7635494759399175386903093 715827633693672692522165)
                  ·
                    refine ⟨67108840658781814923953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 715827633693672692522165 67108840658781814923953)
                    ·
                      rfl

theorem cell22_196041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_196041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196041 prefixEnd_196041 := by exact prefixLift 196041
  have htrace : WordTrace (prefixWord ++ tailWord_196041) baseStart_196041 baseEnd_196041 := by
    simpa [prefixWord, tailWord_196041, baseEnd_196041] using wordTrace_append hprefix tailTrace_196041
  have hstable : (prefixWord ++ tailWord_196041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196041).length < 2 ^ (prefixWord ++ tailWord_196041).sum := by decide
  have hdescent : baseEnd_196041 < baseStart_196041 := by decide
  rcases family_descends (prefixWord ++ tailWord_196041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196058 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_196058 : Nat := 118140960795 + 196058 * 2 ^ 59
def prefixEnd_196058 : Nat := 4983230072969 + 3 ^ 40 * 196058 * 2
def baseEnd_196058 : Nat := 67114660106199437248901

theorem tailTrace_196058 : CollatzResearch.WordTrace tailWord_196058 prefixEnd_196058 67114660106199437248901 := by
  unfold tailWord_196058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787705680930706221427207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4767215149148549923805885 1787705680930706221427207)
  ·
    refine ⟨2681558521396059332140811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1787705680930706221427207 2681558521396059332140811)
    ·
      refine ⟨4022337782094088998211217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2681558521396059332140811 4022337782094088998211217)
      ·
        refine ⟨3016753336570566748658413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4022337782094088998211217 3016753336570566748658413)
        ·
          refine ⟨1131282501213962530746905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3016753336570566748658413 1131282501213962530746905)
          ·
            refine ⟨848461875910471898060179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131282501213962530746905 848461875910471898060179)
            ·
              refine ⟨1272692813865707847090269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848461875910471898060179 1272692813865707847090269)
              ·
                refine ⟨477259805199640442658851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1272692813865707847090269 477259805199640442658851)
                ·
                  refine ⟨715889707799460663988277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477259805199640442658851 715889707799460663988277)
                  ·
                    refine ⟨67114660106199437248901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 715889707799460663988277 67114660106199437248901)
                    ·
                      rfl

theorem cell22_196058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_196058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196058 prefixEnd_196058 := by exact prefixLift 196058
  have htrace : WordTrace (prefixWord ++ tailWord_196058) baseStart_196058 baseEnd_196058 := by
    simpa [prefixWord, tailWord_196058, baseEnd_196058] using wordTrace_append hprefix tailTrace_196058
  have hstable : (prefixWord ++ tailWord_196058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196058).length < 2 ^ (prefixWord ++ tailWord_196058).sum := by decide
  have hdescent : baseEnd_196058 < baseStart_196058 := by decide
  rcases family_descends (prefixWord ++ tailWord_196058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196154 : List Nat := [3, 1, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_196154 : Nat := 118140960795 + 196154 * 2 ^ 59
def prefixEnd_196154 : Nat := 4983230072969 + 3 ^ 40 * 196154 * 2
def baseEnd_196154 : Nat := 67147522868087186848607

theorem tailTrace_196154 : CollatzResearch.WordTrace tailWord_196154 prefixEnd_196154 67147522868087186848607 := by
  unfold tailWord_196154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788581032843758320300879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4769549420916688854135677 1788581032843758320300879)
  ·
    refine ⟨2682871549265637480451319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1788581032843758320300879 2682871549265637480451319)
    ·
      refine ⟨4024307323898456220676979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2682871549265637480451319 4024307323898456220676979)
      ·
        refine ⟨6036460985847684331015469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024307323898456220676979 6036460985847684331015469)
        ·
          refine ⟨2263672869692881624130801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6036460985847684331015469 2263672869692881624130801)
          ·
            refine ⟨1697754652269661218098101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263672869692881624130801 1697754652269661218098101)
            ·
              refine ⟨159164498650280739196697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1697754652269661218098101 159164498650280739196697)
              ·
                refine ⟨119373373987710554397523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159164498650280739196697 119373373987710554397523)
                ·
                  refine ⟨179060060981565831596285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119373373987710554397523 179060060981565831596285)
                  ·
                    refine ⟨67147522868087186848607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179060060981565831596285 67147522868087186848607)
                    ·
                      rfl

theorem cell22_196154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_196154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196154 prefixEnd_196154 := by exact prefixLift 196154
  have htrace : WordTrace (prefixWord ++ tailWord_196154) baseStart_196154 baseEnd_196154 := by
    simpa [prefixWord, tailWord_196154, baseEnd_196154] using wordTrace_append hprefix tailTrace_196154
  have hstable : (prefixWord ++ tailWord_196154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196154).length < 2 ^ (prefixWord ++ tailWord_196154).sum := by decide
  have hdescent : baseEnd_196154 < baseStart_196154 := by decide
  rcases family_descends (prefixWord ++ tailWord_196154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196180 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_196180 : Nat := 118140960795 + 196180 * 2 ^ 59
def prefixEnd_196180 : Nat := 4983230072969 + 3 ^ 40 * 196180 * 2
def baseEnd_196180 : Nat := 67156423199431785698527

theorem tailTrace_196180 : CollatzResearch.WordTrace tailWord_196180 prefixEnd_196180 67156423199431785698527 := by
  unfold tailWord_196180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577636214640419860824997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4770181619520559814433329 3577636214640419860824997)
  ·
    refine ⟨670806790245078723904687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3577636214640419860824997 670806790245078723904687)
    ·
      refine ⟨1006210185367618085857031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670806790245078723904687 1006210185367618085857031)
      ·
        refine ⟨1509315278051427128785547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006210185367618085857031 1509315278051427128785547)
        ·
          refine ⟨2263972917077140693178321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509315278051427128785547 2263972917077140693178321)
          ·
            refine ⟨1697979687807855519883741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263972917077140693178321 1697979687807855519883741)
            ·
              refine ⟨636742382927945819956403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1697979687807855519883741 636742382927945819956403)
              ·
                refine ⟨955113574391918729934605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636742382927945819956403 955113574391918729934605)
                ·
                  refine ⟨358167590396969523725477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955113574391918729934605 358167590396969523725477)
                  ·
                    refine ⟨67156423199431785698527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 358167590396969523725477 67156423199431785698527)
                    ·
                      rfl

theorem cell22_196180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_196180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196180 prefixEnd_196180 := by exact prefixLift 196180
  have htrace : WordTrace (prefixWord ++ tailWord_196180) baseStart_196180 baseEnd_196180 := by
    simpa [prefixWord, tailWord_196180, baseEnd_196180] using wordTrace_append hprefix tailTrace_196180
  have hstable : (prefixWord ++ tailWord_196180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196180).length < 2 ^ (prefixWord ++ tailWord_196180).sum := by decide
  have hdescent : baseEnd_196180 < baseStart_196180 := by decide
  rcases family_descends (prefixWord ++ tailWord_196180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196242 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_196242 : Nat := 118140960795 + 196242 * 2 ^ 59
def prefixEnd_196242 : Nat := 4983230072969 + 3 ^ 40 * 196242 * 2
def baseEnd_196242 : Nat := 67177647066484290648337

theorem tailTrace_196242 : CollatzResearch.WordTrace tailWord_196242 prefixEnd_196242 67177647066484290648337 := by
  unfold tailWord_196242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789383438764056077601745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4771689170037482873604653 1789383438764056077601745)
  ·
    refine ⟨1342037579073042058201309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1789383438764056077601745 1342037579073042058201309)
    ·
      refine ⟨503264092152390771825491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1342037579073042058201309 503264092152390771825491)
      ·
        refine ⟨754896138228586157738237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503264092152390771825491 754896138228586157738237)
        ·
          refine ⟨283086051835719809151839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 754896138228586157738237 283086051835719809151839)
          ·
            refine ⟨424629077753579713727759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283086051835719809151839 424629077753579713727759)
            ·
              refine ⟨636943616630369570591639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424629077753579713727759 636943616630369570591639)
              ·
                refine ⟨955415424945554355887459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636943616630369570591639 955415424945554355887459)
                ·
                  refine ⟨1433123137418331533831189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955415424945554355887459 1433123137418331533831189)
                  ·
                    refine ⟨67177647066484290648337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1433123137418331533831189 67177647066484290648337)
                    ·
                      rfl

theorem cell22_196242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_196242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196242 prefixEnd_196242 := by exact prefixLift 196242
  have htrace : WordTrace (prefixWord ++ tailWord_196242) baseStart_196242 baseEnd_196242 := by
    simpa [prefixWord, tailWord_196242, baseEnd_196242] using wordTrace_append hprefix tailTrace_196242
  have hstable : (prefixWord ++ tailWord_196242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196242).length < 2 ^ (prefixWord ++ tailWord_196242).sum := by decide
  have hdescent : baseEnd_196242 < baseStart_196242 := by decide
  rcases family_descends (prefixWord ++ tailWord_196242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196278 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_196278 : Nat := 118140960795 + 196278 * 2 ^ 59
def prefixEnd_196278 : Nat := 4983230072969 + 3 ^ 40 * 196278 * 2
def baseEnd_196278 : Nat := 67189970602192196748227

theorem tailTrace_196278 : CollatzResearch.WordTrace tailWord_196278 prefixEnd_196278 67189970602192196748227 := by
  unfold tailWord_196278
  simp only [CollatzResearch.WordTrace]
  refine ⟨447427923932862653669843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4772564521950534972478325 447427923932862653669843)
  ·
    refine ⟨671141885899293980504765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 447427923932862653669843 671141885899293980504765)
    ·
      refine ⟨251678207212235242689287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 671141885899293980504765 251678207212235242689287)
      ·
        refine ⟨377517310818352864033931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251678207212235242689287 377517310818352864033931)
        ·
          refine ⟨566275966227529296050897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377517310818352864033931 566275966227529296050897)
          ·
            refine ⟨424706974670646972038173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566275966227529296050897 424706974670646972038173)
            ·
              refine ⟨159265115501492614514315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424706974670646972038173 159265115501492614514315)
              ·
                refine ⟨238897673252238921771473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159265115501492614514315 238897673252238921771473)
                ·
                  refine ⟨179173254939179191328605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238897673252238921771473 179173254939179191328605)
                  ·
                    refine ⟨67189970602192196748227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179173254939179191328605 67189970602192196748227)
                    ·
                      rfl

theorem cell22_196278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_196278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196278 prefixEnd_196278 := by exact prefixLift 196278
  have htrace : WordTrace (prefixWord ++ tailWord_196278) baseStart_196278 baseEnd_196278 := by
    simpa [prefixWord, tailWord_196278, baseEnd_196278] using wordTrace_append hprefix tailTrace_196278
  have hstable : (prefixWord ++ tailWord_196278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196278).length < 2 ^ (prefixWord ++ tailWord_196278).sum := by decide
  have hdescent : baseEnd_196278 < baseStart_196278 := by decide
  rcases family_descends (prefixWord ++ tailWord_196278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196306 : List Nat := [3, 2, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_196306 : Nat := 118140960795 + 196306 * 2 ^ 59
def prefixEnd_196306 : Nat := 4983230072969 + 3 ^ 40 * 196306 * 2
def baseEnd_196306 : Nat := 67199555574409457048141

theorem tailTrace_196306 : CollatzResearch.WordTrace tailWord_196306 prefixEnd_196306 67199555574409457048141 := by
  unfold tailWord_196306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789967006706090810184193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4773245351216242160491181 1789967006706090810184193)
  ·
    refine ⟨1342475255029568107638145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1789967006706090810184193 1342475255029568107638145)
    ·
      refine ⟨1006856441272176080728609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1342475255029568107638145 1006856441272176080728609)
      ·
        refine ⟨755142330954132060546457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1006856441272176080728609 755142330954132060546457)
        ·
          refine ⟨566356748215599045409843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755142330954132060546457 566356748215599045409843)
          ·
            refine ⟨849535122323398568114765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566356748215599045409843 849535122323398568114765)
            ·
              refine ⟨318575670871274463043037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849535122323398568114765 318575670871274463043037)
              ·
                refine ⟨119465876576727923641139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318575670871274463043037 119465876576727923641139)
                ·
                  refine ⟨179198814865091885461709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119465876576727923641139 179198814865091885461709)
                  ·
                    refine ⟨67199555574409457048141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179198814865091885461709 67199555574409457048141)
                    ·
                      rfl

theorem cell22_196306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_196306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196306 prefixEnd_196306 := by exact prefixLift 196306
  have htrace : WordTrace (prefixWord ++ tailWord_196306) baseStart_196306 baseEnd_196306 := by
    simpa [prefixWord, tailWord_196306, baseEnd_196306] using wordTrace_append hprefix tailTrace_196306
  have hstable : (prefixWord ++ tailWord_196306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196306).length < 2 ^ (prefixWord ++ tailWord_196306).sum := by decide
  have hdescent : baseEnd_196306 < baseStart_196306 := by decide
  rcases family_descends (prefixWord ++ tailWord_196306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196323 : List Nat := [1, 1, 1, 7, 2, 1, 3, 2, 1, 3]
def baseStart_196323 : Nat := 118140960795 + 196323 * 2 ^ 59
def prefixEnd_196323 : Nat := 4983230072969 + 3 ^ 40 * 196323 * 2
def baseEnd_196323 : Nat := 67205375021827079373089

theorem tailTrace_196323 : CollatzResearch.WordTrace tailWord_196323 prefixEnd_196323 67205375021827079373089 := by
  unfold tailWord_196323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160488067762775144105623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4773658711841850096070415 7160488067762775144105623)
  ·
    refine ⟨10740732101644162716158435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7160488067762775144105623 10740732101644162716158435)
    ·
      refine ⟨16111098152466244074237653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740732101644162716158435 16111098152466244074237653)
      ·
        refine ⟨377603862948427595489945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16111098152466244074237653 377603862948427595489945)
        ·
          refine ⟨283202897211320696617459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377603862948427595489945 283202897211320696617459)
          ·
            refine ⟨424804345816981044926189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283202897211320696617459 424804345816981044926189)
            ·
              refine ⟨159301629681367891847321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424804345816981044926189 159301629681367891847321)
              ·
                refine ⟨119476222261025918885491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159301629681367891847321 119476222261025918885491)
                ·
                  refine ⟨179214333391538878328237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119476222261025918885491 179214333391538878328237)
                  ·
                    refine ⟨67205375021827079373089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179214333391538878328237 67205375021827079373089)
                    ·
                      rfl

theorem cell22_196323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 3].length) (baseStart_196323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196323 prefixEnd_196323 := by exact prefixLift 196323
  have htrace : WordTrace (prefixWord ++ tailWord_196323) baseStart_196323 baseEnd_196323 := by
    simpa [prefixWord, tailWord_196323, baseEnd_196323] using wordTrace_append hprefix tailTrace_196323
  have hstable : (prefixWord ++ tailWord_196323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196323).length < 2 ^ (prefixWord ++ tailWord_196323).sum := by decide
  have hdescent : baseEnd_196323 < baseStart_196323 := by decide
  rcases family_descends (prefixWord ++ tailWord_196323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196362 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_196362 : Nat := 118140960795 + 196362 * 2 ^ 59
def prefixEnd_196362 : Nat := 4983230072969 + 3 ^ 40 * 196362 * 2
def baseEnd_196362 : Nat := 67218725518843977647969

theorem tailTrace_196362 : CollatzResearch.WordTrace tailWord_196362 prefixEnd_196362 67218725518843977647969 := by
  unfold tailWord_196362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790477628655371201193835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4774607009747656536516893 1790477628655371201193835)
  ·
    refine ⟨2685716442983056801790753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1790477628655371201193835 2685716442983056801790753)
    ·
      refine ⟨2014287332237292601343065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2685716442983056801790753 2014287332237292601343065)
      ·
        refine ⟨1510715499177969451007299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2014287332237292601343065 1510715499177969451007299)
        ·
          refine ⟨2266073248766954176510949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510715499177969451007299 2266073248766954176510949)
          ·
            refine ⟨424888734143803908095803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2266073248766954176510949 424888734143803908095803)
            ·
              refine ⟨637333101215705862143705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424888734143803908095803 637333101215705862143705)
              ·
                refine ⟨477999825911779396607779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637333101215705862143705 477999825911779396607779)
                ·
                  refine ⟨716999738867669094911669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477999825911779396607779 716999738867669094911669)
                  ·
                    refine ⟨67218725518843977647969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 716999738867669094911669 67218725518843977647969)
                    ·
                      rfl

theorem cell22_196362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_196362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196362 prefixEnd_196362 := by exact prefixLift 196362
  have htrace : WordTrace (prefixWord ++ tailWord_196362) baseStart_196362 baseEnd_196362 := by
    simpa [prefixWord, tailWord_196362, baseEnd_196362] using wordTrace_append hprefix tailTrace_196362
  have hstable : (prefixWord ++ tailWord_196362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196362).length < 2 ^ (prefixWord ++ tailWord_196362).sum := by decide
  have hdescent : baseEnd_196362 < baseStart_196362 := by decide
  rcases family_descends (prefixWord ++ tailWord_196362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196375 : List Nat := [1, 1, 3, 4, 2, 11]
def baseStart_196375 : Nat := 118140960795 + 196375 * 2 ^ 59
def prefixEnd_196375 : Nat := 4983230072969 + 3 ^ 40 * 196375 * 2
def baseEnd_196375 : Nat := 829915749191558976209

theorem tailTrace_196375 : CollatzResearch.WordTrace tailWord_196375 prefixEnd_196375 829915749191558976209 := by
  unfold tailWord_196375
  simp only [CollatzResearch.WordTrace]
  refine ⟨7162384663574388024998579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4774923109049592016665719 7162384663574388024998579)
  ·
    refine ⟨10743576995361582037497869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7162384663574388024998579 10743576995361582037497869)
    ·
      refine ⟨4028841373260593264061701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10743576995361582037497869 4028841373260593264061701)
      ·
        refine ⟨755407757486361237011569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4028841373260593264061701 755407757486361237011569)
        ·
          refine ⟨566555818114770927758677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755407757486361237011569 566555818114770927758677)
          ·
            refine ⟨829915749191558976209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 566555818114770927758677 829915749191558976209)
            ·
              rfl

theorem cell22_196375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 11].length) (baseStart_196375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196375 prefixEnd_196375 := by exact prefixLift 196375
  have htrace : WordTrace (prefixWord ++ tailWord_196375) baseStart_196375 baseEnd_196375 := by
    simpa [prefixWord, tailWord_196375, baseEnd_196375] using wordTrace_append hprefix tailTrace_196375
  have hstable : (prefixWord ++ tailWord_196375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196375).length < 2 ^ (prefixWord ++ tailWord_196375).sum := by decide
  have hdescent : baseEnd_196375 < baseStart_196375 := by decide
  rcases family_descends (prefixWord ++ tailWord_196375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196392 : List Nat := [2, 1, 5, 1, 1, 2, 3, 7]
def baseStart_196392 : Nat := 118140960795 + 196392 * 2 ^ 59
def prefixEnd_196392 : Nat := 4983230072969 + 3 ^ 40 * 196392 * 2
def baseEnd_196392 : Nat := 7469888347992655488653

theorem tailTrace_196392 : CollatzResearch.WordTrace tailWord_196392 prefixEnd_196392 7469888347992655488653 := by
  unfold tailWord_196392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581502352256399964183715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4775336469675199952244953 3581502352256399964183715)
  ·
    refine ⟨5372253528384599946275573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3581502352256399964183715 5372253528384599946275573)
    ·
      refine ⟨503648768286056244963335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5372253528384599946275573 503648768286056244963335)
      ·
        refine ⟨755473152429084367445003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503648768286056244963335 755473152429084367445003)
        ·
          refine ⟨1133209728643626551167505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755473152429084367445003 1133209728643626551167505)
          ·
            refine ⟨849907296482719913375629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1133209728643626551167505 849907296482719913375629)
            ·
              refine ⟨318715236181019967515861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849907296482719913375629 318715236181019967515861)
              ·
                refine ⟨7469888347992655488653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 318715236181019967515861 7469888347992655488653)
                ·
                  rfl

theorem cell22_196392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_196392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196392 prefixEnd_196392 := by exact prefixLift 196392
  have htrace : WordTrace (prefixWord ++ tailWord_196392) baseStart_196392 baseEnd_196392 := by
    simpa [prefixWord, tailWord_196392, baseEnd_196392] using wordTrace_append hprefix tailTrace_196392
  have hstable : (prefixWord ++ tailWord_196392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196392).length < 2 ^ (prefixWord ++ tailWord_196392).sum := by decide
  have hdescent : baseEnd_196392 < baseStart_196392 := by decide
  rcases family_descends (prefixWord ++ tailWord_196392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196437 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 7]
def baseStart_196437 : Nat := 118140960795 + 196437 * 2 ^ 59
def prefixEnd_196437 : Nat := 4983230072969 + 3 ^ 40 * 196437 * 2
def baseEnd_196437 : Nat := 22414799850522927340913

theorem tailTrace_196437 : CollatzResearch.WordTrace tailWord_196437 prefixEnd_196437 22414799850522927340913 := by
  unfold tailWord_196437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164645989349772613755565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4776430659566515075837043 7164645989349772613755565)
  ·
    refine ⟨2686742246006164730158337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7164645989349772613755565 2686742246006164730158337)
    ·
      refine ⟨2015056684504623547618753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2686742246006164730158337 2015056684504623547618753)
      ·
        refine ⟨1511292513378467660714065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2015056684504623547618753 1511292513378467660714065)
        ·
          refine ⟨1133469385033850745535549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1511292513378467660714065 1133469385033850745535549)
          ·
            refine ⟨425051019387694029575831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1133469385033850745535549 425051019387694029575831)
            ·
              refine ⟨637576529081541044363747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425051019387694029575831 637576529081541044363747)
              ·
                refine ⟨956364793622311566545621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637576529081541044363747 956364793622311566545621)
                ·
                  refine ⟨22414799850522927340913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 956364793622311566545621 22414799850522927340913)
                  ·
                    rfl

theorem cell22_196437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_196437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196437 prefixEnd_196437 := by exact prefixLift 196437
  have htrace : WordTrace (prefixWord ++ tailWord_196437) baseStart_196437 baseEnd_196437 := by
    simpa [prefixWord, tailWord_196437, baseEnd_196437] using wordTrace_append hprefix tailTrace_196437
  have hstable : (prefixWord ++ tailWord_196437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196437).length < 2 ^ (prefixWord ++ tailWord_196437).sum := by decide
  have hdescent : baseEnd_196437 < baseStart_196437 := by decide
  rcases family_descends (prefixWord ++ tailWord_196437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196484 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_196484 : Nat := 118140960795 + 196484 * 2 ^ 59
def prefixEnd_196484 : Nat := 4983230072969 + 3 ^ 40 * 196484 * 2
def baseEnd_196484 : Nat := 67260488612076326097595

theorem tailTrace_196484 : CollatzResearch.WordTrace tailWord_196484 prefixEnd_196484 67260488612076326097595 := by
  unfold tailWord_196484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583180110089749820358253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4777573480119666427144337 3583180110089749820358253)
  ·
    refine ⟨1343692541283656182634345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3583180110089749820358253 1343692541283656182634345)
    ·
      refine ⟨1007769405962742136975759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1343692541283656182634345 1007769405962742136975759)
      ·
        refine ⟨1511654108944113205463639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007769405962742136975759 1511654108944113205463639)
        ·
          refine ⟨2267481163416169808195459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511654108944113205463639 2267481163416169808195459)
          ·
            refine ⟨3401221745124254712293189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267481163416169808195459 3401221745124254712293189)
            ·
              refine ⟨637729077210797758554973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3401221745124254712293189 637729077210797758554973)
              ·
                refine ⟨239148403954049159458115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637729077210797758554973 239148403954049159458115)
                ·
                  refine ⟨358722605931073739187173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239148403954049159458115 358722605931073739187173)
                  ·
                    refine ⟨67260488612076326097595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 358722605931073739187173 67260488612076326097595)
                    ·
                      rfl

theorem cell22_196484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_196484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196484 prefixEnd_196484 := by exact prefixLift 196484
  have htrace : WordTrace (prefixWord ++ tailWord_196484) baseStart_196484 baseEnd_196484 := by
    simpa [prefixWord, tailWord_196484, baseEnd_196484] using wordTrace_append hprefix tailTrace_196484
  have hstable : (prefixWord ++ tailWord_196484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196484).length < 2 ^ (prefixWord ++ tailWord_196484).sum := by decide
  have hdescent : baseEnd_196484 < baseStart_196484 := by decide
  rcases family_descends (prefixWord ++ tailWord_196484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196512 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_196512 : Nat := 118140960795 + 196512 * 2 ^ 59
def prefixEnd_196512 : Nat := 4983230072969 + 3 ^ 40 * 196512 * 2
def baseEnd_196512 : Nat := 67270073584293586397509

theorem tailTrace_196512 : CollatzResearch.WordTrace tailWord_196512 prefixEnd_196512 67270073584293586397509 := by
  unfold tailWord_196512
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583690732039030211367895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4778254309385373615157193 3583690732039030211367895)
  ·
    refine ⟨5375536098058545317051843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583690732039030211367895 5375536098058545317051843)
    ·
      refine ⟨8063304147087817975577765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375536098058545317051843 8063304147087817975577765)
      ·
        refine ⟨1511869527578965870420831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8063304147087817975577765 1511869527578965870420831)
        ·
          refine ⟨2267804291368448805631247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511869527578965870420831 2267804291368448805631247)
          ·
            refine ⟨3401706437052673208446871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267804291368448805631247 3401706437052673208446871)
            ·
              refine ⟨5102559655579009812670307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401706437052673208446871 5102559655579009812670307)
              ·
                refine ⟨7653839483368514719005461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102559655579009812670307 7653839483368514719005461)
                ·
                  refine ⟨358773725782899127453381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7653839483368514719005461 358773725782899127453381)
                  ·
                    refine ⟨67270073584293586397509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 358773725782899127453381 67270073584293586397509)
                    ·
                      rfl

theorem cell22_196512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_196512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196512 prefixEnd_196512 := by exact prefixLift 196512
  have htrace : WordTrace (prefixWord ++ tailWord_196512) baseStart_196512 baseEnd_196512 := by
    simpa [prefixWord, tailWord_196512, baseEnd_196512] using wordTrace_append hprefix tailTrace_196512
  have hstable : (prefixWord ++ tailWord_196512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196512).length < 2 ^ (prefixWord ++ tailWord_196512).sum := by decide
  have hdescent : baseEnd_196512 < baseStart_196512 := by decide
  rcases family_descends (prefixWord ++ tailWord_196512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196529 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_196529 : Nat := 118140960795 + 196529 * 2 ^ 59
def prefixEnd_196529 : Nat := 4983230072969 + 3 ^ 40 * 196529 * 2
def baseEnd_196529 : Nat := 67275893031711208722457

theorem tailTrace_196529 : CollatzResearch.WordTrace tailWord_196529 prefixEnd_196529 67275893031711208722457 := by
  unfold tailWord_196529
  simp only [CollatzResearch.WordTrace]
  refine ⟨7168001505016472326104641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4778667670010981550736427 7168001505016472326104641)
  ·
    refine ⟨5376001128762354244578481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7168001505016472326104641 5376001128762354244578481)
    ·
      refine ⟨4032000846571765683433861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5376001128762354244578481 4032000846571765683433861)
      ·
        refine ⟨756000158732206065643849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4032000846571765683433861 756000158732206065643849)
        ·
          refine ⟨567000119049154549232887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756000158732206065643849 567000119049154549232887)
          ·
            refine ⟨850500178573731823849331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567000119049154549232887 850500178573731823849331)
            ·
              refine ⟨1275750267860597735773997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850500178573731823849331 1275750267860597735773997)
              ·
                refine ⟨478406350447724150915249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1275750267860597735773997 478406350447724150915249)
                ·
                  refine ⟨358804762835793113186437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478406350447724150915249 358804762835793113186437)
                  ·
                    refine ⟨67275893031711208722457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 358804762835793113186437 67275893031711208722457)
                    ·
                      rfl

theorem cell22_196529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_196529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196529 prefixEnd_196529 := by exact prefixLift 196529
  have htrace : WordTrace (prefixWord ++ tailWord_196529) baseStart_196529 baseEnd_196529 := by
    simpa [prefixWord, tailWord_196529, baseEnd_196529] using wordTrace_append hprefix tailTrace_196529
  have hstable : (prefixWord ++ tailWord_196529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196529).length < 2 ^ (prefixWord ++ tailWord_196529).sum := by decide
  have hdescent : baseEnd_196529 < baseStart_196529 := by decide
  rcases family_descends (prefixWord ++ tailWord_196529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196559 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 3, 3]
def baseStart_196559 : Nat := 118140960795 + 196559 * 2 ^ 59
def prefixEnd_196559 : Nat := 4983230072969 + 3 ^ 40 * 196559 * 2
def baseEnd_196559 : Nat := 67286162644801130472365

theorem tailTrace_196559 : CollatzResearch.WordTrace tailWord_196559 prefixEnd_196559 67286162644801130472365 := by
  unfold tailWord_196559
  simp only [CollatzResearch.WordTrace]
  refine ⟨7169095694907787449696731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4779397129938524966464487 7169095694907787449696731)
  ·
    refine ⟨10753643542361681174545097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7169095694907787449696731 10753643542361681174545097)
    ·
      refine ⟨8065232656771260880908823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10753643542361681174545097 8065232656771260880908823)
      ·
        refine ⟨12097848985156891321363235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8065232656771260880908823 12097848985156891321363235)
        ·
          refine ⟨18146773477735336982044853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12097848985156891321363235 18146773477735336982044853)
          ·
            refine ⟨1701260013537687842066705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18146773477735336982044853 1701260013537687842066705)
            ·
              refine ⟨1275945010153265881550029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701260013537687842066705 1275945010153265881550029)
              ·
                refine ⟨478479378807474705581261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1275945010153265881550029 478479378807474705581261)
                ·
                  refine ⟨179429767052803014592973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478479378807474705581261 179429767052803014592973)
                  ·
                    refine ⟨67286162644801130472365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179429767052803014592973 67286162644801130472365)
                    ·
                      rfl

theorem cell22_196559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_196559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196559 prefixEnd_196559 := by exact prefixLift 196559
  have htrace : WordTrace (prefixWord ++ tailWord_196559) baseStart_196559 baseEnd_196559 := by
    simpa [prefixWord, tailWord_196559, baseEnd_196559] using wordTrace_append hprefix tailTrace_196559
  have hstable : (prefixWord ++ tailWord_196559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196559).length < 2 ^ (prefixWord ++ tailWord_196559).sum := by decide
  have hdescent : baseEnd_196559 < baseStart_196559 := by decide
  rcases family_descends (prefixWord ++ tailWord_196559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196578 : List Nat := [3, 3, 3, 1, 2, 1, 3, 6]
def baseStart_196578 : Nat := 118140960795 + 196578 * 2 ^ 59
def prefixEnd_196578 : Nat := 4983230072969 + 3 ^ 40 * 196578 * 2
def baseEnd_196578 : Nat := 7476962970343490471923

theorem tailTrace_196578 : CollatzResearch.WordTrace tailWord_196578 prefixEnd_196578 7476962970343490471923 := by
  unfold tailWord_196578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1792447170459738423659597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4779859121225969129758925 1792447170459738423659597)
  ·
    refine ⟨672167688922401908872349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1792447170459738423659597 672167688922401908872349)
    ·
      refine ⟨252062883345900715827131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 672167688922401908872349 252062883345900715827131)
      ·
        refine ⟨378094325018851073740697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252062883345900715827131 378094325018851073740697)
        ·
          refine ⟨283570743764138305305523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378094325018851073740697 283570743764138305305523)
          ·
            refine ⟨425356115646207457958285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283570743764138305305523 425356115646207457958285)
            ·
              refine ⟨159508543367327796734357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425356115646207457958285 159508543367327796734357)
              ·
                refine ⟨7476962970343490471923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159508543367327796734357 7476962970343490471923)
                ·
                  rfl

theorem cell22_196578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_196578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196578 prefixEnd_196578 := by exact prefixLift 196578
  have htrace : WordTrace (prefixWord ++ tailWord_196578) baseStart_196578 baseEnd_196578 := by
    simpa [prefixWord, tailWord_196578, baseEnd_196578] using wordTrace_append hprefix tailTrace_196578
  have hstable : (prefixWord ++ tailWord_196578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196578).length < 2 ^ (prefixWord ++ tailWord_196578).sum := by decide
  have hdescent : baseEnd_196578 < baseStart_196578 := by decide
  rcases family_descends (prefixWord ++ tailWord_196578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196606 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_196606 : Nat := 118140960795 + 196606 * 2 ^ 59
def prefixEnd_196606 : Nat := 4983230072969 + 3 ^ 40 * 196606 * 2
def baseEnd_196606 : Nat := 22434083901769558182407

theorem tailTrace_196606 : CollatzResearch.WordTrace tailWord_196606 prefixEnd_196606 22434083901769558182407 := by
  unfold tailWord_196606
  simp only [CollatzResearch.WordTrace]
  refine ⟨896351240717189309582209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4780539950491676317771781 896351240717189309582209)
  ·
    refine ⟨672263430537891982186657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 896351240717189309582209 672263430537891982186657)
    ·
      refine ⟨504197572903418986639993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 672263430537891982186657 504197572903418986639993)
      ·
        refine ⟨378148179677564239979995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504197572903418986639993 378148179677564239979995)
        ·
          refine ⟨567222269516346359969993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378148179677564239979995 567222269516346359969993)
          ·
            refine ⟨425416702137259769977495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567222269516346359969993 425416702137259769977495)
            ·
              refine ⟨638125053205889654966243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425416702137259769977495 638125053205889654966243)
              ·
                refine ⟨957187579808834482449365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638125053205889654966243 957187579808834482449365)
                ·
                  refine ⟨22434083901769558182407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 957187579808834482449365 22434083901769558182407)
                  ·
                    rfl

theorem cell22_196606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_196606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196606 prefixEnd_196606 := by exact prefixLift 196606
  have htrace : WordTrace (prefixWord ++ tailWord_196606) baseStart_196606 baseEnd_196606 := by
    simpa [prefixWord, tailWord_196606, baseEnd_196606] using wordTrace_append hprefix tailTrace_196606
  have hstable : (prefixWord ++ tailWord_196606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196606).length < 2 ^ (prefixWord ++ tailWord_196606).sum := by decide
  have hdescent : baseEnd_196606 < baseStart_196606 := by decide
  rcases family_descends (prefixWord ++ tailWord_196606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196634 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_196634 : Nat := 118140960795 + 196634 * 2 ^ 59
def prefixEnd_196634 : Nat := 4983230072969 + 3 ^ 40 * 196634 * 2
def baseEnd_196634 : Nat := 22437278892508644949045

theorem tailTrace_196634 : CollatzResearch.WordTrace tailWord_196634 prefixEnd_196634 22437278892508644949045 := by
  unfold tailWord_196634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1792957792409018814669239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4781220779757383505784637 1792957792409018814669239)
  ·
    refine ⟨2689436688613528222003859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1792957792409018814669239 2689436688613528222003859)
    ·
      refine ⟨4034155032920292333005789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2689436688613528222003859 4034155032920292333005789)
      ·
        refine ⟨1512808137345109624877171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4034155032920292333005789 1512808137345109624877171)
        ·
          refine ⟨2269212206017664437315757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1512808137345109624877171 2269212206017664437315757)
          ·
            refine ⟨850954577256624163993409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2269212206017664437315757 850954577256624163993409)
            ·
              refine ⟨638215932942468122995057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850954577256624163993409 638215932942468122995057)
              ·
                refine ⟨478661949706851092246293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638215932942468122995057 478661949706851092246293)
                ·
                  refine ⟨22437278892508644949045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 478661949706851092246293 22437278892508644949045)
                  ·
                    rfl

theorem cell22_196634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_196634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196634 prefixEnd_196634 := by exact prefixLift 196634
  have htrace : WordTrace (prefixWord ++ tailWord_196634) baseStart_196634 baseEnd_196634 := by
    simpa [prefixWord, tailWord_196634, baseEnd_196634] using wordTrace_append hprefix tailTrace_196634
  have hstable : (prefixWord ++ tailWord_196634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196634).length < 2 ^ (prefixWord ++ tailWord_196634).sum := by decide
  have hdescent : baseEnd_196634 < baseStart_196634 := by decide
  rcases family_descends (prefixWord ++ tailWord_196634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196636 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_196636 : Nat := 118140960795 + 196636 * 2 ^ 59
def prefixEnd_196636 : Nat := 4983230072969 + 3 ^ 40 * 196636 * 2
def baseEnd_196636 : Nat := 67312521318398596297129

theorem tailTrace_196636 : CollatzResearch.WordTrace tailWord_196636 prefixEnd_196636 67312521318398596297129 := by
  unfold tailWord_196636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585952057814414800124881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4781269410419219733499841 3585952057814414800124881)
  ·
    refine ⟨2689464043360811100093661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3585952057814414800124881 2689464043360811100093661)
    ·
      refine ⟨1008549016260304162535123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2689464043360811100093661 1008549016260304162535123)
      ·
        refine ⟨1512823524390456243802685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008549016260304162535123 1512823524390456243802685)
        ·
          refine ⟨567308821646421091426007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1512823524390456243802685 567308821646421091426007)
          ·
            refine ⟨850963232469631637139011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567308821646421091426007 850963232469631637139011)
            ·
              refine ⟨1276444848704447455708517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850963232469631637139011 1276444848704447455708517)
              ·
                refine ⟨239333409132083897945347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1276444848704447455708517 239333409132083897945347)
                ·
                  refine ⟨359000113698125846918021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239333409132083897945347 359000113698125846918021)
                  ·
                    refine ⟨67312521318398596297129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 359000113698125846918021 67312521318398596297129)
                    ·
                      rfl

theorem cell22_196636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_196636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196636 prefixEnd_196636 := by exact prefixLift 196636
  have htrace : WordTrace (prefixWord ++ tailWord_196636) baseStart_196636 baseEnd_196636 := by
    simpa [prefixWord, tailWord_196636, baseEnd_196636] using wordTrace_append hprefix tailTrace_196636
  have hstable : (prefixWord ++ tailWord_196636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196636).length < 2 ^ (prefixWord ++ tailWord_196636).sum := by decide
  have hdescent : baseEnd_196636 < baseStart_196636 := by decide
  rcases family_descends (prefixWord ++ tailWord_196636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196666 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_196666 : Nat := 118140960795 + 196666 * 2 ^ 59
def prefixEnd_196666 : Nat := 4983230072969 + 3 ^ 40 * 196666 * 2
def baseEnd_196666 : Nat := 67322790931488518047037

theorem tailTrace_196666 : CollatzResearch.WordTrace tailWord_196666 prefixEnd_196666 67322790931488518047037 := by
  unfold tailWord_196666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1793249576380036180960463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4781998870346763149227901 1793249576380036180960463)
  ·
    refine ⟨2689874364570054271440695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1793249576380036180960463 2689874364570054271440695)
    ·
      refine ⟨4034811546855081407161043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2689874364570054271440695 4034811546855081407161043)
      ·
        refine ⟨6052217320282622110741565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4034811546855081407161043 6052217320282622110741565)
        ·
          refine ⟨2269581495105983291528087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6052217320282622110741565 2269581495105983291528087)
          ·
            refine ⟨3404372242658974937292131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269581495105983291528087 3404372242658974937292131)
            ·
              refine ⟨5106558363988462405938197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404372242658974937292131 5106558363988462405938197)
              ·
                refine ⟨239369923311959175278353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5106558363988462405938197 239369923311959175278353)
                ·
                  refine ⟨179527442483969381458765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239369923311959175278353 179527442483969381458765)
                  ·
                    refine ⟨67322790931488518047037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179527442483969381458765 67322790931488518047037)
                    ·
                      rfl

theorem cell22_196666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_196666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196666 prefixEnd_196666 := by exact prefixLift 196666
  have htrace : WordTrace (prefixWord ++ tailWord_196666) baseStart_196666 baseEnd_196666 := by
    simpa [prefixWord, tailWord_196666, baseEnd_196666] using wordTrace_append hprefix tailTrace_196666
  have hstable : (prefixWord ++ tailWord_196666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196666).length < 2 ^ (prefixWord ++ tailWord_196666).sum := by decide
  have hdescent : baseEnd_196666 < baseStart_196666 := by decide
  rcases family_descends (prefixWord ++ tailWord_196666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196668 : List Nat := [2, 2, 2, 2, 2, 1, 5, 2, 4]
def baseStart_196668 : Nat := 118140960795 + 196668 * 2 ^ 59
def prefixEnd_196668 : Nat := 4983230072969 + 3 ^ 40 * 196668 * 2
def baseEnd_196668 : Nat := 22441158524120393165677

theorem tailTrace_196668 : CollatzResearch.WordTrace tailWord_196668 prefixEnd_196668 22441158524120393165677 := by
  unfold tailWord_196668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3586535625756449532707329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4782047501008599376943105 3586535625756449532707329)
  ·
    refine ⟨2689901719317337149530497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3586535625756449532707329 2689901719317337149530497)
    ·
      refine ⟨2017426289488002862147873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2689901719317337149530497 2017426289488002862147873)
      ·
        refine ⟨1513069717116002146610905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2017426289488002862147873 1513069717116002146610905)
        ·
          refine ⟨1134802287837001609958179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1513069717116002146610905 1134802287837001609958179)
          ·
            refine ⟨1702203431755502414937269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134802287837001609958179 1702203431755502414937269)
            ·
              refine ⟨159581571727078351400369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1702203431755502414937269 159581571727078351400369)
              ·
                refine ⟨119686178795308763550277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159581571727078351400369 119686178795308763550277)
                ·
                  refine ⟨22441158524120393165677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119686178795308763550277 22441158524120393165677)
                  ·
                    rfl

theorem cell22_196668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_196668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196668 prefixEnd_196668 := by exact prefixLift 196668
  have htrace : WordTrace (prefixWord ++ tailWord_196668) baseStart_196668 baseEnd_196668 := by
    simpa [prefixWord, tailWord_196668, baseEnd_196668] using wordTrace_append hprefix tailTrace_196668
  have hstable : (prefixWord ++ tailWord_196668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196668).length < 2 ^ (prefixWord ++ tailWord_196668).sum := by decide
  have hdescent : baseEnd_196668 < baseStart_196668 := by decide
  rcases family_descends (prefixWord ++ tailWord_196668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196679 : List Nat := [1, 1, 4, 1, 3, 1, 4, 7]
def baseStart_196679 : Nat := 118140960795 + 196679 * 2 ^ 59
def prefixEnd_196679 : Nat := 4983230072969 + 3 ^ 40 * 196679 * 2
def baseEnd_196679 : Nat := 7480804566351201941333

theorem tailTrace_196679 : CollatzResearch.WordTrace tailWord_196679 prefixEnd_196679 7480804566351201941333 := by
  unfold tailWord_196679
  simp only [CollatzResearch.WordTrace]
  refine ⟨7173472454473047944065091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4782314969648698629376727 7173472454473047944065091)
  ·
    refine ⟨10760208681709571916097637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7173472454473047944065091 10760208681709571916097637)
    ·
      refine ⟨2017539127820544734268307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10760208681709571916097637 2017539127820544734268307)
      ·
        refine ⟨3026308691730817101402461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2017539127820544734268307 3026308691730817101402461)
        ·
          refine ⟨1134865759399056413025923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3026308691730817101402461 1134865759399056413025923)
          ·
            refine ⟨1702298639098584619538885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134865759399056413025923 1702298639098584619538885)
            ·
              refine ⟨319180994830984616163541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1702298639098584619538885 319180994830984616163541)
              ·
                refine ⟨7480804566351201941333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 319180994830984616163541 7480804566351201941333)
                ·
                  rfl

theorem cell22_196679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 7].length) (baseStart_196679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196679 prefixEnd_196679 := by exact prefixLift 196679
  have htrace : WordTrace (prefixWord ++ tailWord_196679) baseStart_196679 baseEnd_196679 := by
    simpa [prefixWord, tailWord_196679, baseEnd_196679] using wordTrace_append hprefix tailTrace_196679
  have hstable : (prefixWord ++ tailWord_196679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196679).length < 2 ^ (prefixWord ++ tailWord_196679).sum := by decide
  have hdescent : baseEnd_196679 < baseStart_196679 := by decide
  rcases family_descends (prefixWord ++ tailWord_196679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196726 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_196726 : Nat := 118140960795 + 196726 * 2 ^ 59
def prefixEnd_196726 : Nat := 4983230072969 + 3 ^ 40 * 196726 * 2
def baseEnd_196726 : Nat := 67343330157668361546853

theorem tailTrace_196726 : CollatzResearch.WordTrace tailWord_196726 prefixEnd_196726 67343330157668361546853 := by
  unfold tailWord_196726
  simp only [CollatzResearch.WordTrace]
  refine ⟨448449167831423435689127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4783457790201849980684021 448449167831423435689127)
  ·
    refine ⟨672673751747135153533691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 448449167831423435689127 672673751747135153533691)
    ·
      refine ⟨1009010627620702730300537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672673751747135153533691 1009010627620702730300537)
      ·
        refine ⟨756757970715527047725403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1009010627620702730300537 756757970715527047725403)
        ·
          refine ⟨1135136956073290571588105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756757970715527047725403 1135136956073290571588105)
          ·
            refine ⟨851352717054967928691079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135136956073290571588105 851352717054967928691079)
            ·
              refine ⟨1277029075582451893036619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851352717054967928691079 1277029075582451893036619)
              ·
                refine ⟨1915543613373677839554929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277029075582451893036619 1915543613373677839554929)
                ·
                  refine ⟨1436657710030258379666197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1915543613373677839554929 1436657710030258379666197)
                  ·
                    refine ⟨67343330157668361546853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1436657710030258379666197 67343330157668361546853)
                    ·
                      rfl

theorem cell22_196726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_196726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196726 prefixEnd_196726 := by exact prefixLift 196726
  have htrace : WordTrace (prefixWord ++ tailWord_196726) baseStart_196726 baseEnd_196726 := by
    simpa [prefixWord, tailWord_196726, baseEnd_196726] using wordTrace_append hprefix tailTrace_196726
  have hstable : (prefixWord ++ tailWord_196726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196726).length < 2 ^ (prefixWord ++ tailWord_196726).sum := by decide
  have hdescent : baseEnd_196726 < baseStart_196726 := by decide
  rcases family_descends (prefixWord ++ tailWord_196726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196739 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 1, 7]
def baseStart_196739 : Nat := 118140960795 + 196739 * 2 ^ 59
def prefixEnd_196739 : Nat := 4983230072969 + 3 ^ 40 * 196739 * 2
def baseEnd_196739 : Nat := 67347780323340660971813

theorem tailTrace_196739 : CollatzResearch.WordTrace tailWord_196739 prefixEnd_196739 67347780323340660971813 := by
  unfold tailWord_196739
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175660834255678191249271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4783773889503785460832847 7175660834255678191249271)
  ·
    refine ⟨10763491251383517286873907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7175660834255678191249271 10763491251383517286873907)
    ·
      refine ⟨16145236877075275930310861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10763491251383517286873907 16145236877075275930310861)
      ·
        refine ⟨6054463828903228473866573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16145236877075275930310861 6054463828903228473866573)
        ·
          refine ⟨2270423935838710677699965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6054463828903228473866573 2270423935838710677699965)
          ·
            refine ⟨851408975939516504137487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2270423935838710677699965 851408975939516504137487)
            ·
              refine ⟨1277113463909274756206231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851408975939516504137487 1277113463909274756206231)
              ·
                refine ⟨1915670195863912134309347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277113463909274756206231 1915670195863912134309347)
                ·
                  refine ⟨2873505293795868201464021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915670195863912134309347 2873505293795868201464021)
                  ·
                    refine ⟨67347780323340660971813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2873505293795868201464021 67347780323340660971813)
                    ·
                      rfl

theorem cell22_196739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_196739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196739 prefixEnd_196739 := by exact prefixLift 196739
  have htrace : WordTrace (prefixWord ++ tailWord_196739) baseStart_196739 baseEnd_196739 := by
    simpa [prefixWord, tailWord_196739, baseEnd_196739] using wordTrace_append hprefix tailTrace_196739
  have hstable : (prefixWord ++ tailWord_196739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196739).length < 2 ^ (prefixWord ++ tailWord_196739).sum := by decide
  have hdescent : baseEnd_196739 < baseStart_196739 := by decide
  rcases family_descends (prefixWord ++ tailWord_196739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196741 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 5]
def baseStart_196741 : Nat := 118140960795 + 196741 * 2 ^ 59
def prefixEnd_196741 : Nat := 4983230072969 + 3 ^ 40 * 196741 * 2
def baseEnd_196741 : Nat := 22449488321404440807269

theorem tailTrace_196741 : CollatzResearch.WordTrace tailWord_196741 prefixEnd_196741 22449488321404440807269 := by
  unfold tailWord_196741
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175733780248432532822077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4783822520165621688548051 7175733780248432532822077)
  ·
    refine ⟨2690900167593162199808279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7175733780248432532822077 2690900167593162199808279)
    ·
      refine ⟨4036350251389743299712419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690900167593162199808279 4036350251389743299712419)
      ·
        refine ⟨6054525377084614949568629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4036350251389743299712419 6054525377084614949568629)
        ·
          refine ⟨567611754101682651522059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6054525377084614949568629 567611754101682651522059)
          ·
            refine ⟨851417631152523977283089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567611754101682651522059 851417631152523977283089)
            ·
              refine ⟨638563223364392982962317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851417631152523977283089 638563223364392982962317)
              ·
                refine ⟨239461208761647368610869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 638563223364392982962317 239461208761647368610869)
                ·
                  refine ⟨22449488321404440807269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239461208761647368610869 22449488321404440807269)
                  ·
                    rfl

theorem cell22_196741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_196741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196741 prefixEnd_196741 := by exact prefixLift 196741
  have htrace : WordTrace (prefixWord ++ tailWord_196741) baseStart_196741 baseEnd_196741 := by
    simpa [prefixWord, tailWord_196741, baseEnd_196741] using wordTrace_append hprefix tailTrace_196741
  have hstable : (prefixWord ++ tailWord_196741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196741).length < 2 ^ (prefixWord ++ tailWord_196741).sum := by decide
  have hdescent : baseEnd_196741 < baseStart_196741 := by decide
  rcases family_descends (prefixWord ++ tailWord_196741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196762 : List Nat := [3, 1, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_196762 : Nat := 118140960795 + 196762 * 2 ^ 59
def prefixEnd_196762 : Nat := 4983230072969 + 3 ^ 40 * 196762 * 2
def baseEnd_196762 : Nat := 67355653693376267646743

theorem tailTrace_196762 : CollatzResearch.WordTrace tailWord_196762 prefixEnd_196762 67355653693376267646743 := by
  unfold tailWord_196762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794124928293088279834135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4784333142114902079557693 1794124928293088279834135)
  ·
    refine ⟨2691187392439632419751203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1794124928293088279834135 2691187392439632419751203)
    ·
      refine ⟨4036781088659448629626805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691187392439632419751203 4036781088659448629626805)
      ·
        refine ⟨378448227061823309027513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4036781088659448629626805 378448227061823309027513)
        ·
          refine ⟨283836170296367481770635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378448227061823309027513 283836170296367481770635)
          ·
            refine ⟨425754255444551222655953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283836170296367481770635 425754255444551222655953)
            ·
              refine ⟨319315691583413416991965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425754255444551222655953 319315691583413416991965)
              ·
                refine ⟨119743384343780031371987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319315691583413416991965 119743384343780031371987)
                ·
                  refine ⟨179615076515670047057981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119743384343780031371987 179615076515670047057981)
                  ·
                    refine ⟨67355653693376267646743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179615076515670047057981 67355653693376267646743)
                    ·
                      rfl

theorem cell22_196762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_196762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196762 prefixEnd_196762 := by exact prefixLift 196762
  have htrace : WordTrace (prefixWord ++ tailWord_196762) baseStart_196762 baseEnd_196762 := by
    simpa [prefixWord, tailWord_196762, baseEnd_196762] using wordTrace_append hprefix tailTrace_196762
  have hstable : (prefixWord ++ tailWord_196762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196762).length < 2 ^ (prefixWord ++ tailWord_196762).sum := by decide
  have hdescent : baseEnd_196762 < baseStart_196762 := by decide
  rcases family_descends (prefixWord ++ tailWord_196762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196775 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 5]
def baseStart_196775 : Nat := 118140960795 + 196775 * 2 ^ 59
def prefixEnd_196775 : Nat := 4983230072969 + 3 ^ 40 * 196775 * 2
def baseEnd_196775 : Nat := 22453367953016189023901

theorem tailTrace_196775 : CollatzResearch.WordTrace tailWord_196775 prefixEnd_196775 22453367953016189023901 := by
  unfold tailWord_196775
  simp only [CollatzResearch.WordTrace]
  refine ⟨7176973862125256339559779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4784649241416837559706519 7176973862125256339559779)
  ·
    refine ⟨10765460793187884509339669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7176973862125256339559779 10765460793187884509339669)
    ·
      refine ⟨504630974680682086375297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10765460793187884509339669 504630974680682086375297)
      ·
        refine ⟨378473231010511564781473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504630974680682086375297 378473231010511564781473)
        ·
          refine ⟨283854923257883673586105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378473231010511564781473 283854923257883673586105)
          ·
            refine ⟨212891192443412755189579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283854923257883673586105 212891192443412755189579)
            ·
              refine ⟨319336788665119132784369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212891192443412755189579 319336788665119132784369)
              ·
                refine ⟨239502591498839349588277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319336788665119132784369 239502591498839349588277)
                ·
                  refine ⟨22453367953016189023901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239502591498839349588277 22453367953016189023901)
                  ·
                    rfl

theorem cell22_196775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 5].length) (baseStart_196775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196775 prefixEnd_196775 := by exact prefixLift 196775
  have htrace : WordTrace (prefixWord ++ tailWord_196775) baseStart_196775 baseEnd_196775 := by
    simpa [prefixWord, tailWord_196775, baseEnd_196775] using wordTrace_append hprefix tailTrace_196775
  have hstable : (prefixWord ++ tailWord_196775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196775).length < 2 ^ (prefixWord ++ tailWord_196775).sum := by decide
  have hdescent : baseEnd_196775 < baseStart_196775 := by decide
  rcases family_descends (prefixWord ++ tailWord_196775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196786 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_196786 : Nat := 118140960795 + 196786 * 2 ^ 59
def prefixEnd_196786 : Nat := 4983230072969 + 3 ^ 40 * 196786 * 2
def baseEnd_196786 : Nat := 22454623127949401682223

theorem tailTrace_196786 : CollatzResearch.WordTrace tailWord_196786 prefixEnd_196786 22454623127949401682223 := by
  unfold tailWord_196786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794343766271351304552553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4784916710056936812140141 1794343766271351304552553)
  ·
    refine ⟨1345757824703513478414415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1794343766271351304552553 1345757824703513478414415)
    ·
      refine ⟨2018636737055270217621623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1345757824703513478414415 2018636737055270217621623)
      ·
        refine ⟨3027955105582905326432435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018636737055270217621623 3027955105582905326432435)
        ·
          refine ⟨4541932658374357989648653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027955105582905326432435 4541932658374357989648653)
          ·
            refine ⟨1703224746890384246118245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4541932658374357989648653 1703224746890384246118245)
            ·
              refine ⟨319354640041947046147171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1703224746890384246118245 319354640041947046147171)
              ·
                refine ⟨479031960062920569220757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319354640041947046147171 479031960062920569220757)
                ·
                  refine ⟨22454623127949401682223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 479031960062920569220757 22454623127949401682223)
                  ·
                    rfl

theorem cell22_196786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_196786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196786 prefixEnd_196786 := by exact prefixLift 196786
  have htrace : WordTrace (prefixWord ++ tailWord_196786) baseStart_196786 baseEnd_196786 := by
    simpa [prefixWord, tailWord_196786, baseEnd_196786] using wordTrace_append hprefix tailTrace_196786
  have hstable : (prefixWord ++ tailWord_196786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196786).length < 2 ^ (prefixWord ++ tailWord_196786).sum := by decide
  have hdescent : baseEnd_196786 < baseStart_196786 := by decide
  rcases family_descends (prefixWord ++ tailWord_196786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196818 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_196818 : Nat := 118140960795 + 196818 * 2 ^ 59
def prefixEnd_196818 : Nat := 4983230072969 + 3 ^ 40 * 196818 * 2
def baseEnd_196818 : Nat := 67374823637810788246571

theorem tailTrace_196818 : CollatzResearch.WordTrace tailWord_196818 prefixEnd_196818 67374823637810788246571 := by
  unfold tailWord_196818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794635550242368670843777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4785694800646316455583405 1794635550242368670843777)
  ·
    refine ⟨1345976662681776503132833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1794635550242368670843777 1345976662681776503132833)
    ·
      refine ⟨1009482497011332377349625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1345976662681776503132833 1009482497011332377349625)
      ·
        refine ⟨757111872758499283012219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1009482497011332377349625 757111872758499283012219)
        ·
          refine ⟨1135667809137748924518329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757111872758499283012219 1135667809137748924518329)
          ·
            refine ⟨851750856853311693388747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135667809137748924518329 851750856853311693388747)
            ·
              refine ⟨1277626285279967540083121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851750856853311693388747 1277626285279967540083121)
              ·
                refine ⟨958219713959975655062341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277626285279967540083121 958219713959975655062341)
                ·
                  refine ⟨179666196367495435324189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958219713959975655062341 179666196367495435324189)
                  ·
                    refine ⟨67374823637810788246571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179666196367495435324189 67374823637810788246571)
                    ·
                      rfl

theorem cell22_196818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_196818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196818 prefixEnd_196818 := by exact prefixLift 196818
  have htrace : WordTrace (prefixWord ++ tailWord_196818) baseStart_196818 baseEnd_196818 := by
    simpa [prefixWord, tailWord_196818, baseEnd_196818] using wordTrace_append hprefix tailTrace_196818
  have hstable : (prefixWord ++ tailWord_196818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196818).length < 2 ^ (prefixWord ++ tailWord_196818).sum := by decide
  have hdescent : baseEnd_196818 < baseStart_196818 := by decide
  rcases family_descends (prefixWord ++ tailWord_196818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196897 : List Nat := [1, 2, 3, 2, 1, 1, 6, 2, 1, 3]
def baseStart_196897 : Nat := 118140960795 + 196897 * 2 ^ 59
def prefixEnd_196897 : Nat := 4983230072969 + 3 ^ 40 * 196897 * 2
def baseEnd_196897 : Nat := 67401866952280915521329

theorem tailTrace_196897 : CollatzResearch.WordTrace tailWord_196897 prefixEnd_196897 67401866952280915521329 := by
  unfold tailWord_196897
  simp only [CollatzResearch.WordTrace]
  refine ⟨7181423567683271175500945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4787615711788847450333963 7181423567683271175500945)
  ·
    refine ⟨5386067675762453381625709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7181423567683271175500945 5386067675762453381625709)
    ·
      refine ⟨2019775378410920018109641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5386067675762453381625709 2019775378410920018109641)
      ·
        refine ⟨1514831533808190013582231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2019775378410920018109641 1514831533808190013582231)
        ·
          refine ⟨2272247300712285020373347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514831533808190013582231 2272247300712285020373347)
          ·
            refine ⟨3408370951068427530560021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272247300712285020373347 3408370951068427530560021)
            ·
              refine ⟨159767388331332540495001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3408370951068427530560021 159767388331332540495001)
              ·
                refine ⟨119825541248499405371251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159767388331332540495001 119825541248499405371251)
                ·
                  refine ⟨179738311872749108056877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119825541248499405371251 179738311872749108056877)
                  ·
                    refine ⟨67401866952280915521329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179738311872749108056877 67401866952280915521329)
                    ·
                      rfl

theorem cell22_196897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_196897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196897 prefixEnd_196897 := by exact prefixLift 196897
  have htrace : WordTrace (prefixWord ++ tailWord_196897) baseStart_196897 baseEnd_196897 := by
    simpa [prefixWord, tailWord_196897, baseEnd_196897] using wordTrace_append hprefix tailTrace_196897
  have hstable : (prefixWord ++ tailWord_196897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196897).length < 2 ^ (prefixWord ++ tailWord_196897).sum := by decide
  have hdescent : baseEnd_196897 < baseStart_196897 := by decide
  rcases family_descends (prefixWord ++ tailWord_196897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196968 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_196968 : Nat := 118140960795 + 196968 * 2 ^ 59
def prefixEnd_196968 : Nat := 4983230072969 + 3 ^ 40 * 196968 * 2
def baseEnd_196968 : Nat := 67426171703260396996111

theorem tailTrace_196968 : CollatzResearch.WordTrace tailWord_196968 prefixEnd_196968 67426171703260396996111 := by
  unfold tailWord_196968
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592006575213025150667779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4789342100284033534223705 3592006575213025150667779)
  ·
    refine ⟨5388009862819537726001669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3592006575213025150667779 5388009862819537726001669)
    ·
      refine ⟨1010251849278663323625313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5388009862819537726001669 1010251849278663323625313)
      ·
        refine ⟨757688886958997492718985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1010251849278663323625313 757688886958997492718985)
        ·
          refine ⟨568266665219248119539239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757688886958997492718985 568266665219248119539239)
          ·
            refine ⟨852399997828872179308859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568266665219248119539239 852399997828872179308859)
            ·
              refine ⟨1278599996743308268963289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852399997828872179308859 1278599996743308268963289)
              ·
                refine ⟨958949997557481201722467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278599996743308268963289 958949997557481201722467)
                ·
                  refine ⟨1438424996336221802583701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958949997557481201722467 1438424996336221802583701)
                  ·
                    refine ⟨67426171703260396996111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1438424996336221802583701 67426171703260396996111)
                    ·
                      rfl

theorem cell22_196968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_196968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196968 prefixEnd_196968 := by exact prefixLift 196968
  have htrace : WordTrace (prefixWord ++ tailWord_196968) baseStart_196968 baseEnd_196968 := by
    simpa [prefixWord, tailWord_196968, baseEnd_196968] using wordTrace_append hprefix tailTrace_196968
  have hstable : (prefixWord ++ tailWord_196968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196968).length < 2 ^ (prefixWord ++ tailWord_196968).sum := by decide
  have hdescent : baseEnd_196968 < baseStart_196968 := by decide
  rcases family_descends (prefixWord ++ tailWord_196968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196970 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_196970 : Nat := 118140960795 + 196970 * 2 ^ 59
def prefixEnd_196970 : Nat := 4983230072969 + 3 ^ 40 * 196970 * 2
def baseEnd_196970 : Nat := 67426856344133058446105

theorem tailTrace_196970 : CollatzResearch.WordTrace tailWord_196970 prefixEnd_196970 67426856344133058446105 := by
  unfold tailWord_196970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796021524104701160727091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4789390730945869761938909 1796021524104701160727091)
  ·
    refine ⟨2694032286157051741090637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1796021524104701160727091 2694032286157051741090637)
    ·
      refine ⟨1010262107308894402908989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2694032286157051741090637 1010262107308894402908989)
      ·
        refine ⟨378848290240835401090871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1010262107308894402908989 378848290240835401090871)
        ·
          refine ⟨568272435361253101636307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378848290240835401090871 568272435361253101636307)
          ·
            refine ⟨852408653041879652454461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568272435361253101636307 852408653041879652454461)
            ·
              refine ⟨319653244890704869670423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852408653041879652454461 319653244890704869670423)
              ·
                refine ⟨479479867336057304505635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319653244890704869670423 479479867336057304505635)
                ·
                  refine ⟨719219801004085956758453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479479867336057304505635 719219801004085956758453)
                  ·
                    refine ⟨67426856344133058446105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 719219801004085956758453 67426856344133058446105)
                    ·
                      rfl

theorem cell22_196970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_196970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_196970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_196970 prefixEnd_196970 := by exact prefixLift 196970
  have htrace : WordTrace (prefixWord ++ tailWord_196970) baseStart_196970 baseEnd_196970 := by
    simpa [prefixWord, tailWord_196970, baseEnd_196970] using wordTrace_append hprefix tailTrace_196970
  have hstable : (prefixWord ++ tailWord_196970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196970).length < 2 ^ (prefixWord ++ tailWord_196970).sum := by decide
  have hdescent : baseEnd_196970 < baseStart_196970 := by decide
  rcases family_descends (prefixWord ++ tailWord_196970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197002 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_197002 : Nat := 118140960795 + 197002 * 2 ^ 59
def prefixEnd_197002 : Nat := 4983230072969 + 3 ^ 40 * 197002 * 2
def baseEnd_197002 : Nat := 67437810598095641646007

theorem tailTrace_197002 : CollatzResearch.WordTrace tailWord_197002 prefixEnd_197002 67437810598095641646007 := by
  unfold tailWord_197002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796313308075718527018315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4790168821535249405382173 1796313308075718527018315)
  ·
    refine ⟨2694469962113577790527473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1796313308075718527018315 2694469962113577790527473)
    ·
      refine ⟨2020852471585183342895605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2694469962113577790527473 2020852471585183342895605)
      ·
        refine ⟨189454919211110938396463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2020852471585183342895605 189454919211110938396463)
        ·
          refine ⟨284182378816666407594695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189454919211110938396463 284182378816666407594695)
          ·
            refine ⟨426273568224999611392043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284182378816666407594695 426273568224999611392043)
            ·
              refine ⟨639410352337499417088065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426273568224999611392043 639410352337499417088065)
              ·
                refine ⟨479557764253124562816049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639410352337499417088065 479557764253124562816049)
                ·
                  refine ⟨359668323189843422112037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479557764253124562816049 359668323189843422112037)
                  ·
                    refine ⟨67437810598095641646007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 359668323189843422112037 67437810598095641646007)
                    ·
                      rfl

theorem cell22_197002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_197002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197002 prefixEnd_197002 := by exact prefixLift 197002
  have htrace : WordTrace (prefixWord ++ tailWord_197002) baseStart_197002 baseEnd_197002 := by
    simpa [prefixWord, tailWord_197002, baseEnd_197002] using wordTrace_append hprefix tailTrace_197002
  have hstable : (prefixWord ++ tailWord_197002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197002).length < 2 ^ (prefixWord ++ tailWord_197002).sum := by decide
  have hdescent : baseEnd_197002 < baseStart_197002 := by decide
  rcases family_descends (prefixWord ++ tailWord_197002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197015 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 3, 3]
def baseStart_197015 : Nat := 118140960795 + 197015 * 2 ^ 59
def prefixEnd_197015 : Nat := 4983230072969 + 3 ^ 40 * 197015 * 2
def baseEnd_197015 : Nat := 67442260763767941070967

theorem tailTrace_197015 : CollatzResearch.WordTrace tailWord_197015 prefixEnd_197015 67442260763767941070967 := by
  unfold tailWord_197015
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185727381255777328296499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4790484920837184885530999 7185727381255777328296499)
  ·
    refine ⟨10778591071883665992444749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7185727381255777328296499 10778591071883665992444749)
    ·
      refine ⟨4041971651956374747166781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10778591071883665992444749 4041971651956374747166781)
      ·
        refine ⟨1515739369483640530187543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4041971651956374747166781 1515739369483640530187543)
        ·
          refine ⟨2273609054225460795281315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515739369483640530187543 2273609054225460795281315)
          ·
            refine ⟨3410413581338191192921973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273609054225460795281315 3410413581338191192921973)
            ·
              refine ⟨319726273250455424336435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3410413581338191192921973 319726273250455424336435)
              ·
                refine ⟨479589409875683136504653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319726273250455424336435 479589409875683136504653)
                ·
                  refine ⟨179846028703381176189245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479589409875683136504653 179846028703381176189245)
                  ·
                    refine ⟨67442260763767941070967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179846028703381176189245 67442260763767941070967)
                    ·
                      rfl

theorem cell22_197015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_197015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197015 prefixEnd_197015 := by exact prefixLift 197015
  have htrace : WordTrace (prefixWord ++ tailWord_197015) baseStart_197015 baseEnd_197015 := by
    simpa [prefixWord, tailWord_197015, baseEnd_197015] using wordTrace_append hprefix tailTrace_197015
  have hstable : (prefixWord ++ tailWord_197015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197015).length < 2 ^ (prefixWord ++ tailWord_197015).sum := by decide
  have hdescent : baseEnd_197015 < baseStart_197015 := by decide
  rcases family_descends (prefixWord ++ tailWord_197015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197021 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_197021 : Nat := 118140960795 + 197021 * 2 ^ 59
def prefixEnd_197021 : Nat := 4983230072969 + 3 ^ 40 * 197021 * 2
def baseEnd_197021 : Nat := 67444314686385925420949

theorem tailTrace_197021 : CollatzResearch.WordTrace tailWord_197021 prefixEnd_197021 67444314686385925420949 := by
  unfold tailWord_197021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185946219234040353014917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4790630812822693568676611 7185946219234040353014917)
  ·
    refine ⟨1347364916106382566190297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7185946219234040353014917 1347364916106382566190297)
    ·
      refine ⟨1010523687079786924642723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1347364916106382566190297 1010523687079786924642723)
      ·
        refine ⟨1515785530619680386964085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010523687079786924642723 1515785530619680386964085)
        ·
          refine ⟨142104893495595036277883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1515785530619680386964085 142104893495595036277883)
          ·
            refine ⟨213157340243392554416825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142104893495595036277883 213157340243392554416825)
            ·
              refine ⟨159868005182544415812619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213157340243392554416825 159868005182544415812619)
              ·
                refine ⟨239802007773816623718929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159868005182544415812619 239802007773816623718929)
                ·
                  refine ⟨179851505830362467789197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239802007773816623718929 179851505830362467789197)
                  ·
                    refine ⟨67444314686385925420949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179851505830362467789197 67444314686385925420949)
                    ·
                      rfl

theorem cell22_197021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_197021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197021 prefixEnd_197021 := by exact prefixLift 197021
  have htrace : WordTrace (prefixWord ++ tailWord_197021) baseStart_197021 baseEnd_197021 := by
    simpa [prefixWord, tailWord_197021, baseEnd_197021] using wordTrace_append hprefix tailTrace_197021
  have hstable : (prefixWord ++ tailWord_197021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197021).length < 2 ^ (prefixWord ++ tailWord_197021).sum := by decide
  have hdescent : baseEnd_197021 < baseStart_197021 := by decide
  rcases family_descends (prefixWord ++ tailWord_197021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197105 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 4, 3]
def baseStart_197105 : Nat := 118140960795 + 197105 * 2 ^ 59
def prefixEnd_197105 : Nat := 4983230072969 + 3 ^ 40 * 197105 * 2
def baseEnd_197105 : Nat := 67473069603037706320691

theorem tailTrace_197105 : CollatzResearch.WordTrace tailWord_197105 prefixEnd_197105 67473069603037706320691 := by
  unfold tailWord_197105
  simp only [CollatzResearch.WordTrace]
  refine ⟨7189009950929722699072769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4792673300619815132715179 7189009950929722699072769)
  ·
    refine ⟨5391757463197292024304577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7189009950929722699072769 5391757463197292024304577)
    ·
      refine ⟨4043818097397969018228433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5391757463197292024304577 4043818097397969018228433)
      ·
        refine ⟨3032863573048476763671325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4043818097397969018228433 3032863573048476763671325)
        ·
          refine ⟨1137323839893178786376747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3032863573048476763671325 1137323839893178786376747)
          ·
            refine ⟨1705985759839768179565121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137323839893178786376747 1705985759839768179565121)
            ·
              refine ⟨1279489319879826134673841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705985759839768179565121 1279489319879826134673841)
              ·
                refine ⟨959616989909869601005381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279489319879826134673841 959616989909869601005381)
                ·
                  refine ⟨179928185608100550188509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959616989909869601005381 179928185608100550188509)
                  ·
                    refine ⟨67473069603037706320691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179928185608100550188509 67473069603037706320691)
                    ·
                      rfl

theorem cell22_197105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_197105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197105 prefixEnd_197105 := by exact prefixLift 197105
  have htrace : WordTrace (prefixWord ++ tailWord_197105) baseStart_197105 baseEnd_197105 := by
    simpa [prefixWord, tailWord_197105, baseEnd_197105] using wordTrace_append hprefix tailTrace_197105
  have hstable : (prefixWord ++ tailWord_197105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197105).length < 2 ^ (prefixWord ++ tailWord_197105).sum := by decide
  have hdescent : baseEnd_197105 < baseStart_197105 := by decide
  rcases family_descends (prefixWord ++ tailWord_197105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197109 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_197109 : Nat := 118140960795 + 197109 * 2 ^ 59
def prefixEnd_197109 : Nat := 4983230072969 + 3 ^ 40 * 197109 * 2
def baseEnd_197109 : Nat := 67474438884783029220679

theorem tailTrace_197109 : CollatzResearch.WordTrace tailWord_197109 prefixEnd_197109 67474438884783029220679 := by
  unfold tailWord_197109
  simp only [CollatzResearch.WordTrace]
  refine ⟨7189155842915231382218381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4792770561943487588145587 7189155842915231382218381)
  ·
    refine ⟨2695933441093211768331893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7189155842915231382218381 2695933441093211768331893)
    ·
      refine ⟨252743760102488603281115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2695933441093211768331893 252743760102488603281115)
      ·
        refine ⟨379115640153732904921673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252743760102488603281115 379115640153732904921673)
        ·
          refine ⟨284336730115299678691255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379115640153732904921673 284336730115299678691255)
          ·
            refine ⟨426505095172949518036883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284336730115299678691255 426505095172949518036883)
            ·
              refine ⟨639757642759424277055325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426505095172949518036883 639757642759424277055325)
              ·
                refine ⟨239909116034784103895747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 639757642759424277055325 239909116034784103895747)
                ·
                  refine ⟨359863674052176155843621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239909116034784103895747 359863674052176155843621)
                  ·
                    refine ⟨67474438884783029220679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 359863674052176155843621 67474438884783029220679)
                    ·
                      rfl

theorem cell22_197109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_197109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197109 prefixEnd_197109 := by exact prefixLift 197109
  have htrace : WordTrace (prefixWord ++ tailWord_197109) baseStart_197109 baseEnd_197109 := by
    simpa [prefixWord, tailWord_197109, baseEnd_197109] using wordTrace_append hprefix tailTrace_197109
  have hstable : (prefixWord ++ tailWord_197109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197109).length < 2 ^ (prefixWord ++ tailWord_197109).sum := by decide
  have hdescent : baseEnd_197109 < baseStart_197109 := by decide
  rcases family_descends (prefixWord ++ tailWord_197109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197180 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 7]
def baseStart_197180 : Nat := 118140960795 + 197180 * 2 ^ 59
def prefixEnd_197180 : Nat := 4983230072969 + 3 ^ 40 * 197180 * 2
def baseEnd_197180 : Nat := 22499581211920836898487

theorem tailTrace_197180 : CollatzResearch.WordTrace tailWord_197180 prefixEnd_197180 22499581211920836898487 := by
  unfold tailWord_197180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595872712829005254026497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4794496950438673672035329 3595872712829005254026497)
  ·
    refine ⟨2696904534621753940519873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3595872712829005254026497 2696904534621753940519873)
    ·
      refine ⟨2022678400966315455389905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2696904534621753940519873 2022678400966315455389905)
      ·
        refine ⟨1517008800724736591542429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2022678400966315455389905 1517008800724736591542429)
        ·
          refine ⟨568878300271776221828411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1517008800724736591542429 568878300271776221828411)
          ·
            refine ⟨853317450407664332742617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568878300271776221828411 853317450407664332742617)
            ·
              refine ⟨639988087805748249556963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853317450407664332742617 639988087805748249556963)
              ·
                refine ⟨959982131708622374335445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639988087805748249556963 959982131708622374335445)
                ·
                  refine ⟨22499581211920836898487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 959982131708622374335445 22499581211920836898487)
                  ·
                    rfl

theorem cell22_197180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_197180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197180 prefixEnd_197180 := by exact prefixLift 197180
  have htrace : WordTrace (prefixWord ++ tailWord_197180) baseStart_197180 baseEnd_197180 := by
    simpa [prefixWord, tailWord_197180, baseEnd_197180] using wordTrace_append hprefix tailTrace_197180
  have hstable : (prefixWord ++ tailWord_197180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197180).length < 2 ^ (prefixWord ++ tailWord_197180).sum := by decide
  have hdescent : baseEnd_197180 < baseStart_197180 := by decide
  rcases family_descends (prefixWord ++ tailWord_197180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197193 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_197193 : Nat := 118140960795 + 197193 * 2 ^ 59
def prefixEnd_197193 : Nat := 4983230072969 + 3 ^ 40 * 197193 * 2
def baseEnd_197193 : Nat := 67503193801434810120421

theorem tailTrace_197193 : CollatzResearch.WordTrace tailWord_197193 prefixEnd_197193 67503193801434810120421 := by
  unfold tailWord_197193
  simp only [CollatzResearch.WordTrace]
  refine ⟨7192219574610913728276233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4794813049740609152184155 7192219574610913728276233)
  ·
    refine ⟨5394164680958185296207175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7192219574610913728276233 5394164680958185296207175)
    ·
      refine ⟨8091247021437277944310763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5394164680958185296207175 8091247021437277944310763)
      ·
        refine ⟨12136870532155916916466145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091247021437277944310763 12136870532155916916466145)
        ·
          refine ⟨9102652899116937687349609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12136870532155916916466145 9102652899116937687349609)
          ·
            refine ⟨6826989674337703265512207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9102652899116937687349609 6826989674337703265512207)
            ·
              refine ⟨10240484511506554898268311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826989674337703265512207 10240484511506554898268311)
              ·
                refine ⟨15360726767259832347402467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10240484511506554898268311 15360726767259832347402467)
                ·
                  refine ⟨23041090150889748521103701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15360726767259832347402467 23041090150889748521103701)
                  ·
                    refine ⟨67503193801434810120421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 23041090150889748521103701 67503193801434810120421)
                    ·
                      rfl

theorem cell22_197193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_197193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197193 prefixEnd_197193 := by exact prefixLift 197193
  have htrace : WordTrace (prefixWord ++ tailWord_197193) baseStart_197193 baseEnd_197193 := by
    simpa [prefixWord, tailWord_197193, baseEnd_197193] using wordTrace_append hprefix tailTrace_197193
  have hstable : (prefixWord ++ tailWord_197193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197193).length < 2 ^ (prefixWord ++ tailWord_197193).sum := by decide
  have hdescent : baseEnd_197193 < baseStart_197193 := by decide
  rcases family_descends (prefixWord ++ tailWord_197193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197255 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 1, 6]
def baseStart_197255 : Nat := 118140960795 + 197255 * 2 ^ 59
def prefixEnd_197255 : Nat := 4983230072969 + 3 ^ 40 * 197255 * 2
def baseEnd_197255 : Nat := 67524417668487315070231

theorem tailTrace_197255 : CollatzResearch.WordTrace tailWord_197255 prefixEnd_197255 67524417668487315070231 := by
  unfold tailWord_197255
  simp only [CollatzResearch.WordTrace]
  refine ⟨7194480900386298317033219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4796320600257532211355479 7194480900386298317033219)
  ·
    refine ⟨10791721350579447475549829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7194480900386298317033219 10791721350579447475549829)
    ·
      refine ⟨2023447753233646401665593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10791721350579447475549829 2023447753233646401665593)
      ·
        refine ⟨1517585814925234801249195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2023447753233646401665593 1517585814925234801249195)
        ·
          refine ⟨2276378722387852201873793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517585814925234801249195 2276378722387852201873793)
          ·
            refine ⟨1707284041790889151405345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276378722387852201873793 1707284041790889151405345)
            ·
              refine ⟨1280463031343166863554009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707284041790889151405345 1280463031343166863554009)
              ·
                refine ⟨960347273507375147665507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280463031343166863554009 960347273507375147665507)
                ·
                  refine ⟨1440520910261062721498261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960347273507375147665507 1440520910261062721498261)
                  ·
                    refine ⟨67524417668487315070231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1440520910261062721498261 67524417668487315070231)
                    ·
                      rfl

theorem cell22_197255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_197255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197255 prefixEnd_197255 := by exact prefixLift 197255
  have htrace : WordTrace (prefixWord ++ tailWord_197255) baseStart_197255 baseEnd_197255 := by
    simpa [prefixWord, tailWord_197255, baseEnd_197255] using wordTrace_append hprefix tailTrace_197255
  have hstable : (prefixWord ++ tailWord_197255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197255).length < 2 ^ (prefixWord ++ tailWord_197255).sum := by decide
  have hdescent : baseEnd_197255 < baseStart_197255 := by decide
  rcases family_descends (prefixWord ++ tailWord_197255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197336 : List Nat := [2, 1, 2, 2, 3, 2, 3, 3, 1, 3]
def baseStart_197336 : Nat := 118140960795 + 197336 * 2 ^ 59
def prefixEnd_197336 : Nat := 4983230072969 + 3 ^ 40 * 197336 * 2
def baseEnd_197336 : Nat := 67552145623830103794983

theorem tailTrace_197336 : CollatzResearch.WordTrace tailWord_197336 prefixEnd_197336 67552145623830103794983 := by
  unfold tailWord_197336
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598717606546424575365931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4798290142061899433821241 3598717606546424575365931)
  ·
    refine ⟨5398076409819636863048897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3598717606546424575365931 5398076409819636863048897)
    ·
      refine ⟨4048557307364727647286673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5398076409819636863048897 4048557307364727647286673)
      ·
        refine ⟨3036417980523545735465005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4048557307364727647286673 3036417980523545735465005)
        ·
          refine ⟨1138656742696329650799377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3036417980523545735465005 1138656742696329650799377)
          ·
            refine ⟨853992557022247238099533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138656742696329650799377 853992557022247238099533)
            ·
              refine ⟨320247208883342714287325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853992557022247238099533 320247208883342714287325)
              ·
                refine ⟨120092703331253517857747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320247208883342714287325 120092703331253517857747)
                ·
                  refine ⟨180139054996880276786621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120092703331253517857747 180139054996880276786621)
                  ·
                    refine ⟨67552145623830103794983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180139054996880276786621 67552145623830103794983)
                    ·
                      rfl

theorem cell22_197336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_197336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197336 prefixEnd_197336 := by exact prefixLift 197336
  have htrace : WordTrace (prefixWord ++ tailWord_197336) baseStart_197336 baseEnd_197336 := by
    simpa [prefixWord, tailWord_197336, baseEnd_197336] using wordTrace_append hprefix tailTrace_197336
  have hstable : (prefixWord ++ tailWord_197336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197336).length < 2 ^ (prefixWord ++ tailWord_197336).sum := by decide
  have hdescent : baseEnd_197336 < baseStart_197336 := by decide
  rcases family_descends (prefixWord ++ tailWord_197336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197439 : List Nat := [1, 1, 2, 2, 5, 2, 3, 6]
def baseStart_197439 : Nat := 118140960795 + 197439 * 2 ^ 59
def prefixEnd_197439 : Nat := 4983230072969 + 3 ^ 40 * 197439 * 2
def baseEnd_197439 : Nat := 7509711625419129829963

theorem tailTrace_197439 : CollatzResearch.WordTrace tailWord_197439 prefixEnd_197439 7509711625419129829963 := by
  unfold tailWord_197439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201191931719697741731371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4800794621146465161154247 7201191931719697741731371)
  ·
    refine ⟨10801787897579546612597057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7201191931719697741731371 10801787897579546612597057)
    ·
      refine ⟨8101340923184659959447793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10801787897579546612597057 8101340923184659959447793)
      ·
        refine ⟨6076005692388494969585845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8101340923184659959447793 6076005692388494969585845)
        ·
          refine ⟨569625533661421403398673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6076005692388494969585845 569625533661421403398673)
          ·
            refine ⟨427219150246066052549005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569625533661421403398673 427219150246066052549005)
            ·
              refine ⟨160207181342274769705877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427219150246066052549005 160207181342274769705877)
              ·
                refine ⟨7509711625419129829963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160207181342274769705877 7509711625419129829963)
                ·
                  rfl

theorem cell22_197439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 6].length) (baseStart_197439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197439 prefixEnd_197439 := by exact prefixLift 197439
  have htrace : WordTrace (prefixWord ++ tailWord_197439) baseStart_197439 baseEnd_197439 := by
    simpa [prefixWord, tailWord_197439, baseEnd_197439] using wordTrace_append hprefix tailTrace_197439
  have hstable : (prefixWord ++ tailWord_197439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197439).length < 2 ^ (prefixWord ++ tailWord_197439).sum := by decide
  have hdescent : baseEnd_197439 < baseStart_197439 := by decide
  rcases family_descends (prefixWord ++ tailWord_197439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197441 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 1, 6]
def baseStart_197441 : Nat := 118140960795 + 197441 * 2 ^ 59
def prefixEnd_197441 : Nat := 4983230072969 + 3 ^ 40 * 197441 * 2
def baseEnd_197441 : Nat := 67588089269644829919661

theorem tailTrace_197441 : CollatzResearch.WordTrace tailWord_197441 prefixEnd_197441 67588089269644829919661 := by
  unfold tailWord_197441
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201264877712452083304177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4800843251808301388869451 7201264877712452083304177)
  ·
    refine ⟨5400948658284339062478133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7201264877712452083304177 5400948658284339062478133)
    ·
      refine ⟨506338936714156787107325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5400948658284339062478133 506338936714156787107325)
      ·
        refine ⟨189877101267808795165247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506338936714156787107325 189877101267808795165247)
        ·
          refine ⟨284815651901713192747871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189877101267808795165247 284815651901713192747871)
          ·
            refine ⟨427223477852569789121807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284815651901713192747871 427223477852569789121807)
            ·
              refine ⟨640835216778854683682711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427223477852569789121807 640835216778854683682711)
              ·
                refine ⟨961252825168282025524067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640835216778854683682711 961252825168282025524067)
                ·
                  refine ⟨1441879237752423038286101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961252825168282025524067 1441879237752423038286101)
                  ·
                    refine ⟨67588089269644829919661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1441879237752423038286101 67588089269644829919661)
                    ·
                      rfl

theorem cell22_197441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_197441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197441 prefixEnd_197441 := by exact prefixLift 197441
  have htrace : WordTrace (prefixWord ++ tailWord_197441) baseStart_197441 baseEnd_197441 := by
    simpa [prefixWord, tailWord_197441, baseEnd_197441] using wordTrace_append hprefix tailTrace_197441
  have hstable : (prefixWord ++ tailWord_197441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197441).length < 2 ^ (prefixWord ++ tailWord_197441).sum := by decide
  have hdescent : baseEnd_197441 < baseStart_197441 := by decide
  rcases family_descends (prefixWord ++ tailWord_197441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197460 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_197460 : Nat := 118140960795 + 197460 * 2 ^ 59
def prefixEnd_197460 : Nat := 4983230072969 + 3 ^ 40 * 197460 * 2
def baseEnd_197460 : Nat := 67594593357935113694603

theorem tailTrace_197460 : CollatzResearch.WordTrace tailWord_197460 prefixEnd_197460 67594593357935113694603 := by
  unfold tailWord_197460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600978932321809164122917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4801305243095745552163889 3600978932321809164122917)
  ·
    refine ⟨675183549810339218273047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3600978932321809164122917 675183549810339218273047)
    ·
      refine ⟨1012775324715508827409571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675183549810339218273047 1012775324715508827409571)
      ·
        refine ⟨1519162987073263241114357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012775324715508827409571 1519162987073263241114357)
        ·
          refine ⟨142421530038118428854471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1519162987073263241114357 142421530038118428854471)
          ·
            refine ⟨213632295057177643281707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142421530038118428854471 213632295057177643281707)
            ·
              refine ⟨320448442585766464922561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213632295057177643281707 320448442585766464922561)
              ·
                refine ⟨240336331939324848691921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320448442585766464922561 240336331939324848691921)
                ·
                  refine ⟨180252248954493636518941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240336331939324848691921 180252248954493636518941)
                  ·
                    refine ⟨67594593357935113694603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180252248954493636518941 67594593357935113694603)
                    ·
                      rfl

theorem cell22_197460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_197460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197460 prefixEnd_197460 := by exact prefixLift 197460
  have htrace : WordTrace (prefixWord ++ tailWord_197460) baseStart_197460 baseEnd_197460 := by
    simpa [prefixWord, tailWord_197460, baseEnd_197460] using wordTrace_append hprefix tailTrace_197460
  have hstable : (prefixWord ++ tailWord_197460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197460).length < 2 ^ (prefixWord ++ tailWord_197460).sum := by decide
  have hdescent : baseEnd_197460 < baseStart_197460 := by decide
  rcases family_descends (prefixWord ++ tailWord_197460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197471 : List Nat := [1, 1, 2, 3, 1, 3, 1, 6, 1, 3]
def baseStart_197471 : Nat := 118140960795 + 197471 * 2 ^ 59
def prefixEnd_197471 : Nat := 4983230072969 + 3 ^ 40 * 197471 * 2
def baseEnd_197471 : Nat := 67598358882734751669569

theorem tailTrace_197471 : CollatzResearch.WordTrace tailWord_197471 prefixEnd_197471 67598358882734751669569 := by
  unfold tailWord_197471
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202359067603767206896267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4801572711735844804597511 7202359067603767206896267)
  ·
    refine ⟨10803538601405650810344401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7202359067603767206896267 10803538601405650810344401)
    ·
      refine ⟨8102653951054238107758301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10803538601405650810344401 8102653951054238107758301)
      ·
        refine ⟨3038495231645339290409363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8102653951054238107758301 3038495231645339290409363)
        ·
          refine ⟨4557742847468008935614045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038495231645339290409363 4557742847468008935614045)
          ·
            refine ⟨1709153567800503350855267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4557742847468008935614045 1709153567800503350855267)
            ·
              refine ⟨2563730351700755026282901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709153567800503350855267 2563730351700755026282901)
              ·
                refine ⟨120174860235972891857011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2563730351700755026282901 120174860235972891857011)
                ·
                  refine ⟨180262290353959337785517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120174860235972891857011 180262290353959337785517)
                  ·
                    refine ⟨67598358882734751669569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180262290353959337785517 67598358882734751669569)
                    ·
                      rfl

theorem cell22_197471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 3].length) (baseStart_197471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197471 prefixEnd_197471 := by exact prefixLift 197471
  have htrace : WordTrace (prefixWord ++ tailWord_197471) baseStart_197471 baseEnd_197471 := by
    simpa [prefixWord, tailWord_197471, baseEnd_197471] using wordTrace_append hprefix tailTrace_197471
  have hstable : (prefixWord ++ tailWord_197471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197471).length < 2 ^ (prefixWord ++ tailWord_197471).sum := by decide
  have hdescent : baseEnd_197471 < baseStart_197471 := by decide
  rcases family_descends (prefixWord ++ tailWord_197471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197522 : List Nat := [3, 2, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_197522 : Nat := 118140960795 + 197522 * 2 ^ 59
def prefixEnd_197522 : Nat := 4983230072969 + 3 ^ 40 * 197522 * 2
def baseEnd_197522 : Nat := 67615817224987618644413

theorem tailTrace_197522 : CollatzResearch.WordTrace tailWord_197522 prefixEnd_197522 67615817224987618644413 := by
  unfold tailWord_197522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801054797604750729250705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4802812793612668611335213 1801054797604750729250705)
  ·
    refine ⟨1350791098203563046938029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1801054797604750729250705 1350791098203563046938029)
    ·
      refine ⟨506546661826336142601761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1350791098203563046938029 506546661826336142601761)
      ·
        refine ⟨379909996369752106951321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506546661826336142601761 379909996369752106951321)
        ·
          refine ⟨284932497277314080213491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379909996369752106951321 284932497277314080213491)
          ·
            refine ⟨427398745915971120320237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284932497277314080213491 427398745915971120320237)
            ·
              refine ⟨160274529718489170120089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427398745915971120320237 160274529718489170120089)
              ·
                refine ⟨120205897288866877590067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160274529718489170120089 120205897288866877590067)
                ·
                  refine ⟨180308845933300316385101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120205897288866877590067 180308845933300316385101)
                  ·
                    refine ⟨67615817224987618644413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180308845933300316385101 67615817224987618644413)
                    ·
                      rfl

theorem cell22_197522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_197522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197522 prefixEnd_197522 := by exact prefixLift 197522
  have htrace : WordTrace (prefixWord ++ tailWord_197522) baseStart_197522 baseEnd_197522 := by
    simpa [prefixWord, tailWord_197522, baseEnd_197522] using wordTrace_append hprefix tailTrace_197522
  have hstable : (prefixWord ++ tailWord_197522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197522).length < 2 ^ (prefixWord ++ tailWord_197522).sum := by decide
  have hdescent : baseEnd_197522 < baseStart_197522 := by decide
  rcases family_descends (prefixWord ++ tailWord_197522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197559 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 2, 4]
def baseStart_197559 : Nat := 118140960795 + 197559 * 2 ^ 59
def prefixEnd_197559 : Nat := 4983230072969 + 3 ^ 40 * 197559 * 2
def baseEnd_197559 : Nat := 67628483081131855469299

theorem tailTrace_197559 : CollatzResearch.WordTrace tailWord_197559 prefixEnd_197559 67628483081131855469299 := by
  unfold tailWord_197559
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205568691284958236099731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4803712460856638824066487 7205568691284958236099731)
  ·
    refine ⟨10808353036927437354149597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205568691284958236099731 10808353036927437354149597)
    ·
      refine ⟨4053132388847789007806099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10808353036927437354149597 4053132388847789007806099)
      ·
        refine ⟨6079698583271683511709149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053132388847789007806099 6079698583271683511709149)
        ·
          refine ⟨2279886968726881316890931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6079698583271683511709149 2279886968726881316890931)
          ·
            refine ⟨3419830453090321975336397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279886968726881316890931 3419830453090321975336397)
            ·
              refine ⟨1282436419908870740751149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3419830453090321975336397 1282436419908870740751149)
              ·
                refine ⟨480913657465826527781681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282436419908870740751149 480913657465826527781681)
                ·
                  refine ⟨360685243099369895836261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480913657465826527781681 360685243099369895836261)
                  ·
                    refine ⟨67628483081131855469299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360685243099369895836261 67628483081131855469299)
                    ·
                      rfl

theorem cell22_197559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_197559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197559 prefixEnd_197559 := by exact prefixLift 197559
  have htrace : WordTrace (prefixWord ++ tailWord_197559) baseStart_197559 baseEnd_197559 := by
    simpa [prefixWord, tailWord_197559, baseEnd_197559] using wordTrace_append hprefix tailTrace_197559
  have hstable : (prefixWord ++ tailWord_197559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197559).length < 2 ^ (prefixWord ++ tailWord_197559).sum := by decide
  have hdescent : baseEnd_197559 < baseStart_197559 := by decide
  rcases family_descends (prefixWord ++ tailWord_197559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197649 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_197649 : Nat := 118140960795 + 197649 * 2 ^ 59
def prefixEnd_197649 : Nat := 4983230072969 + 3 ^ 40 * 197649 * 2
def baseEnd_197649 : Nat := 67659291920401620719023

theorem tailTrace_197649 : CollatzResearch.WordTrace tailWord_197649 prefixEnd_197649 67659291920401620719023 := by
  unfold tailWord_197649
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208851260958903606876001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4805900840639269071250667 7208851260958903606876001)
  ·
    refine ⟨5406638445719177705157001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7208851260958903606876001 5406638445719177705157001)
    ·
      refine ⟨4054978834289383278867751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5406638445719177705157001 4054978834289383278867751)
      ·
        refine ⟨6082468251434074918301627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054978834289383278867751 6082468251434074918301627)
        ·
          refine ⟨9123702377151112377452441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6082468251434074918301627 9123702377151112377452441)
          ·
            refine ⟨6842776782863334283089331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9123702377151112377452441 6842776782863334283089331)
            ·
              refine ⟨10264165174295001424633997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6842776782863334283089331 10264165174295001424633997)
              ·
                refine ⟨3849061940360625534237749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10264165174295001424633997 3849061940360625534237749)
                ·
                  refine ⟨360849556908808643834789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849061940360625534237749 360849556908808643834789)
                  ·
                    refine ⟨67659291920401620719023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360849556908808643834789 67659291920401620719023)
                    ·
                      rfl

theorem cell22_197649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_197649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197649 prefixEnd_197649 := by exact prefixLift 197649
  have htrace : WordTrace (prefixWord ++ tailWord_197649) baseStart_197649 baseEnd_197649 := by
    simpa [prefixWord, tailWord_197649, baseEnd_197649] using wordTrace_append hprefix tailTrace_197649
  have hstable : (prefixWord ++ tailWord_197649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197649).length < 2 ^ (prefixWord ++ tailWord_197649).sum := by decide
  have hdescent : baseEnd_197649 < baseStart_197649 := by decide
  rcases family_descends (prefixWord ++ tailWord_197649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197653 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 5]
def baseStart_197653 : Nat := 118140960795 + 197653 * 2 ^ 59
def prefixEnd_197653 : Nat := 4983230072969 + 3 ^ 40 * 197653 * 2
def baseEnd_197653 : Nat := 22553553734048981206337

theorem tailTrace_197653 : CollatzResearch.WordTrace tailWord_197653 prefixEnd_197653 22553553734048981206337 := by
  unfold tailWord_197653
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208997152944412290021613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4805998101962941526681075 7208997152944412290021613)
  ·
    refine ⟨2703373932354154608758105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7208997152944412290021613 2703373932354154608758105)
    ·
      refine ⟨2027530449265615956568579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703373932354154608758105 2027530449265615956568579)
      ·
        refine ⟨3041295673898423934852869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027530449265615956568579 3041295673898423934852869)
        ·
          refine ⟨570242938855954487784913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3041295673898423934852869 570242938855954487784913)
          ·
            refine ⟨427682204141965865838685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570242938855954487784913 427682204141965865838685)
            ·
              refine ⟨160380826553237199689507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427682204141965865838685 160380826553237199689507)
              ·
                refine ⟨240571239829855799534261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160380826553237199689507 240571239829855799534261)
                ·
                  refine ⟨22553553734048981206337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240571239829855799534261 22553553734048981206337)
                  ·
                    rfl

theorem cell22_197653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_197653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197653 prefixEnd_197653 := by exact prefixLift 197653
  have htrace : WordTrace (prefixWord ++ tailWord_197653) baseStart_197653 baseEnd_197653 := by
    simpa [prefixWord, tailWord_197653, baseEnd_197653] using wordTrace_append hprefix tailTrace_197653
  have hstable : (prefixWord ++ tailWord_197653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197653).length < 2 ^ (prefixWord ++ tailWord_197653).sum := by decide
  have hdescent : baseEnd_197653 < baseStart_197653 := by decide
  rcases family_descends (prefixWord ++ tailWord_197653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197674 : List Nat := [3, 1, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_197674 : Nat := 118140960795 + 197674 * 2 ^ 59
def prefixEnd_197674 : Nat := 4983230072969 + 3 ^ 40 * 197674 * 2
def baseEnd_197674 : Nat := 67667849931309888843947

theorem tailTrace_197674 : CollatzResearch.WordTrace tailWord_197674 prefixEnd_197674 67667849931309888843947 := by
  unfold tailWord_197674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802440771467083219134019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4806508723912221917690717 1802440771467083219134019)
  ·
    refine ⟨2703661157200624828701029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802440771467083219134019 2703661157200624828701029)
    ·
      refine ⟨506936466975117155381443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2703661157200624828701029 506936466975117155381443)
      ·
        refine ⟨760404700462675733072165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506936466975117155381443 760404700462675733072165)
        ·
          refine ⟨142575881336751699951031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 760404700462675733072165 142575881336751699951031)
          ·
            refine ⟨213863822005127549926547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142575881336751699951031 213863822005127549926547)
            ·
              refine ⟨320795733007691324889821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213863822005127549926547 320795733007691324889821)
              ·
                refine ⟨120298399877884246833683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320795733007691324889821 120298399877884246833683)
                ·
                  refine ⟨180447599816826370250525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120298399877884246833683 180447599816826370250525)
                  ·
                    refine ⟨67667849931309888843947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180447599816826370250525 67667849931309888843947)
                    ·
                      rfl

theorem cell22_197674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_197674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197674 prefixEnd_197674 := by exact prefixLift 197674
  have htrace : WordTrace (prefixWord ++ tailWord_197674) baseStart_197674 baseEnd_197674 := by
    simpa [prefixWord, tailWord_197674, baseEnd_197674] using wordTrace_append hprefix tailTrace_197674
  have hstable : (prefixWord ++ tailWord_197674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197674).length < 2 ^ (prefixWord ++ tailWord_197674).sum := by decide
  have hdescent : baseEnd_197674 < baseStart_197674 := by decide
  rcases family_descends (prefixWord ++ tailWord_197674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197696 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 4, 3]
def baseStart_197696 : Nat := 118140960795 + 197696 * 2 ^ 59
def prefixEnd_197696 : Nat := 4983230072969 + 3 ^ 40 * 197696 * 2
def baseEnd_197696 : Nat := 67675380980909164793879

theorem tailTrace_197696 : CollatzResearch.WordTrace tailWord_197696 prefixEnd_197696 67675380980909164793879 := by
  unfold tailWord_197696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605282745894315316918471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4807043661192420422557961 3605282745894315316918471)
  ·
    refine ⟨5407924118841472975377707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605282745894315316918471 5407924118841472975377707)
    ·
      refine ⟨8111886178262209463066561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5407924118841472975377707 8111886178262209463066561)
      ·
        refine ⟨6083914633696657097299921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8111886178262209463066561 6083914633696657097299921)
        ·
          refine ⟨4562935975272492822974941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6083914633696657097299921 4562935975272492822974941)
          ·
            refine ⟨1711100990727184808615603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4562935975272492822974941 1711100990727184808615603)
            ·
              refine ⟨2566651486090777212923405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711100990727184808615603 2566651486090777212923405)
              ·
                refine ⟨962494307284041454846277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2566651486090777212923405 962494307284041454846277)
                ·
                  refine ⟨180467682615757772783677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962494307284041454846277 180467682615757772783677)
                  ·
                    refine ⟨67675380980909164793879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180467682615757772783677 67675380980909164793879)
                    ·
                      rfl

theorem cell22_197696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_197696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197696 prefixEnd_197696 := by exact prefixLift 197696
  have htrace : WordTrace (prefixWord ++ tailWord_197696) baseStart_197696 baseEnd_197696 := by
    simpa [prefixWord, tailWord_197696, baseEnd_197696] using wordTrace_append hprefix tailTrace_197696
  have hstable : (prefixWord ++ tailWord_197696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197696).length < 2 ^ (prefixWord ++ tailWord_197696).sum := by decide
  have hdescent : baseEnd_197696 < baseStart_197696 := by decide
  rcases family_descends (prefixWord ++ tailWord_197696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197739 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 6, 6]
def baseStart_197739 : Nat := 118140960795 + 197739 * 2 ^ 59
def prefixEnd_197739 : Nat := 4983230072969 + 3 ^ 40 * 197739 * 2
def baseEnd_197739 : Nat := 67690100759671385968747

theorem tailTrace_197739 : CollatzResearch.WordTrace tailWord_197739 prefixEnd_197739 67690100759671385968747 := by
  unfold tailWord_197739
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212133830632848977652271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4808089220421899318434847 7212133830632848977652271)
  ·
    refine ⟨10818200745949273466478407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7212133830632848977652271 10818200745949273466478407)
    ·
      refine ⟨16227301118923910199717611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10818200745949273466478407 16227301118923910199717611)
      ·
        refine ⟨24340951678385865299576417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16227301118923910199717611 24340951678385865299576417)
        ·
          refine ⟨18255713758789398974682313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24340951678385865299576417 18255713758789398974682313)
          ·
            refine ⟨13691785319092049231011735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18255713758789398974682313 13691785319092049231011735)
            ·
              refine ⟨20537677978638073846517603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13691785319092049231011735 20537677978638073846517603)
              ·
                refine ⟨30806516967957110769776405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20537677978638073846517603 30806516967957110769776405)
                ·
                  refine ⟨1444055482872989567333269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30806516967957110769776405 1444055482872989567333269)
                  ·
                    refine ⟨67690100759671385968747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1444055482872989567333269 67690100759671385968747)
                    ·
                      rfl

theorem cell22_197739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_197739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197739 prefixEnd_197739 := by exact prefixLift 197739
  have htrace : WordTrace (prefixWord ++ tailWord_197739) baseStart_197739 baseEnd_197739 := by
    simpa [prefixWord, tailWord_197739, baseEnd_197739] using wordTrace_append hprefix tailTrace_197739
  have hstable : (prefixWord ++ tailWord_197739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197739).length < 2 ^ (prefixWord ++ tailWord_197739).sum := by decide
  have hdescent : baseEnd_197739 < baseStart_197739 := by decide
  rcases family_descends (prefixWord ++ tailWord_197739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197749 : List Nat := [1, 3, 4, 3, 1, 2, 2, 2, 4]
def baseStart_197749 : Nat := 118140960795 + 197749 * 2 ^ 59
def prefixEnd_197749 : Nat := 4983230072969 + 3 ^ 40 * 197749 * 2
def baseEnd_197749 : Nat := 22564507988011564406239

theorem tailTrace_197749 : CollatzResearch.WordTrace tailWord_197749 prefixEnd_197749 22564507988011564406239 := by
  unfold tailWord_197749
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212498560596620685516301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4808332373731080457010867 7212498560596620685516301)
  ·
    refine ⟨2704686960223732757068613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7212498560596620685516301 2704686960223732757068613)
    ·
      refine ⟨507128805041949891950365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2704686960223732757068613 507128805041949891950365)
      ·
        refine ⟨190173301890731209481387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507128805041949891950365 190173301890731209481387)
        ·
          refine ⟨285259952836096814222081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190173301890731209481387 285259952836096814222081)
          ·
            refine ⟨213944964627072610666561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285259952836096814222081 213944964627072610666561)
            ·
              refine ⟨160458723470304457999921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213944964627072610666561 160458723470304457999921)
              ·
                refine ⟨120344042602728343499941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160458723470304457999921 120344042602728343499941)
                ·
                  refine ⟨22564507988011564406239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120344042602728343499941 22564507988011564406239)
                  ·
                    rfl

theorem cell22_197749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_197749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197749 prefixEnd_197749 := by exact prefixLift 197749
  have htrace : WordTrace (prefixWord ++ tailWord_197749) baseStart_197749 baseEnd_197749 := by
    simpa [prefixWord, tailWord_197749, baseEnd_197749] using wordTrace_append hprefix tailTrace_197749
  have hstable : (prefixWord ++ tailWord_197749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197749).length < 2 ^ (prefixWord ++ tailWord_197749).sum := by decide
  have hdescent : baseEnd_197749 < baseStart_197749 := by decide
  rcases family_descends (prefixWord ++ tailWord_197749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197893 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_197893 : Nat := 118140960795 + 197893 * 2 ^ 59
def prefixEnd_197893 : Nat := 4983230072969 + 3 ^ 40 * 197893 * 2
def baseEnd_197893 : Nat := 67742818106866317618275

theorem tailTrace_197893 : CollatzResearch.WordTrace tailWord_197893 prefixEnd_197893 67742818106866317618275 := by
  unfold tailWord_197893
  simp only [CollatzResearch.WordTrace]
  refine ⟨7217750672074933278758333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4811833781383288852505555 7217750672074933278758333)
  ·
    refine ⟨2706656502028099979534375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7217750672074933278758333 2706656502028099979534375)
    ·
      refine ⟨4059984753042149969301563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706656502028099979534375 4059984753042149969301563)
      ·
        refine ⟨6089977129563224953952345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059984753042149969301563 6089977129563224953952345)
        ·
          refine ⟨4567482847172418715464259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6089977129563224953952345 4567482847172418715464259)
          ·
            refine ⟨6851224270758628073196389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567482847172418715464259 6851224270758628073196389)
            ·
              refine ⟨1284604550767242763724323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6851224270758628073196389 1284604550767242763724323)
              ·
                refine ⟨1926906826150864145586485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284604550767242763724323 1926906826150864145586485)
                ·
                  refine ⟨180647514951643513648733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1926906826150864145586485 180647514951643513648733)
                  ·
                    refine ⟨67742818106866317618275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180647514951643513648733 67742818106866317618275)
                    ·
                      rfl

theorem cell22_197893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_197893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197893 prefixEnd_197893 := by exact prefixLift 197893
  have htrace : WordTrace (prefixWord ++ tailWord_197893) baseStart_197893 baseEnd_197893 := by
    simpa [prefixWord, tailWord_197893, baseEnd_197893] using wordTrace_append hprefix tailTrace_197893
  have hstable : (prefixWord ++ tailWord_197893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197893).length < 2 ^ (prefixWord ++ tailWord_197893).sum := by decide
  have hdescent : baseEnd_197893 < baseStart_197893 := by decide
  rcases family_descends (prefixWord ++ tailWord_197893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197918 : List Nat := [4, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_197918 : Nat := 118140960795 + 197918 * 2 ^ 59
def prefixEnd_197918 : Nat := 4983230072969 + 3 ^ 40 * 197918 * 2
def baseEnd_197918 : Nat := 22583792039258195247733

theorem tailTrace_197918 : CollatzResearch.WordTrace tailWord_197918 prefixEnd_197918 22583792039258195247733 := by
  unfold tailWord_197918
  simp only [CollatzResearch.WordTrace]
  refine ⟨902332812123045318552301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4812441664656241698945605 902332812123045318552301)
  ·
    refine ⟨338374804546141994457113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 902332812123045318552301 338374804546141994457113)
    ·
      refine ⟨253781103409606495842835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338374804546141994457113 253781103409606495842835)
      ·
        refine ⟨380671655114409743764253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253781103409606495842835 380671655114409743764253)
        ·
          refine ⟨142751870667903653911595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380671655114409743764253 142751870667903653911595)
          ·
            refine ⟨214127806001855480867393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142751870667903653911595 214127806001855480867393)
            ·
              refine ⟨160595854501391610650545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214127806001855480867393 160595854501391610650545)
              ·
                refine ⟨120446890876043707987909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160595854501391610650545 120446890876043707987909)
                ·
                  refine ⟨22583792039258195247733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120446890876043707987909 22583792039258195247733)
                  ·
                    rfl

theorem cell22_197918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_197918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197918 prefixEnd_197918 := by exact prefixLift 197918
  have htrace : WordTrace (prefixWord ++ tailWord_197918) baseStart_197918 baseEnd_197918 := by
    simpa [prefixWord, tailWord_197918, baseEnd_197918] using wordTrace_append hprefix tailTrace_197918
  have hstable : (prefixWord ++ tailWord_197918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197918).length < 2 ^ (prefixWord ++ tailWord_197918).sum := by decide
  have hdescent : baseEnd_197918 < baseStart_197918 := by decide
  rcases family_descends (prefixWord ++ tailWord_197918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197923 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 5]
def baseStart_197923 : Nat := 118140960795 + 197923 * 2 ^ 59
def prefixEnd_197923 : Nat := 4983230072969 + 3 ^ 40 * 197923 * 2
def baseEnd_197923 : Nat := 22584362573318746456061

theorem tailTrace_197923 : CollatzResearch.WordTrace tailWord_197923 prefixEnd_197923 22584362573318746456061 := by
  unfold tailWord_197923
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218844861966248402350423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4812563241310832268233615 7218844861966248402350423)
  ·
    refine ⟨10828267292949372603525635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7218844861966248402350423 10828267292949372603525635)
    ·
      refine ⟨16242400939424058905288453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10828267292949372603525635 16242400939424058905288453)
      ·
        refine ⟨3045450176142011044741585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16242400939424058905288453 3045450176142011044741585)
        ·
          refine ⟨2284087632106508283556189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3045450176142011044741585 2284087632106508283556189)
          ·
            refine ⟨856532862039940606333571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2284087632106508283556189 856532862039940606333571)
            ·
              refine ⟨1284799293059910909500357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856532862039940606333571 1284799293059910909500357)
              ·
                refine ⟨240899867448733295531317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1284799293059910909500357 240899867448733295531317)
                ·
                  refine ⟨22584362573318746456061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240899867448733295531317 22584362573318746456061)
                  ·
                    rfl

theorem cell22_197923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 5].length) (baseStart_197923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197923 prefixEnd_197923 := by exact prefixLift 197923
  have htrace : WordTrace (prefixWord ++ tailWord_197923) baseStart_197923 baseEnd_197923 := by
    simpa [prefixWord, tailWord_197923, baseEnd_197923] using wordTrace_append hprefix tailTrace_197923
  have hstable : (prefixWord ++ tailWord_197923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197923).length < 2 ^ (prefixWord ++ tailWord_197923).sum := by decide
  have hdescent : baseEnd_197923 < baseStart_197923 := by decide
  rcases family_descends (prefixWord ++ tailWord_197923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197938 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_197938 : Nat := 118140960795 + 197938 * 2 ^ 59
def prefixEnd_197938 : Nat := 4983230072969 + 3 ^ 40 * 197938 * 2
def baseEnd_197938 : Nat := 67758222526501200243137

theorem tailTrace_197938 : CollatzResearch.WordTrace tailWord_197938 prefixEnd_197938 67758222526501200243137 := by
  unfold tailWord_197938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1804847989227976491036617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4812927971274603976097645 1804847989227976491036617)
  ·
    refine ⟨1353635991920982368277463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1804847989227976491036617 1353635991920982368277463)
    ·
      refine ⟨2030453987881473552416195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1353635991920982368277463 2030453987881473552416195)
      ·
        refine ⟨3045680981822210328624293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030453987881473552416195 3045680981822210328624293)
        ·
          refine ⟨571065184091664436617055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3045680981822210328624293 571065184091664436617055)
          ·
            refine ⟨856597776137496654925583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571065184091664436617055 856597776137496654925583)
            ·
              refine ⟨1284896664206244982388375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856597776137496654925583 1284896664206244982388375)
              ·
                refine ⟨1927344996309367473582563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284896664206244982388375 1927344996309367473582563)
                ·
                  refine ⟨2891017494464051210373845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927344996309367473582563 2891017494464051210373845)
                  ·
                    refine ⟨67758222526501200243137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2891017494464051210373845 67758222526501200243137)
                    ·
                      rfl

theorem cell22_197938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_197938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197938 prefixEnd_197938 := by exact prefixLift 197938
  have htrace : WordTrace (prefixWord ++ tailWord_197938) baseStart_197938 baseEnd_197938 := by
    simpa [prefixWord, tailWord_197938, baseEnd_197938] using wordTrace_append hprefix tailTrace_197938
  have hstable : (prefixWord ++ tailWord_197938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197938).length < 2 ^ (prefixWord ++ tailWord_197938).sum := by decide
  have hdescent : baseEnd_197938 < baseStart_197938 := by decide
  rcases family_descends (prefixWord ++ tailWord_197938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197940 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 5]
def baseStart_197940 : Nat := 118140960795 + 197940 * 2 ^ 59
def prefixEnd_197940 : Nat := 4983230072969 + 3 ^ 40 * 197940 * 2
def baseEnd_197940 : Nat := 22586302389124620564377

theorem tailTrace_197940 : CollatzResearch.WordTrace tailWord_197940 prefixEnd_197940 22586302389124620564377 := by
  unfold tailWord_197940
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609732451452330152859637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4812976601936440203812849 3609732451452330152859637)
  ·
    refine ⟨338412417323655951830591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3609732451452330152859637 338412417323655951830591)
    ·
      refine ⟨507618625985483927745887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338412417323655951830591 507618625985483927745887)
      ·
        refine ⟨761427938978225891618831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507618625985483927745887 761427938978225891618831)
        ·
          refine ⟨1142141908467338837428247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761427938978225891618831 1142141908467338837428247)
          ·
            refine ⟨1713212862701008256142371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142141908467338837428247 1713212862701008256142371)
            ·
              refine ⟨2569819294051512384213557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713212862701008256142371 2569819294051512384213557)
              ·
                refine ⟨240920558817329286020021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2569819294051512384213557 240920558817329286020021)
                ·
                  refine ⟨22586302389124620564377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240920558817329286020021 22586302389124620564377)
                  ·
                    rfl

theorem cell22_197940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_197940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_197940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_197940 prefixEnd_197940 := by exact prefixLift 197940
  have htrace : WordTrace (prefixWord ++ tailWord_197940) baseStart_197940 baseEnd_197940 := by
    simpa [prefixWord, tailWord_197940, baseEnd_197940] using wordTrace_append hprefix tailTrace_197940
  have hstable : (prefixWord ++ tailWord_197940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197940).length < 2 ^ (prefixWord ++ tailWord_197940).sum := by decide
  have hdescent : baseEnd_197940 < baseStart_197940 := by decide
  rcases family_descends (prefixWord ++ tailWord_197940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198013 : List Nat := [1, 4, 1, 1, 2, 2, 3, 8]
def baseStart_198013 : Nat := 118140960795 + 198013 * 2 ^ 59
def prefixEnd_198013 : Nat := 4983230072969 + 3 ^ 40 * 198013 * 2
def baseEnd_198013 : Nat := 7531544062136222735323

theorem tailTrace_198013 : CollatzResearch.WordTrace tailWord_198013 prefixEnd_198013 7531544062136222735323 := by
  unfold tailWord_198013
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222127431640193773126693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4814751621093462515417795 7222127431640193773126693)
  ·
    refine ⟨1354148893432536332461255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7222127431640193773126693 1354148893432536332461255)
    ·
      refine ⟨2031223340148804498691883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354148893432536332461255 2031223340148804498691883)
      ·
        refine ⟨3046835010223206748037825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031223340148804498691883 3046835010223206748037825)
        ·
          refine ⟨2285126257667405061028369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3046835010223206748037825 2285126257667405061028369)
          ·
            refine ⟨1713844693250553795771277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2285126257667405061028369 1713844693250553795771277)
            ·
              refine ⟨642691759968957673414229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1713844693250553795771277 642691759968957673414229)
              ·
                refine ⟨7531544062136222735323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 642691759968957673414229 7531544062136222735323)
                ·
                  rfl

theorem cell22_198013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 8].length) (baseStart_198013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198013 prefixEnd_198013 := by exact prefixLift 198013
  have htrace : WordTrace (prefixWord ++ tailWord_198013) baseStart_198013 baseEnd_198013 := by
    simpa [prefixWord, tailWord_198013, baseEnd_198013] using wordTrace_append hprefix tailTrace_198013
  have hstable : (prefixWord ++ tailWord_198013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198013).length < 2 ^ (prefixWord ++ tailWord_198013).sum := by decide
  have hdescent : baseEnd_198013 < baseStart_198013 := by decide
  rcases family_descends (prefixWord ++ tailWord_198013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198092 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 5]
def baseStart_198092 : Nat := 118140960795 + 198092 * 2 ^ 59
def prefixEnd_198092 : Nat := 4983230072969 + 3 ^ 40 * 198092 * 2
def baseEnd_198092 : Nat := 22603646624565377297555

theorem tailTrace_198092 : CollatzResearch.WordTrace tailWord_198092 prefixEnd_198092 22603646624565377297555 := by
  unfold tailWord_198092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3612504399176995132626265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4816672532235993510168353 3612504399176995132626265)
  ·
    refine ⟨2709378299382746349469699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3612504399176995132626265 2709378299382746349469699)
    ·
      refine ⟨4064067449074119524204549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2709378299382746349469699 4064067449074119524204549)
      ·
        refine ⟨762012646701397410788353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4064067449074119524204549 762012646701397410788353)
        ·
          refine ⟨571509485026048058091265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762012646701397410788353 571509485026048058091265)
          ·
            refine ⟨428632113769536043568449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571509485026048058091265 428632113769536043568449)
            ·
              refine ⟨321474085327152032676337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428632113769536043568449 321474085327152032676337)
              ·
                refine ⟨241105563995364024507253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321474085327152032676337 241105563995364024507253)
                ·
                  refine ⟨22603646624565377297555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241105563995364024507253 22603646624565377297555)
                  ·
                    rfl

theorem cell22_198092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_198092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198092 prefixEnd_198092 := by exact prefixLift 198092
  have htrace : WordTrace (prefixWord ++ tailWord_198092) baseStart_198092 baseEnd_198092 := by
    simpa [prefixWord, tailWord_198092, baseEnd_198092] using wordTrace_append hprefix tailTrace_198092
  have hstable : (prefixWord ++ tailWord_198092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198092).length < 2 ^ (prefixWord ++ tailWord_198092).sum := by decide
  have hdescent : baseEnd_198092 < baseStart_198092 := by decide
  rcases family_descends (prefixWord ++ tailWord_198092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198103 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 10]
def baseStart_198103 : Nat := 118140960795 + 198103 * 2 ^ 59
def prefixEnd_198103 : Nat := 4983230072969 + 3 ^ 40 * 198103 * 2
def baseEnd_198103 : Nat := 22604901799498589955877

theorem tailTrace_198103 : CollatzResearch.WordTrace tailWord_198103 prefixEnd_198103 22604901799498589955877 := by
  unfold tailWord_198103
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225410001314139143902963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4816940000876092762601975 7225410001314139143902963)
  ·
    refine ⟨10838115001971208715854445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7225410001314139143902963 10838115001971208715854445)
    ·
      refine ⟨4064293125739203268445417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10838115001971208715854445 4064293125739203268445417)
      ·
        refine ⟨3048219844304402451334063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4064293125739203268445417 3048219844304402451334063)
        ·
          refine ⟨4572329766456603677001095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3048219844304402451334063 4572329766456603677001095)
          ·
            refine ⟨6858494649684905515501643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4572329766456603677001095 6858494649684905515501643)
            ·
              refine ⟨10287741974527358273252465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6858494649684905515501643 10287741974527358273252465)
              ·
                refine ⟨7715806480895518704939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10287741974527358273252465 7715806480895518704939349)
                ·
                  refine ⟨22604901799498589955877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 7715806480895518704939349 22604901799498589955877)
                  ·
                    rfl

theorem cell22_198103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 10].length) (baseStart_198103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198103 prefixEnd_198103 := by exact prefixLift 198103
  have htrace : WordTrace (prefixWord ++ tailWord_198103) baseStart_198103 baseEnd_198103 := by
    simpa [prefixWord, tailWord_198103, baseEnd_198103] using wordTrace_append hprefix tailTrace_198103
  have hstable : (prefixWord ++ tailWord_198103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198103).length < 2 ^ (prefixWord ++ tailWord_198103).sum := by decide
  have hdescent : baseEnd_198103 < baseStart_198103 := by decide
  rcases family_descends (prefixWord ++ tailWord_198103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198105 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_198105 : Nat := 118140960795 + 198105 * 2 ^ 59
def prefixEnd_198105 : Nat := 4983230072969 + 3 ^ 40 * 198105 * 2
def baseEnd_198105 : Nat := 67815390039368431317625

theorem tailTrace_198105 : CollatzResearch.WordTrace tailWord_198105 prefixEnd_198105 67815390039368431317625 := by
  unfold tailWord_198105
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225482947306893485475769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4816988631537928990317179 7225482947306893485475769)
  ·
    refine ⟨5419112210480170114106827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7225482947306893485475769 5419112210480170114106827)
    ·
      refine ⟨8128668315720255171160241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5419112210480170114106827 8128668315720255171160241)
      ·
        refine ⟨6096501236790191378370181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8128668315720255171160241 6096501236790191378370181)
        ·
          refine ⟨1143093981898160883444409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6096501236790191378370181 1143093981898160883444409)
          ·
            refine ⟨857320486423620662583307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143093981898160883444409 857320486423620662583307)
            ·
              refine ⟨1285980729635430993874961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857320486423620662583307 1285980729635430993874961)
              ·
                refine ⟨964485547226573245406221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1285980729635430993874961 964485547226573245406221)
                ·
                  refine ⟨361682080209964967027333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964485547226573245406221 361682080209964967027333)
                  ·
                    refine ⟨67815390039368431317625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 361682080209964967027333 67815390039368431317625)
                    ·
                      rfl

theorem cell22_198105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_198105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198105 prefixEnd_198105 := by exact prefixLift 198105
  have htrace : WordTrace (prefixWord ++ tailWord_198105) baseStart_198105 baseEnd_198105 := by
    simpa [prefixWord, tailWord_198105, baseEnd_198105] using wordTrace_append hprefix tailTrace_198105
  have hstable : (prefixWord ++ tailWord_198105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198105).length < 2 ^ (prefixWord ++ tailWord_198105).sum := by decide
  have hdescent : baseEnd_198105 < baseStart_198105 := by decide
  rcases family_descends (prefixWord ++ tailWord_198105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198120 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 6]
def baseStart_198120 : Nat := 118140960795 + 198120 * 2 ^ 59
def prefixEnd_198120 : Nat := 4983230072969 + 3 ^ 40 * 198120 * 2
def baseEnd_198120 : Nat := 22606841615304464064193

theorem tailTrace_198120 : CollatzResearch.WordTrace tailWord_198120 prefixEnd_198120 22606841615304464064193 := by
  unfold tailWord_198120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613015021126275523635907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4817353361501700698181209 3613015021126275523635907)
  ·
    refine ⟨5419522531689413285453861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3613015021126275523635907 5419522531689413285453861)
    ·
      refine ⟨1016160474691764991022599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5419522531689413285453861 1016160474691764991022599)
      ·
        refine ⟨1524240712037647486533899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016160474691764991022599 1524240712037647486533899)
        ·
          refine ⟨2286361068056471229800849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524240712037647486533899 2286361068056471229800849)
          ·
            refine ⟨1714770801042353422350637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2286361068056471229800849 1714770801042353422350637)
            ·
              refine ⟨643039050390882533381489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1714770801042353422350637 643039050390882533381489)
              ·
                refine ⟨482279287793161900036117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643039050390882533381489 482279287793161900036117)
                ·
                  refine ⟨22606841615304464064193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 482279287793161900036117 22606841615304464064193)
                  ·
                    rfl

theorem cell22_198120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_198120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198120 prefixEnd_198120 := by exact prefixLift 198120
  have htrace : WordTrace (prefixWord ++ tailWord_198120) baseStart_198120 baseEnd_198120 := by
    simpa [prefixWord, tailWord_198120, baseEnd_198120] using wordTrace_append hprefix tailTrace_198120
  have hstable : (prefixWord ++ tailWord_198120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198120).length < 2 ^ (prefixWord ++ tailWord_198120).sum := by decide
  have hdescent : baseEnd_198120 < baseStart_198120 := by decide
  rcases family_descends (prefixWord ++ tailWord_198120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198225 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_198225 : Nat := 118140960795 + 198225 * 2 ^ 59
def prefixEnd_198225 : Nat := 4983230072969 + 3 ^ 40 * 198225 * 2
def baseEnd_198225 : Nat := 67856468491728118317257

theorem tailTrace_198225 : CollatzResearch.WordTrace tailWord_198225 prefixEnd_198225 67856468491728118317257 := by
  unfold tailWord_198225
  simp only [CollatzResearch.WordTrace]
  refine ⟨7229859706872153979844129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4819906471248102653229419 7229859706872153979844129)
  ·
    refine ⟨5422394780154115484883097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7229859706872153979844129 5422394780154115484883097)
    ·
      refine ⟨4066796085115586613662323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5422394780154115484883097 4066796085115586613662323)
      ·
        refine ⟨6100194127673379920493485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066796085115586613662323 6100194127673379920493485)
        ·
          refine ⟨2287572797877517470185057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6100194127673379920493485 2287572797877517470185057)
          ·
            refine ⟨1715679598408138102638793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287572797877517470185057 1715679598408138102638793)
            ·
              refine ⟨1286759698806103576979095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715679598408138102638793 1286759698806103576979095)
              ·
                refine ⟨1930139548209155365468643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286759698806103576979095 1930139548209155365468643)
                ·
                  refine ⟨2895209322313733048202965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930139548209155365468643 2895209322313733048202965)
                  ·
                    refine ⟨67856468491728118317257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2895209322313733048202965 67856468491728118317257)
                    ·
                      rfl

theorem cell22_198225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_198225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198225 prefixEnd_198225 := by exact prefixLift 198225
  have htrace : WordTrace (prefixWord ++ tailWord_198225) baseStart_198225 baseEnd_198225 := by
    simpa [prefixWord, tailWord_198225, baseEnd_198225] using wordTrace_append hprefix tailTrace_198225
  have hstable : (prefixWord ++ tailWord_198225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198225).length < 2 ^ (prefixWord ++ tailWord_198225).sum := by decide
  have hdescent : baseEnd_198225 < baseStart_198225 := by decide
  rcases family_descends (prefixWord ++ tailWord_198225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198257 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_198257 : Nat := 118140960795 + 198257 * 2 ^ 59
def prefixEnd_198257 : Nat := 4983230072969 + 3 ^ 40 * 198257 * 2
def baseEnd_198257 : Nat := 67867422745690701517159

theorem tailTrace_198257 : CollatzResearch.WordTrace tailWord_198257 prefixEnd_198257 67867422745690701517159 := by
  unfold tailWord_198257
  simp only [CollatzResearch.WordTrace]
  refine ⟨7231026842756223445009025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4820684561837482296672683 7231026842756223445009025)
  ·
    refine ⟨5423270132067167583756769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7231026842756223445009025 5423270132067167583756769)
    ·
      refine ⟨4067452599050375687817577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5423270132067167583756769 4067452599050375687817577)
      ·
        refine ⟨3050589449287781765863183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4067452599050375687817577 3050589449287781765863183)
        ·
          refine ⟨4575884173931672648794775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050589449287781765863183 4575884173931672648794775)
          ·
            refine ⟨6863826260897508973192163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575884173931672648794775 6863826260897508973192163)
            ·
              refine ⟨10295739391346263459788245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863826260897508973192163 10295739391346263459788245)
              ·
                refine ⟨241306391984678049838787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10295739391346263459788245 241306391984678049838787)
                ·
                  refine ⟨361959587977017074758181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241306391984678049838787 361959587977017074758181)
                  ·
                    refine ⟨67867422745690701517159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 361959587977017074758181 67867422745690701517159)
                    ·
                      rfl

theorem cell22_198257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_198257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198257 prefixEnd_198257 := by exact prefixLift 198257
  have htrace : WordTrace (prefixWord ++ tailWord_198257) baseStart_198257 baseEnd_198257 := by
    simpa [prefixWord, tailWord_198257, baseEnd_198257] using wordTrace_append hprefix tailTrace_198257
  have hstable : (prefixWord ++ tailWord_198257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198257).length < 2 ^ (prefixWord ++ tailWord_198257).sum := by decide
  have hdescent : baseEnd_198257 < baseStart_198257 := by decide
  rcases family_descends (prefixWord ++ tailWord_198257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198317 : List Nat := [1, 5, 2, 1, 1, 1, 11]
def baseStart_198317 : Nat := 118140960795 + 198317 * 2 ^ 59
def prefixEnd_198317 : Nat := 4983230072969 + 3 ^ 40 * 198317 * 2
def baseEnd_198317 : Nat := 2514368961921131296925

theorem tailTrace_198317 : CollatzResearch.WordTrace tailWord_198317 prefixEnd_198317 2514368961921131296925 := by
  unfold tailWord_198317
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233215222538853692193205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4822143481692569128128803 7233215222538853692193205)
  ·
    refine ⟨678113927113017533643113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7233215222538853692193205 678113927113017533643113)
    ·
      refine ⟨508585445334763150232335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678113927113017533643113 508585445334763150232335)
      ·
        refine ⟨762878168002144725348503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508585445334763150232335 762878168002144725348503)
        ·
          refine ⟨1144317252003217088022755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762878168002144725348503 1144317252003217088022755)
          ·
            refine ⟨1716475878004825632034133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144317252003217088022755 1716475878004825632034133)
            ·
              refine ⟨2514368961921131296925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1716475878004825632034133 2514368961921131296925)
              ·
                rfl

theorem cell22_198317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 11].length) (baseStart_198317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198317 prefixEnd_198317 := by exact prefixLift 198317
  have htrace : WordTrace (prefixWord ++ tailWord_198317) baseStart_198317 baseEnd_198317 := by
    simpa [prefixWord, tailWord_198317, baseEnd_198317] using wordTrace_append hprefix tailTrace_198317
  have hstable : (prefixWord ++ tailWord_198317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198317).length < 2 ^ (prefixWord ++ tailWord_198317).sum := by decide
  have hdescent : baseEnd_198317 < baseStart_198317 := by decide
  rcases family_descends (prefixWord ++ tailWord_198317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198362 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_198362 : Nat := 118140960795 + 198362 * 2 ^ 59
def prefixEnd_198362 : Nat := 4983230072969 + 3 ^ 40 * 198362 * 2
def baseEnd_198362 : Nat := 22634455463835142547279

theorem tailTrace_198362 : CollatzResearch.WordTrace tailWord_198362 prefixEnd_198362 22634455463835142547279 := by
  unfold tailWord_198362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808714126843956594395335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4823237671583884251720893 1808714126843956594395335)
  ·
    refine ⟨2713071190265934891593003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1808714126843956594395335 2713071190265934891593003)
    ·
      refine ⟨4069606785398902337389505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2713071190265934891593003 4069606785398902337389505)
      ·
        refine ⟨3052205089049176753042129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4069606785398902337389505 3052205089049176753042129)
        ·
          refine ⟨2289153816786882564781597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3052205089049176753042129 2289153816786882564781597)
          ·
            refine ⟨858432681295080961793099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2289153816786882564781597 858432681295080961793099)
            ·
              refine ⟨1287649021942621442689649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858432681295080961793099 1287649021942621442689649)
              ·
                refine ⟨965736766456966082017237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287649021942621442689649 965736766456966082017237)
                ·
                  refine ⟨22634455463835142547279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 965736766456966082017237 22634455463835142547279)
                  ·
                    rfl

theorem cell22_198362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_198362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198362 prefixEnd_198362 := by exact prefixLift 198362
  have htrace : WordTrace (prefixWord ++ tailWord_198362) baseStart_198362 baseEnd_198362 := by
    simpa [prefixWord, tailWord_198362, baseEnd_198362] using wordTrace_append hprefix tailTrace_198362
  have hstable : (prefixWord ++ tailWord_198362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198362).length < 2 ^ (prefixWord ++ tailWord_198362).sum := by decide
  have hdescent : baseEnd_198362 < baseStart_198362 := by decide
  rcases family_descends (prefixWord ++ tailWord_198362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198383 : List Nat := [1, 1, 2, 1, 5, 1, 5, 2, 1, 3]
def baseStart_198383 : Nat := 118140960795 + 198383 * 2 ^ 59
def prefixEnd_198383 : Nat := 4983230072969 + 3 ^ 40 * 198383 * 2
def baseEnd_198383 : Nat := 67910555120668372866773

theorem tailTrace_198383 : CollatzResearch.WordTrace tailWord_198383 prefixEnd_198383 67910555120668372866773 := by
  unfold tailWord_198383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235622440299746964095803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4823748293533164642730535 7235622440299746964095803)
  ·
    refine ⟨10853433660449620446143705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7235622440299746964095803 10853433660449620446143705)
    ·
      refine ⟨8140075245337215334607779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10853433660449620446143705 8140075245337215334607779)
      ·
        refine ⟨12210112868005823001911669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140075245337215334607779 12210112868005823001911669)
        ·
          refine ⟨1144698081375545906429219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12210112868005823001911669 1144698081375545906429219)
          ·
            refine ⟨1717047122063318859643829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144698081375545906429219 1717047122063318859643829)
            ·
              refine ⟨160973167693436143091609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1717047122063318859643829 160973167693436143091609)
              ·
                refine ⟨120729875770077107318707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160973167693436143091609 120729875770077107318707)
                ·
                  refine ⟨181094813655115660978061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120729875770077107318707 181094813655115660978061)
                  ·
                    refine ⟨67910555120668372866773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181094813655115660978061 67910555120668372866773)
                    ·
                      rfl

theorem cell22_198383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 3].length) (baseStart_198383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198383 prefixEnd_198383 := by exact prefixLift 198383
  have htrace : WordTrace (prefixWord ++ tailWord_198383) baseStart_198383 baseEnd_198383 := by
    simpa [prefixWord, tailWord_198383, baseEnd_198383] using wordTrace_append hprefix tailTrace_198383
  have hstable : (prefixWord ++ tailWord_198383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198383).length < 2 ^ (prefixWord ++ tailWord_198383).sum := by decide
  have hdescent : baseEnd_198383 < baseStart_198383 := by decide
  rcases family_descends (prefixWord ++ tailWord_198383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198430 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_198430 : Nat := 118140960795 + 198430 * 2 ^ 59
def prefixEnd_198430 : Nat := 4983230072969 + 3 ^ 40 * 198430 * 2
def baseEnd_198430 : Nat := 22642214727058638980543

theorem tailTrace_198430 : CollatzResearch.WordTrace tailWord_198430 prefixEnd_198430 22642214727058638980543 := by
  unfold tailWord_198430
  simp only [CollatzResearch.WordTrace]
  refine ⟨904667083891184248882093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4824891114086315994037829 904667083891184248882093)
  ·
    refine ⟨339250156459194093330785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 904667083891184248882093 339250156459194093330785)
    ·
      refine ⟨254437617344395569998089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339250156459194093330785 254437617344395569998089)
      ·
        refine ⟨190828213008296677498567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254437617344395569998089 190828213008296677498567)
        ·
          refine ⟨286242319512445016247851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190828213008296677498567 286242319512445016247851)
          ·
            refine ⟨429363479268667524371777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286242319512445016247851 429363479268667524371777)
            ·
              refine ⟨322022609451500643278833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429363479268667524371777 322022609451500643278833)
              ·
                refine ⟨241516957088625482459125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322022609451500643278833 241516957088625482459125)
                ·
                  refine ⟨22642214727058638980543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241516957088625482459125 22642214727058638980543)
                  ·
                    rfl

theorem cell22_198430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_198430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198430 prefixEnd_198430 := by exact prefixLift 198430
  have htrace : WordTrace (prefixWord ++ tailWord_198430) baseStart_198430 baseEnd_198430 := by
    simpa [prefixWord, tailWord_198430, baseEnd_198430] using wordTrace_append hprefix tailTrace_198430
  have hstable : (prefixWord ++ tailWord_198430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198430).length < 2 ^ (prefixWord ++ tailWord_198430).sum := by decide
  have hdescent : baseEnd_198430 < baseStart_198430 := by decide
  rcases family_descends (prefixWord ++ tailWord_198430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198456 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 2, 3]
def baseStart_198456 : Nat := 118140960795 + 198456 * 2 ^ 59
def prefixEnd_198456 : Nat := 4983230072969 + 3 ^ 40 * 198456 * 2
def baseEnd_198456 : Nat := 67935544512520515791549

theorem tailTrace_198456 : CollatzResearch.WordTrace tailWord_198456 prefixEnd_198456 67935544512520515791549 := by
  unfold tailWord_198456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3619142484517640215751611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4825523312690186954335481 3619142484517640215751611)
  ·
    refine ⟨5428713726776460323627417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3619142484517640215751611 5428713726776460323627417)
    ·
      refine ⟨4071535295082345242720563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5428713726776460323627417 4071535295082345242720563)
      ·
        refine ⟨6107302942623517864080845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071535295082345242720563 6107302942623517864080845)
        ·
          refine ⟨2290238603483819199030317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6107302942623517864080845 2290238603483819199030317)
          ·
            refine ⟨858839476306432199636369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2290238603483819199030317 858839476306432199636369)
            ·
              refine ⟨644129607229824149727277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858839476306432199636369 644129607229824149727277)
              ·
                refine ⟨241548602711184056147729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644129607229824149727277 241548602711184056147729)
                ·
                  refine ⟨181161452033388042110797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241548602711184056147729 181161452033388042110797)
                  ·
                    refine ⟨67935544512520515791549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181161452033388042110797 67935544512520515791549)
                    ·
                      rfl

theorem cell22_198456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_198456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198456 prefixEnd_198456 := by exact prefixLift 198456
  have htrace : WordTrace (prefixWord ++ tailWord_198456) baseStart_198456 baseEnd_198456 := by
    simpa [prefixWord, tailWord_198456, baseEnd_198456] using wordTrace_append hprefix tailTrace_198456
  have hstable : (prefixWord ++ tailWord_198456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198456).length < 2 ^ (prefixWord ++ tailWord_198456).sum := by decide
  have hdescent : baseEnd_198456 < baseStart_198456 := by decide
  rcases family_descends (prefixWord ++ tailWord_198456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198469 : List Nat := [1, 3, 1, 1, 1, 2, 7, 6]
def baseStart_198469 : Nat := 118140960795 + 198469 * 2 ^ 59
def prefixEnd_198469 : Nat := 4983230072969 + 3 ^ 40 * 198469 * 2
def baseEnd_198469 : Nat := 7548888297576979468501

theorem tailTrace_198469 : CollatzResearch.WordTrace tailWord_198469 prefixEnd_198469 7548888297576979468501 := by
  unfold tailWord_198469
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238759117988183651726461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4825839411992122434484307 7238759117988183651726461)
  ·
    refine ⟨2714534669245568869397423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7238759117988183651726461 2714534669245568869397423)
    ·
      refine ⟨4071802003868353304096135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714534669245568869397423 4071802003868353304096135)
      ·
        refine ⟨6107703005802529956144203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071802003868353304096135 6107703005802529956144203)
        ·
          refine ⟨9161554508703794934216305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107703005802529956144203 9161554508703794934216305)
          ·
            refine ⟨6871165881527846200662229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9161554508703794934216305 6871165881527846200662229)
            ·
              refine ⟨161042950348308895328021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6871165881527846200662229 161042950348308895328021)
              ·
                refine ⟨7548888297576979468501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161042950348308895328021 7548888297576979468501)
                ·
                  rfl

theorem cell22_198469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 6].length) (baseStart_198469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198469 prefixEnd_198469 := by exact prefixLift 198469
  have htrace : WordTrace (prefixWord ++ tailWord_198469) baseStart_198469 baseEnd_198469 := by
    simpa [prefixWord, tailWord_198469, baseEnd_198469] using wordTrace_append hprefix tailTrace_198469
  have hstable : (prefixWord ++ tailWord_198469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198469).length < 2 ^ (prefixWord ++ tailWord_198469).sum := by decide
  have hdescent : baseEnd_198469 < baseStart_198469 := by decide
  rcases family_descends (prefixWord ++ tailWord_198469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198552 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 3, 3]
def baseStart_198552 : Nat := 118140960795 + 198552 * 2 ^ 59
def prefixEnd_198552 : Nat := 4983230072969 + 3 ^ 40 * 198552 * 2
def baseEnd_198552 : Nat := 67968407274408265391255

theorem tailTrace_198552 : CollatzResearch.WordTrace tailWord_198552 prefixEnd_198552 67968407274408265391255 := by
  unfold tailWord_198552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620893188343744413498955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4827857584458325884665273 3620893188343744413498955)
  ·
    refine ⟨5431339782515616620248433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3620893188343744413498955 5431339782515616620248433)
    ·
      refine ⟨4073504836886712465186325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5431339782515616620248433 4073504836886712465186325)
      ·
        refine ⟨190945539229064646805609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4073504836886712465186325 190945539229064646805609)
        ·
          refine ⟨143209154421798485104207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190945539229064646805609 143209154421798485104207)
          ·
            refine ⟨214813731632697727656311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143209154421798485104207 214813731632697727656311)
            ·
              refine ⟨322220597449046591484467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214813731632697727656311 322220597449046591484467)
              ·
                refine ⟨483330896173569887226701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322220597449046591484467 483330896173569887226701)
                ·
                  refine ⟨181249086065088707710013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483330896173569887226701 181249086065088707710013)
                  ·
                    refine ⟨67968407274408265391255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181249086065088707710013 67968407274408265391255)
                    ·
                      rfl

theorem cell22_198552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_198552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198552 prefixEnd_198552 := by exact prefixLift 198552
  have htrace : WordTrace (prefixWord ++ tailWord_198552) baseStart_198552 baseEnd_198552 := by
    simpa [prefixWord, tailWord_198552, baseEnd_198552] using wordTrace_append hprefix tailTrace_198552
  have hstable : (prefixWord ++ tailWord_198552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198552).length < 2 ^ (prefixWord ++ tailWord_198552).sum := by decide
  have hdescent : baseEnd_198552 < baseStart_198552 := by decide
  rcases family_descends (prefixWord ++ tailWord_198552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198604 : List Nat := [2, 2, 1, 4, 1, 12]
def baseStart_198604 : Nat := 118140960795 + 198604 * 2 ^ 59
def prefixEnd_198604 : Nat := 4983230072969 + 3 ^ 40 * 198604 * 2
def baseEnd_198604 : Nat := 839335900457993371495

theorem tailTrace_198604 : CollatzResearch.WordTrace tailWord_198604 prefixEnd_198604 839335900457993371495 := by
  unfold tailWord_198604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621841486249550853945433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4829121981666067805260577 3621841486249550853945433)
  ·
    refine ⟨2716381114687163140459075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3621841486249550853945433 2716381114687163140459075)
    ·
      refine ⟨4074571672030744710688613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716381114687163140459075 4074571672030744710688613)
      ·
        refine ⟨763982188505764633254115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4074571672030744710688613 763982188505764633254115)
        ·
          refine ⟨1145973282758646949881173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763982188505764633254115 1145973282758646949881173)
          ·
            refine ⟨839335900457993371495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1145973282758646949881173 839335900457993371495)
            ·
              rfl

theorem cell22_198604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 12].length) (baseStart_198604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198604 prefixEnd_198604 := by exact prefixLift 198604
  have htrace : WordTrace (prefixWord ++ tailWord_198604) baseStart_198604 baseEnd_198604 := by
    simpa [prefixWord, tailWord_198604, baseEnd_198604] using wordTrace_append hprefix tailTrace_198604
  have hstable : (prefixWord ++ tailWord_198604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198604).length < 2 ^ (prefixWord ++ tailWord_198604).sum := by decide
  have hdescent : baseEnd_198604 < baseStart_198604 := by decide
  rcases family_descends (prefixWord ++ tailWord_198604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198606 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_198606 : Nat := 118140960795 + 198606 * 2 ^ 59
def prefixEnd_198606 : Nat := 4983230072969 + 3 ^ 40 * 198606 * 2
def baseEnd_198606 : Nat := 67986892577970124541089

theorem tailTrace_198606 : CollatzResearch.WordTrace tailWord_198606 prefixEnd_198606 67986892577970124541089 := by
  unfold tailWord_198606
  simp only [CollatzResearch.WordTrace]
  refine ⟨905469489811482006182959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4829170612327904032975781 905469489811482006182959)
  ·
    refine ⟨1358204234717223009274439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905469489811482006182959 1358204234717223009274439)
    ·
      refine ⟨2037306352075834513911659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358204234717223009274439 2037306352075834513911659)
      ·
        refine ⟨3055959528113751770867489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037306352075834513911659 3055959528113751770867489)
        ·
          refine ⟨2291969646085313828150617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055959528113751770867489 2291969646085313828150617)
          ·
            refine ⟨1718977234563985371112963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291969646085313828150617 1718977234563985371112963)
            ·
              refine ⟨2578465851845978056669445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718977234563985371112963 2578465851845978056669445)
              ·
                refine ⟨483462347221120885625521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2578465851845978056669445 483462347221120885625521)
                ·
                  refine ⟨362596760415840664219141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483462347221120885625521 362596760415840664219141)
                  ·
                    refine ⟨67986892577970124541089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 362596760415840664219141 67986892577970124541089)
                    ·
                      rfl

theorem cell22_198606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_198606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198606 prefixEnd_198606 := by exact prefixLift 198606
  have htrace : WordTrace (prefixWord ++ tailWord_198606) baseStart_198606 baseEnd_198606 := by
    simpa [prefixWord, tailWord_198606, baseEnd_198606] using wordTrace_append hprefix tailTrace_198606
  have hstable : (prefixWord ++ tailWord_198606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198606).length < 2 ^ (prefixWord ++ tailWord_198606).sum := by decide
  have hdescent : baseEnd_198606 < baseStart_198606 := by decide
  rcases family_descends (prefixWord ++ tailWord_198606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198610 : List Nat := [3, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_198610 : Nat := 118140960795 + 198610 * 2 ^ 59
def prefixEnd_198610 : Nat := 4983230072969 + 3 ^ 40 * 198610 * 2
def baseEnd_198610 : Nat := 22662753953238482480359

theorem tailTrace_198610 : CollatzResearch.WordTrace tailWord_198610 prefixEnd_198610 22662753953238482480359 := by
  unfold tailWord_198610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810975452619341183152321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4829267873651576488406189 1810975452619341183152321)
  ·
    refine ⟨1358231589464505887364241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1810975452619341183152321 1358231589464505887364241)
    ·
      refine ⟨1018673692098379415523181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1358231589464505887364241 1018673692098379415523181)
      ·
        refine ⟨382002634536892280821193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1018673692098379415523181 382002634536892280821193)
        ·
          refine ⟨286501975902669210615895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382002634536892280821193 286501975902669210615895)
          ·
            refine ⟨429752963854003815923843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286501975902669210615895 429752963854003815923843)
            ·
              refine ⟨644629445781005723885765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429752963854003815923843 644629445781005723885765)
              ·
                refine ⟨120868021083938573228581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644629445781005723885765 120868021083938573228581)
                ·
                  refine ⟨22662753953238482480359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120868021083938573228581 22662753953238482480359)
                  ·
                    rfl

theorem cell22_198610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_198610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198610 prefixEnd_198610 := by exact prefixLift 198610
  have htrace : WordTrace (prefixWord ++ tailWord_198610) baseStart_198610 baseEnd_198610 := by
    simpa [prefixWord, tailWord_198610, baseEnd_198610] using wordTrace_append hprefix tailTrace_198610
  have hstable : (prefixWord ++ tailWord_198610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198610).length < 2 ^ (prefixWord ++ tailWord_198610).sum := by decide
  have hdescent : baseEnd_198610 < baseStart_198610 := by decide
  rcases family_descends (prefixWord ++ tailWord_198610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198638 : List Nat := [4, 1, 2, 1, 3, 2, 3, 6]
def baseStart_198638 : Nat := 118140960795 + 198638 * 2 ^ 59
def prefixEnd_198638 : Nat := 4983230072969 + 3 ^ 40 * 198638 * 2
def baseEnd_198638 : Nat := 7555316314659189748999

theorem tailTrace_198638 : CollatzResearch.WordTrace tailWord_198638 prefixEnd_198638 7555316314659189748999 := by
  unfold tailWord_198638
  simp only [CollatzResearch.WordTrace]
  refine ⟨905615381796990689328571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4829948702917283676419045 905615381796990689328571)
  ·
    refine ⟨1358423072695486033992857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905615381796990689328571 1358423072695486033992857)
    ·
      refine ⟨1018817304521614525494643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1358423072695486033992857 1018817304521614525494643)
      ·
        refine ⟨1528225956782421788241965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018817304521614525494643 1528225956782421788241965)
        ·
          refine ⟨573084733793408170590737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1528225956782421788241965 573084733793408170590737)
          ·
            refine ⟨429813550345056127943053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573084733793408170590737 429813550345056127943053)
            ·
              refine ⟨161180081379396047978645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429813550345056127943053 161180081379396047978645)
              ·
                refine ⟨7555316314659189748999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161180081379396047978645 7555316314659189748999)
                ·
                  rfl

theorem cell22_198638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_198638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198638 prefixEnd_198638 := by exact prefixLift 198638
  have htrace : WordTrace (prefixWord ++ tailWord_198638) baseStart_198638 baseEnd_198638 := by
    simpa [prefixWord, tailWord_198638, baseEnd_198638] using wordTrace_append hprefix tailTrace_198638
  have hstable : (prefixWord ++ tailWord_198638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198638).length < 2 ^ (prefixWord ++ tailWord_198638).sum := by decide
  have hdescent : baseEnd_198638 < baseStart_198638 := by decide
  rcases family_descends (prefixWord ++ tailWord_198638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198670 : List Nat := [4, 1, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_198670 : Nat := 118140960795 + 198670 * 2 ^ 59
def prefixEnd_198670 : Nat := 4983230072969 + 3 ^ 40 * 198670 * 2
def baseEnd_198670 : Nat := 68008801085895290940893

theorem tailTrace_198670 : CollatzResearch.WordTrace tailWord_198670 prefixEnd_198670 68008801085895290940893 := by
  unfold tailWord_198670
  simp only [CollatzResearch.WordTrace]
  refine ⟨905761273782499372474183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4830726793506663319862309 905761273782499372474183)
  ·
    refine ⟨1358641910673749058711275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905761273782499372474183 1358641910673749058711275)
    ·
      refine ⟨2037962866010623588066913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358641910673749058711275 2037962866010623588066913)
      ·
        refine ⟨1528472149507967691050185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2037962866010623588066913 1528472149507967691050185)
        ·
          refine ⟨1146354112130975768287639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528472149507967691050185 1146354112130975768287639)
          ·
            refine ⟨1719531168196463652431459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146354112130975768287639 1719531168196463652431459)
            ·
              refine ⟨2579296752294695478647189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719531168196463652431459 2579296752294695478647189)
              ·
                refine ⟨120904535263813850561587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2579296752294695478647189 120904535263813850561587)
                ·
                  refine ⟨181356802895720775842381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120904535263813850561587 181356802895720775842381)
                  ·
                    refine ⟨68008801085895290940893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181356802895720775842381 68008801085895290940893)
                    ·
                      rfl

theorem cell22_198670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_198670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198670 prefixEnd_198670 := by exact prefixLift 198670
  have htrace : WordTrace (prefixWord ++ tailWord_198670) baseStart_198670 baseEnd_198670 := by
    simpa [prefixWord, tailWord_198670, baseEnd_198670] using wordTrace_append hprefix tailTrace_198670
  have hstable : (prefixWord ++ tailWord_198670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198670).length < 2 ^ (prefixWord ++ tailWord_198670).sum := by decide
  have hdescent : baseEnd_198670 < baseStart_198670 := by decide
  rcases family_descends (prefixWord ++ tailWord_198670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198756 : List Nat := [2, 3, 1, 1, 2, 1, 4, 8]
def baseStart_198756 : Nat := 118140960795 + 198756 * 2 ^ 59
def prefixEnd_198756 : Nat := 4983230072969 + 3 ^ 40 * 198756 * 2
def baseEnd_198756 : Nat := 7559804515935525921181

theorem tailTrace_198756 : CollatzResearch.WordTrace tailWord_198756 prefixEnd_198756 7559804515935525921181 := by
  unfold tailWord_198756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3624613433974215833712061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4832817911965621111616081 3624613433974215833712061)
  ·
    refine ⟨1359230037740330937642023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3624613433974215833712061 1359230037740330937642023)
    ·
      refine ⟨2038845056610496406463035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359230037740330937642023 2038845056610496406463035)
      ·
        refine ⟨3058267584915744609694553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038845056610496406463035 3058267584915744609694553)
        ·
          refine ⟨2293700688686808457270915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3058267584915744609694553 2293700688686808457270915)
          ·
            refine ⟨3440551033030212685906373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293700688686808457270915 3440551033030212685906373)
            ·
              refine ⟨645103318693164878607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3440551033030212685906373 645103318693164878607445)
              ·
                refine ⟨7559804515935525921181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 645103318693164878607445 7559804515935525921181)
                ·
                  rfl

theorem cell22_198756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 8].length) (baseStart_198756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198756 prefixEnd_198756 := by exact prefixLift 198756
  have htrace : WordTrace (prefixWord ++ tailWord_198756) baseStart_198756 baseEnd_198756 := by
    simpa [prefixWord, tailWord_198756, baseEnd_198756] using wordTrace_append hprefix tailTrace_198756
  have hstable : (prefixWord ++ tailWord_198756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198756).length < 2 ^ (prefixWord ++ tailWord_198756).sum := by decide
  have hdescent : baseEnd_198756 < baseStart_198756 := by decide
  rcases family_descends (prefixWord ++ tailWord_198756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198852 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 5]
def baseStart_198852 : Nat := 118140960795 + 198852 * 2 ^ 59
def prefixEnd_198852 : Nat := 4983230072969 + 3 ^ 40 * 198852 * 2
def baseEnd_198852 : Nat := 22690367801769160963445

theorem tailTrace_198852 : CollatzResearch.WordTrace tailWord_198852 prefixEnd_198852 22690367801769160963445 := by
  unfold tailWord_198852
  simp only [CollatzResearch.WordTrace]
  refine ⟨3626364137800320031459405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4835152183733760041945873 3626364137800320031459405)
  ·
    refine ⟨1359886551675120011797277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3626364137800320031459405 1359886551675120011797277)
    ·
      refine ⟨509957456878170004423979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1359886551675120011797277 509957456878170004423979)
      ·
        refine ⟨764936185317255006635969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509957456878170004423979 764936185317255006635969)
        ·
          refine ⟨573702138987941254976977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764936185317255006635969 573702138987941254976977)
          ·
            refine ⟨430276604240955941232733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573702138987941254976977 430276604240955941232733)
            ·
              refine ⟨161353726590358477962275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430276604240955941232733 161353726590358477962275)
              ·
                refine ⟨242030589885537716943413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161353726590358477962275 242030589885537716943413)
                ·
                  refine ⟨22690367801769160963445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242030589885537716943413 22690367801769160963445)
                  ·
                    rfl

theorem cell22_198852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_198852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198852 prefixEnd_198852 := by exact prefixLift 198852
  have htrace : WordTrace (prefixWord ++ tailWord_198852) baseStart_198852 baseEnd_198852 := by
    simpa [prefixWord, tailWord_198852, baseEnd_198852] using wordTrace_append hprefix tailTrace_198852
  have hstable : (prefixWord ++ tailWord_198852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198852).length < 2 ^ (prefixWord ++ tailWord_198852).sum := by decide
  have hdescent : baseEnd_198852 < baseStart_198852 := by decide
  rcases family_descends (prefixWord ++ tailWord_198852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198895 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 4, 3]
def baseStart_198895 : Nat := 118140960795 + 198895 * 2 ^ 59
def prefixEnd_198895 : Nat := 4983230072969 + 3 ^ 40 * 198895 * 2
def baseEnd_198895 : Nat := 68085823184069704065203

theorem tailTrace_198895 : CollatzResearch.WordTrace tailWord_198895 prefixEnd_198895 68085823184069704065203 := by
  unfold tailWord_198895
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254296614444858406734139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4836197742963238937822759 7254296614444858406734139)
  ·
    refine ⟨10881444921667287610101209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254296614444858406734139 10881444921667287610101209)
    ·
      refine ⟨8161083691250465707575907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10881444921667287610101209 8161083691250465707575907)
      ·
        refine ⟨12241625536875698561363861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161083691250465707575907 12241625536875698561363861)
        ·
          refine ⟨573826197041048370063931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12241625536875698561363861 573826197041048370063931)
          ·
            refine ⟨860739295561572555095897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573826197041048370063931 860739295561572555095897)
            ·
              refine ⟨645554471671179416321923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860739295561572555095897 645554471671179416321923)
              ·
                refine ⟨968331707506769124482885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645554471671179416321923 968331707506769124482885)
                ·
                  refine ⟨181562195157519210840541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968331707506769124482885 181562195157519210840541)
                  ·
                    refine ⟨68085823184069704065203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181562195157519210840541 68085823184069704065203)
                    ·
                      rfl

theorem cell22_198895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_198895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198895 prefixEnd_198895 := by exact prefixLift 198895
  have htrace : WordTrace (prefixWord ++ tailWord_198895) baseStart_198895 baseEnd_198895 := by
    simpa [prefixWord, tailWord_198895, baseEnd_198895] using wordTrace_append hprefix tailTrace_198895
  have hstable : (prefixWord ++ tailWord_198895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198895).length < 2 ^ (prefixWord ++ tailWord_198895).sum := by decide
  have hdescent : baseEnd_198895 < baseStart_198895 := by decide
  rcases family_descends (prefixWord ++ tailWord_198895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198908 : List Nat := [2, 2, 2, 1, 4, 1, 1, 9]
def baseStart_198908 : Nat := 118140960795 + 198908 * 2 ^ 59
def prefixEnd_198908 : Nat := 4983230072969 + 3 ^ 40 * 198908 * 2
def baseEnd_198908 : Nat := 7565585927749111498907

theorem tailTrace_198908 : CollatzResearch.WordTrace tailWord_198908 prefixEnd_198908 7565585927749111498907 := by
  unfold tailWord_198908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627385381698880813478689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4836513842265174417971585 3627385381698880813478689)
  ·
    refine ⟨2720539036274160610109017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3627385381698880813478689 2720539036274160610109017)
    ·
      refine ⟨2040404277205620457581763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2720539036274160610109017 2040404277205620457581763)
      ·
        refine ⟨3060606415808430686372645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040404277205620457581763 3060606415808430686372645)
        ·
          refine ⟨573863702964080753694871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3060606415808430686372645 573863702964080753694871)
          ·
            refine ⟨860795554446121130542307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573863702964080753694871 860795554446121130542307)
            ·
              refine ⟨1291193331669181695813461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860795554446121130542307 1291193331669181695813461)
              ·
                refine ⟨7565585927749111498907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1291193331669181695813461 7565585927749111498907)
                ·
                  rfl

theorem cell22_198908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 9].length) (baseStart_198908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198908 prefixEnd_198908 := by exact prefixLift 198908
  have htrace : WordTrace (prefixWord ++ tailWord_198908) baseStart_198908 baseEnd_198908 := by
    simpa [prefixWord, tailWord_198908, baseEnd_198908] using wordTrace_append hprefix tailTrace_198908
  have hstable : (prefixWord ++ tailWord_198908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198908).length < 2 ^ (prefixWord ++ tailWord_198908).sum := by decide
  have hdescent : baseEnd_198908 < baseStart_198908 := by decide
  rcases family_descends (prefixWord ++ tailWord_198908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198910 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_198910 : Nat := 118140960795 + 198910 * 2 ^ 59
def prefixEnd_198910 : Nat := 4983230072969 + 3 ^ 40 * 198910 * 2
def baseEnd_198910 : Nat := 68090957990614664940157

theorem tailTrace_198910 : CollatzResearch.WordTrace tailWord_198910 prefixEnd_198910 68090957990614664940157 := by
  unfold tailWord_198910
  simp only [CollatzResearch.WordTrace]
  refine ⟨906855463673814496066273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4836562472927010645686789 906855463673814496066273)
  ·
    refine ⟨680141597755360872049705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 906855463673814496066273 680141597755360872049705)
    ·
      refine ⟨510106198316520654037279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680141597755360872049705 510106198316520654037279)
      ·
        refine ⟨765159297474780981055919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510106198316520654037279 765159297474780981055919)
        ·
          refine ⟨1147738946212171471583879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765159297474780981055919 1147738946212171471583879)
          ·
            refine ⟨1721608419318257207375819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147738946212171471583879 1721608419318257207375819)
            ·
              refine ⟨2582412628977385811063729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721608419318257207375819 2582412628977385811063729)
              ·
                refine ⟨1936809471733039358297797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2582412628977385811063729 1936809471733039358297797)
                ·
                  refine ⟨363151775949944879680837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936809471733039358297797 363151775949944879680837)
                  ·
                    refine ⟨68090957990614664940157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 363151775949944879680837 68090957990614664940157)
                    ·
                      rfl

theorem cell22_198910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_198910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198910 prefixEnd_198910 := by exact prefixLift 198910
  have htrace : WordTrace (prefixWord ++ tailWord_198910) baseStart_198910 baseEnd_198910 := by
    simpa [prefixWord, tailWord_198910, baseEnd_198910] using wordTrace_append hprefix tailTrace_198910
  have hstable : (prefixWord ++ tailWord_198910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198910).length < 2 ^ (prefixWord ++ tailWord_198910).sum := by decide
  have hdescent : baseEnd_198910 < baseStart_198910 := by decide
  rcases family_descends (prefixWord ++ tailWord_198910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198912 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 2, 3]
def baseStart_198912 : Nat := 118140960795 + 198912 * 2 ^ 59
def prefixEnd_198912 : Nat := 4983230072969 + 3 ^ 40 * 198912 * 2
def baseEnd_198912 : Nat := 68091642631487326390151

theorem tailTrace_198912 : CollatzResearch.WordTrace tailWord_198912 prefixEnd_198912 68091642631487326390151 := by
  unfold tailWord_198912
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627458327691635155051495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4836611103588846873401993 3627458327691635155051495)
  ·
    refine ⟨5441187491537452732577243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3627458327691635155051495 5441187491537452732577243)
    ·
      refine ⟨8161781237306179098865865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5441187491537452732577243 8161781237306179098865865)
      ·
        refine ⟨6121335927979634324149399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8161781237306179098865865 6121335927979634324149399)
        ·
          refine ⟨9182003891969451486224099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121335927979634324149399 9182003891969451486224099)
          ·
            refine ⟨13773005837954177229336149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9182003891969451486224099 13773005837954177229336149)
            ·
              refine ⟨161402412163525514406283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 13773005837954177229336149 161402412163525514406283)
              ·
                refine ⟨242103618245288271609425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161402412163525514406283 242103618245288271609425)
                ·
                  refine ⟨181577713683966203707069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242103618245288271609425 181577713683966203707069)
                  ·
                    refine ⟨68091642631487326390151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181577713683966203707069 68091642631487326390151)
                    ·
                      rfl

theorem cell22_198912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_198912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198912 prefixEnd_198912 := by exact prefixLift 198912
  have htrace : WordTrace (prefixWord ++ tailWord_198912) baseStart_198912 baseEnd_198912 := by
    simpa [prefixWord, tailWord_198912, baseEnd_198912] using wordTrace_append hprefix tailTrace_198912
  have hstable : (prefixWord ++ tailWord_198912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198912).length < 2 ^ (prefixWord ++ tailWord_198912).sum := by decide
  have hdescent : baseEnd_198912 < baseStart_198912 := by decide
  rcases family_descends (prefixWord ++ tailWord_198912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198968 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_198968 : Nat := 118140960795 + 198968 * 2 ^ 59
def prefixEnd_198968 : Nat := 4983230072969 + 3 ^ 40 * 198968 * 2
def baseEnd_198968 : Nat := 68110812575921846989979

theorem tailTrace_198968 : CollatzResearch.WordTrace tailWord_198968 prefixEnd_198968 68110812575921846989979 := by
  unfold tailWord_198968
  simp only [CollatzResearch.WordTrace]
  refine ⟨3628479571590195937070779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4837972762120261249427705 3628479571590195937070779)
  ·
    refine ⟨5442719357385293905606169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3628479571590195937070779 5442719357385293905606169)
    ·
      refine ⟨4082039518038970429204627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5442719357385293905606169 4082039518038970429204627)
      ·
        refine ⟨6123059277058455643806941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082039518038970429204627 6123059277058455643806941)
        ·
          refine ⟨2296147228896920866427603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6123059277058455643806941 2296147228896920866427603)
          ·
            refine ⟨3444220843345381299641405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296147228896920866427603 3444220843345381299641405)
            ·
              refine ⟨1291582816254517987365527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3444220843345381299641405 1291582816254517987365527)
              ·
                refine ⟨1937374224381776981048291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291582816254517987365527 1937374224381776981048291)
                ·
                  refine ⟨2906061336572665471572437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937374224381776981048291 2906061336572665471572437)
                  ·
                    refine ⟨68110812575921846989979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2906061336572665471572437 68110812575921846989979)
                    ·
                      rfl

theorem cell22_198968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_198968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198968 prefixEnd_198968 := by exact prefixLift 198968
  have htrace : WordTrace (prefixWord ++ tailWord_198968) baseStart_198968 baseEnd_198968 := by
    simpa [prefixWord, tailWord_198968, baseEnd_198968] using wordTrace_append hprefix tailTrace_198968
  have hstable : (prefixWord ++ tailWord_198968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198968).length < 2 ^ (prefixWord ++ tailWord_198968).sum := by decide
  have hdescent : baseEnd_198968 < baseStart_198968 := by decide
  rcases family_descends (prefixWord ++ tailWord_198968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198970 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_198970 : Nat := 118140960795 + 198970 * 2 ^ 59
def prefixEnd_198970 : Nat := 4983230072969 + 3 ^ 40 * 198970 * 2
def baseEnd_198970 : Nat := 22703832405598169479991

theorem tailTrace_198970 : CollatzResearch.WordTrace tailWord_198970 prefixEnd_198970 22703832405598169479991 := by
  unfold tailWord_198970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814258022293286553928591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4838021392782097477142909 1814258022293286553928591)
  ·
    refine ⟨2721387033439929830892887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814258022293286553928591 2721387033439929830892887)
    ·
      refine ⟨4082080550159894746339331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721387033439929830892887 4082080550159894746339331)
      ·
        refine ⟨6123120825239842119508997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082080550159894746339331 6123120825239842119508997)
        ·
          refine ⟨1148085154732470397407937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6123120825239842119508997 1148085154732470397407937)
          ·
            refine ⟨861063866049352798055953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148085154732470397407937 861063866049352798055953)
            ·
              refine ⟨645797899537014598541965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861063866049352798055953 645797899537014598541965)
              ·
                refine ⟨242174212326380474453237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 645797899537014598541965 242174212326380474453237)
                ·
                  refine ⟨22703832405598169479991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242174212326380474453237 22703832405598169479991)
                  ·
                    rfl

theorem cell22_198970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_198970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_198970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_198970 prefixEnd_198970 := by exact prefixLift 198970
  have htrace : WordTrace (prefixWord ++ tailWord_198970) baseStart_198970 baseEnd_198970 := by
    simpa [prefixWord, tailWord_198970, baseEnd_198970] using wordTrace_append hprefix tailTrace_198970
  have hstable : (prefixWord ++ tailWord_198970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198970).length < 2 ^ (prefixWord ++ tailWord_198970).sum := by decide
  have hdescent : baseEnd_198970 < baseStart_198970 := by decide
  rcases family_descends (prefixWord ++ tailWord_198970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199015 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 6]
def baseStart_199015 : Nat := 118140960795 + 199015 * 2 ^ 59
def prefixEnd_199015 : Nat := 4983230072969 + 3 ^ 40 * 199015 * 2
def baseEnd_199015 : Nat := 22708967212143130354945

theorem tailTrace_199015 : CollatzResearch.WordTrace tailWord_199015 prefixEnd_199015 22708967212143130354945 := by
  unfold tailWord_199015
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258673374010118901102499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4839115582673412600734999 7258673374010118901102499)
  ·
    refine ⟨10888010061015178351653749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7258673374010118901102499 10888010061015178351653749)
    ·
      refine ⟨1020750943220172970467539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10888010061015178351653749 1020750943220172970467539)
      ·
        refine ⟨1531126414830259455701309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020750943220172970467539 1531126414830259455701309)
        ·
          refine ⟨574172405561347295887991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1531126414830259455701309 574172405561347295887991)
          ·
            refine ⟨861258608342020943831987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574172405561347295887991 861258608342020943831987)
            ·
              refine ⟨1291887912513031415747981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861258608342020943831987 1291887912513031415747981)
              ·
                refine ⟨484457967192386780905493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291887912513031415747981 484457967192386780905493)
                ·
                  refine ⟨22708967212143130354945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 484457967192386780905493 22708967212143130354945)
                  ·
                    rfl

theorem cell22_199015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 6].length) (baseStart_199015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199015 prefixEnd_199015 := by exact prefixLift 199015
  have htrace : WordTrace (prefixWord ++ tailWord_199015) baseStart_199015 baseEnd_199015 := by
    simpa [prefixWord, tailWord_199015, baseEnd_199015] using wordTrace_append hprefix tailTrace_199015
  have hstable : (prefixWord ++ tailWord_199015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199015).length < 2 ^ (prefixWord ++ tailWord_199015).sum := by decide
  have hdescent : baseEnd_199015 < baseStart_199015 := by decide
  rcases family_descends (prefixWord ++ tailWord_199015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199045 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_199045 : Nat := 118140960795 + 199045 * 2 ^ 59
def prefixEnd_199045 : Nat := 4983230072969 + 3 ^ 40 * 199045 * 2
def baseEnd_199045 : Nat := 68137171249519312814743

theorem tailTrace_199045 : CollatzResearch.WordTrace tailWord_199045 prefixEnd_199045 68137171249519312814743 := by
  unfold tailWord_199045
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259767563901434024694589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4839845042600956016463059 7259767563901434024694589)
  ·
    refine ⟨2722412836463037759260471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7259767563901434024694589 2722412836463037759260471)
    ·
      refine ⟨4083619254694556638890707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722412836463037759260471 4083619254694556638890707)
      ·
        refine ⟨6125428882041834958336061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083619254694556638890707 6125428882041834958336061)
        ·
          refine ⟨2297035830765688109376023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6125428882041834958336061 2297035830765688109376023)
          ·
            refine ⟨3445553746148532164064035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297035830765688109376023 3445553746148532164064035)
            ·
              refine ⟨5168330619222798246096053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445553746148532164064035 5168330619222798246096053)
              ·
                refine ⟨484530995552137335571505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5168330619222798246096053 484530995552137335571505)
                ·
                  refine ⟨363398246664103001678629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484530995552137335571505 363398246664103001678629)
                  ·
                    refine ⟨68137171249519312814743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 363398246664103001678629 68137171249519312814743)
                    ·
                      rfl

theorem cell22_199045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_199045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199045 prefixEnd_199045 := by exact prefixLift 199045
  have htrace : WordTrace (prefixWord ++ tailWord_199045) baseStart_199045 baseEnd_199045 := by
    simpa [prefixWord, tailWord_199045, baseEnd_199045] using wordTrace_append hprefix tailTrace_199045
  have hstable : (prefixWord ++ tailWord_199045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199045).length < 2 ^ (prefixWord ++ tailWord_199045).sum := by decide
  have hdescent : baseEnd_199045 < baseStart_199045 := by decide
  rcases family_descends (prefixWord ++ tailWord_199045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199049 : List Nat := [1, 2, 1, 1, 6, 3, 1, 3, 4]
def baseStart_199049 : Nat := 118140960795 + 199049 * 2 ^ 59
def prefixEnd_199049 : Nat := 4983230072969 + 3 ^ 40 * 199049 * 2
def baseEnd_199049 : Nat := 22712846843754878571577

theorem tailTrace_199049 : CollatzResearch.WordTrace tailWord_199049 prefixEnd_199049 22712846843754878571577 := by
  unfold tailWord_199049
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259913455886942707840201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4839942303924628471893467 7259913455886942707840201)
  ·
    refine ⟨5444935091915207030880151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7259913455886942707840201 5444935091915207030880151)
    ·
      refine ⟨8167402637872810546320227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444935091915207030880151 8167402637872810546320227)
      ·
        refine ⟨12251103956809215819480341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167402637872810546320227 12251103956809215819480341)
        ·
          refine ⟨574270497975431991538141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12251103956809215819480341 574270497975431991538141)
          ·
            refine ⟨215351436740786996826803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574270497975431991538141 215351436740786996826803)
            ·
              refine ⟨323027155111180495240205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215351436740786996826803 323027155111180495240205)
              ·
                refine ⟨121135183166692685715077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323027155111180495240205 121135183166692685715077)
                ·
                  refine ⟨22712846843754878571577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121135183166692685715077 22712846843754878571577)
                  ·
                    rfl

theorem cell22_199049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_199049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199049 prefixEnd_199049 := by exact prefixLift 199049
  have htrace : WordTrace (prefixWord ++ tailWord_199049) baseStart_199049 baseEnd_199049 := by
    simpa [prefixWord, tailWord_199049, baseEnd_199049] using wordTrace_append hprefix tailTrace_199049
  have hstable : (prefixWord ++ tailWord_199049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199049).length < 2 ^ (prefixWord ++ tailWord_199049).sum := by decide
  have hdescent : baseEnd_199049 < baseStart_199049 := by decide
  rcases family_descends (prefixWord ++ tailWord_199049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199152 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_199152 : Nat := 118140960795 + 199152 * 2 ^ 59
def prefixEnd_199152 : Nat := 4983230072969 + 3 ^ 40 * 199152 * 2
def baseEnd_199152 : Nat := 68173799536206700389415

theorem tailTrace_199152 : CollatzResearch.WordTrace tailWord_199152 prefixEnd_199152 68173799536206700389415 := by
  unfold tailWord_199152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3631835087256895649419855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4842446783009194199226473 3631835087256895649419855)
  ·
    refine ⟨5447752630885343474129783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3631835087256895649419855 5447752630885343474129783)
    ·
      refine ⟨8171628946328015211194675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5447752630885343474129783 8171628946328015211194675)
      ·
        refine ⟨12257443419492022816792013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8171628946328015211194675 12257443419492022816792013)
        ·
          refine ⟨4596541282309508556297005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12257443419492022816792013 4596541282309508556297005)
          ·
            refine ⟨1723702980866065708611377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4596541282309508556297005 1723702980866065708611377)
            ·
              refine ⟨1292777235649549281458533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723702980866065708611377 1292777235649549281458533)
              ·
                refine ⟨242395731684290490273475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1292777235649549281458533 242395731684290490273475)
                ·
                  refine ⟨363593597526435735410213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242395731684290490273475 363593597526435735410213)
                  ·
                    refine ⟨68173799536206700389415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 363593597526435735410213 68173799536206700389415)
                    ·
                      rfl

theorem cell22_199152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_199152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199152 prefixEnd_199152 := by exact prefixLift 199152
  have htrace : WordTrace (prefixWord ++ tailWord_199152) baseStart_199152 baseEnd_199152 := by
    simpa [prefixWord, tailWord_199152, baseEnd_199152] using wordTrace_append hprefix tailTrace_199152
  have hstable : (prefixWord ++ tailWord_199152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199152).length < 2 ^ (prefixWord ++ tailWord_199152).sum := by decide
  have hdescent : baseEnd_199152 < baseStart_199152 := by decide
  rcases family_descends (prefixWord ++ tailWord_199152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199169 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_199169 : Nat := 118140960795 + 199169 * 2 ^ 59
def prefixEnd_199169 : Nat := 4983230072969 + 3 ^ 40 * 199169 * 2
def baseEnd_199169 : Nat := 68179618983624322714363

theorem tailTrace_199169 : CollatzResearch.WordTrace tailWord_199169 prefixEnd_199169 68179618983624322714363 := by
  unfold tailWord_199169
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264290215452203202208561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4842860143634802134805707 7264290215452203202208561)
  ·
    refine ⟨5448217661589152401656421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7264290215452203202208561 5448217661589152401656421)
    ·
      refine ⟨1021540811547966075310579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5448217661589152401656421 1021540811547966075310579)
      ·
        refine ⟨1532311217321949112965869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021540811547966075310579 1532311217321949112965869)
        ·
          refine ⟨574616706495730917362201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1532311217321949112965869 574616706495730917362201)
          ·
            refine ⟨430962529871798188021651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574616706495730917362201 430962529871798188021651)
            ·
              refine ⟨646443794807697282032477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430962529871798188021651 646443794807697282032477)
              ·
                refine ⟨242416423052886480762179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646443794807697282032477 242416423052886480762179)
                ·
                  refine ⟨363624634579329721143269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242416423052886480762179 363624634579329721143269)
                  ·
                    refine ⟨68179618983624322714363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 363624634579329721143269 68179618983624322714363)
                    ·
                      rfl

theorem cell22_199169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_199169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199169 prefixEnd_199169 := by exact prefixLift 199169
  have htrace : WordTrace (prefixWord ++ tailWord_199169) baseStart_199169 baseEnd_199169 := by
    simpa [prefixWord, tailWord_199169, baseEnd_199169] using wordTrace_append hprefix tailTrace_199169
  have hstable : (prefixWord ++ tailWord_199169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199169).length < 2 ^ (prefixWord ++ tailWord_199169).sum := by decide
  have hdescent : baseEnd_199169 < baseStart_199169 := by decide
  rcases family_descends (prefixWord ++ tailWord_199169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199197 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_199197 : Nat := 118140960795 + 199197 * 2 ^ 59
def prefixEnd_199197 : Nat := 4983230072969 + 3 ^ 40 * 199197 * 2
def baseEnd_199197 : Nat := 68189203955841583014277

theorem tailTrace_199197 : CollatzResearch.WordTrace tailWord_199197 prefixEnd_199197 68189203955841583014277 := by
  unfold tailWord_199197
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265311459350763984227845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4843540972900509322818563 7265311459350763984227845)
  ·
    refine ⟨1362245898628268247042721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7265311459350763984227845 1362245898628268247042721)
    ·
      refine ⟨1021684423971201185282041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1362245898628268247042721 1021684423971201185282041)
      ·
        refine ⟨766263317978400888961531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1021684423971201185282041 766263317978400888961531)
        ·
          refine ⟨1149394976967601333442297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766263317978400888961531 1149394976967601333442297)
          ·
            refine ⟨862046232725701000081723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149394976967601333442297 862046232725701000081723)
            ·
              refine ⟨1293069349088551500122585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862046232725701000081723 1293069349088551500122585)
              ·
                refine ⟨969802011816413625091939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293069349088551500122585 969802011816413625091939)
                ·
                  refine ⟨1454703017724620437637909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969802011816413625091939 1454703017724620437637909)
                  ·
                    refine ⟨68189203955841583014277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1454703017724620437637909 68189203955841583014277)
                    ·
                      rfl

theorem cell22_199197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_199197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199197 prefixEnd_199197 := by exact prefixLift 199197
  have htrace : WordTrace (prefixWord ++ tailWord_199197) baseStart_199197 baseEnd_199197 := by
    simpa [prefixWord, tailWord_199197, baseEnd_199197] using wordTrace_append hprefix tailTrace_199197
  have hstable : (prefixWord ++ tailWord_199197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199197).length < 2 ^ (prefixWord ++ tailWord_199197).sum := by decide
  have hdescent : baseEnd_199197 < baseStart_199197 := by decide
  rcases family_descends (prefixWord ++ tailWord_199197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199347 : List Nat := [1, 1, 1, 2, 3, 5, 9]
def baseStart_199347 : Nat := 118140960795 + 199347 * 2 ^ 59
def prefixEnd_199347 : Nat := 4983230072969 + 3 ^ 40 * 199347 * 2
def baseEnd_199347 : Nat := 2527427852640414509771

theorem tailTrace_199347 : CollatzResearch.WordTrace tailWord_199347 prefixEnd_199347 2527427852640414509771 := by
  unfold tailWord_199347
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270782408807339602188295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4847188272538226401458863 7270782408807339602188295)
  ·
    refine ⟨10906173613211009403282443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7270782408807339602188295 10906173613211009403282443)
    ·
      refine ⟨16359260419816514104923665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10906173613211009403282443 16359260419816514104923665)
      ·
        refine ⟨12269445314862385578692749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16359260419816514104923665 12269445314862385578692749)
        ·
          refine ⟨4601041993073394592009781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12269445314862385578692749 4601041993073394592009781)
          ·
            refine ⟨431347686850630743000917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4601041993073394592009781 431347686850630743000917)
            ·
              refine ⟨2527427852640414509771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 431347686850630743000917 2527427852640414509771)
              ·
                rfl

theorem cell22_199347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 9].length) (baseStart_199347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199347 prefixEnd_199347 := by exact prefixLift 199347
  have htrace : WordTrace (prefixWord ++ tailWord_199347) baseStart_199347 baseEnd_199347 := by
    simpa [prefixWord, tailWord_199347, baseEnd_199347] using wordTrace_append hprefix tailTrace_199347
  have hstable : (prefixWord ++ tailWord_199347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199347).length < 2 ^ (prefixWord ++ tailWord_199347).sum := by decide
  have hdescent : baseEnd_199347 < baseStart_199347 := by decide
  rcases family_descends (prefixWord ++ tailWord_199347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199351 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 4, 3]
def baseStart_199351 : Nat := 118140960795 + 199351 * 2 ^ 59
def prefixEnd_199351 : Nat := 4983230072969 + 3 ^ 40 * 199351 * 2
def baseEnd_199351 : Nat := 68241921303036514663805

theorem tailTrace_199351 : CollatzResearch.WordTrace tailWord_199351 prefixEnd_199351 68241921303036514663805 := by
  unfold tailWord_199351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270928300792848285333907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4847285533861898856889271 7270928300792848285333907)
  ·
    refine ⟨10906392451189272428000861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7270928300792848285333907 10906392451189272428000861)
    ·
      refine ⟨4089897169195977160500323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10906392451189272428000861 4089897169195977160500323)
      ·
        refine ⟨6134845753793965740750485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4089897169195977160500323 6134845753793965740750485)
        ·
          refine ⟨287570894709092144097679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6134845753793965740750485 287570894709092144097679)
          ·
            refine ⟨431356342063638216146519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287570894709092144097679 431356342063638216146519)
            ·
              refine ⟨647034513095457324219779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431356342063638216146519 647034513095457324219779)
              ·
                refine ⟨970551769643185986329669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647034513095457324219779 970551769643185986329669)
                ·
                  refine ⟨181978456808097372436813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970551769643185986329669 181978456808097372436813)
                  ·
                    refine ⟨68241921303036514663805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181978456808097372436813 68241921303036514663805)
                    ·
                      rfl

theorem cell22_199351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_199351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199351 prefixEnd_199351 := by exact prefixLift 199351
  have htrace : WordTrace (prefixWord ++ tailWord_199351) baseStart_199351 baseEnd_199351 := by
    simpa [prefixWord, tailWord_199351, baseEnd_199351] using wordTrace_append hprefix tailTrace_199351
  have hstable : (prefixWord ++ tailWord_199351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199351).length < 2 ^ (prefixWord ++ tailWord_199351).sum := by decide
  have hdescent : baseEnd_199351 < baseStart_199351 := by decide
  rcases family_descends (prefixWord ++ tailWord_199351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199368 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 2, 3]
def baseStart_199368 : Nat := 118140960795 + 199368 * 2 ^ 59
def prefixEnd_199368 : Nat := 4983230072969 + 3 ^ 40 * 199368 * 2
def baseEnd_199368 : Nat := 68247740750454136988753

theorem tailTrace_199368 : CollatzResearch.WordTrace tailWord_199368 prefixEnd_199368 68247740750454136988753 := by
  unfold tailWord_199368
  simp only [CollatzResearch.WordTrace]
  refine ⟨3635774170865630094351379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4847698894487506792468505 3635774170865630094351379)
  ·
    refine ⟨5453661256298445141527069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3635774170865630094351379 5453661256298445141527069)
    ·
      refine ⟨2045122971111916928072651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5453661256298445141527069 2045122971111916928072651)
      ·
        refine ⟨3067684456667875392108977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045122971111916928072651 3067684456667875392108977)
        ·
          refine ⟨2300763342500906544081733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3067684456667875392108977 2300763342500906544081733)
          ·
            refine ⟨431393126718919977015325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2300763342500906544081733 431393126718919977015325)
            ·
              refine ⟨161772422519594991380747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431393126718919977015325 161772422519594991380747)
              ·
                refine ⟨242658633779392487071121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161772422519594991380747 242658633779392487071121)
                ·
                  refine ⟨181993975334544365303341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242658633779392487071121 181993975334544365303341)
                  ·
                    refine ⟨68247740750454136988753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181993975334544365303341 68247740750454136988753)
                    ·
                      rfl

theorem cell22_199368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_199368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199368 prefixEnd_199368 := by exact prefixLift 199368
  have htrace : WordTrace (prefixWord ++ tailWord_199368) baseStart_199368 baseEnd_199368 := by
    simpa [prefixWord, tailWord_199368, baseEnd_199368] using wordTrace_append hprefix tailTrace_199368
  have hstable : (prefixWord ++ tailWord_199368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199368).length < 2 ^ (prefixWord ++ tailWord_199368).sum := by decide
  have hdescent : baseEnd_199368 < baseStart_199368 := by decide
  rcases family_descends (prefixWord ++ tailWord_199368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199381 : List Nat := [1, 3, 2, 5, 1, 1, 1, 8]
def baseStart_199381 : Nat := 118140960795 + 199381 * 2 ^ 59
def prefixEnd_199381 : Nat := 4983230072969 + 3 ^ 40 * 199381 * 2
def baseEnd_199381 : Nat := 7583576768458492934857

theorem tailTrace_199381 : CollatzResearch.WordTrace tailWord_199381 prefixEnd_199381 7583576768458492934857 := by
  unfold tailWord_199381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272022490684163408925997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4848014993789442272617331 7272022490684163408925997)
  ·
    refine ⟨2727008434006561278347249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7272022490684163408925997 2727008434006561278347249)
    ·
      refine ⟨2045256325504920958760437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2727008434006561278347249 2045256325504920958760437)
      ·
        refine ⟨191742780516086339883791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2045256325504920958760437 191742780516086339883791)
        ·
          refine ⟨287614170774129509825687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191742780516086339883791 287614170774129509825687)
          ·
            refine ⟨431421256161194264738531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287614170774129509825687 431421256161194264738531)
            ·
              refine ⟨647131884241791397107797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431421256161194264738531 647131884241791397107797)
              ·
                refine ⟨7583576768458492934857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 647131884241791397107797 7583576768458492934857)
                ·
                  rfl

theorem cell22_199381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 8].length) (baseStart_199381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199381 prefixEnd_199381 := by exact prefixLift 199381
  have htrace : WordTrace (prefixWord ++ tailWord_199381) baseStart_199381 baseEnd_199381 := by
    simpa [prefixWord, tailWord_199381, baseEnd_199381] using wordTrace_append hprefix tailTrace_199381
  have hstable : (prefixWord ++ tailWord_199381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199381).length < 2 ^ (prefixWord ++ tailWord_199381).sum := by decide
  have hdescent : baseEnd_199381 < baseStart_199381 := by decide
  rcases family_descends (prefixWord ++ tailWord_199381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199409 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 5]
def baseStart_199409 : Nat := 118140960795 + 199409 * 2 ^ 59
def prefixEnd_199409 : Nat := 4983230072969 + 3 ^ 40 * 199409 * 2
def baseEnd_199409 : Nat := 22753925296114565571209

theorem tailTrace_199409 : CollatzResearch.WordTrace tailWord_199409 prefixEnd_199409 22753925296114565571209 := by
  unfold tailWord_199409
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273043734582724190945281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4848695823055149460630187 7273043734582724190945281)
  ·
    refine ⟨5454782800937043143208961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7273043734582724190945281 5454782800937043143208961)
    ·
      refine ⟨4091087100702782357406721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5454782800937043143208961 4091087100702782357406721)
      ·
        refine ⟨3068315325527086768055041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4091087100702782357406721 3068315325527086768055041)
        ·
          refine ⟨2301236494145315076041281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3068315325527086768055041 2301236494145315076041281)
          ·
            refine ⟨1725927370608986307030961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301236494145315076041281 1725927370608986307030961)
            ·
              refine ⟨1294445527956739730273221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725927370608986307030961 1294445527956739730273221)
              ·
                refine ⟨242708536491888699426229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1294445527956739730273221 242708536491888699426229)
                ·
                  refine ⟨22753925296114565571209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242708536491888699426229 22753925296114565571209)
                  ·
                    rfl

theorem cell22_199409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_199409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199409 prefixEnd_199409 := by exact prefixLift 199409
  have htrace : WordTrace (prefixWord ++ tailWord_199409) baseStart_199409 baseEnd_199409 := by
    simpa [prefixWord, tailWord_199409, baseEnd_199409] using wordTrace_append hprefix tailTrace_199409
  have hstable : (prefixWord ++ tailWord_199409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199409).length < 2 ^ (prefixWord ++ tailWord_199409).sum := by decide
  have hdescent : baseEnd_199409 < baseStart_199409 := by decide
  rcases family_descends (prefixWord ++ tailWord_199409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199439 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 3, 4]
def baseStart_199439 : Nat := 118140960795 + 199439 * 2 ^ 59
def prefixEnd_199439 : Nat := 4983230072969 + 3 ^ 40 * 199439 * 2
def baseEnd_199439 : Nat := 68272045501433618463535

theorem tailTrace_199439 : CollatzResearch.WordTrace tailWord_199439 prefixEnd_199439 68272045501433618463535 := by
  unfold tailWord_199439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274137924474039314537371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4849425282982692876358247 7274137924474039314537371)
  ·
    refine ⟨10911206886711058971806057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7274137924474039314537371 10911206886711058971806057)
    ·
      refine ⟨8183405165033294228854543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10911206886711058971806057 8183405165033294228854543)
      ·
        refine ⟨12275107747549941343281815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8183405165033294228854543 12275107747549941343281815)
        ·
          refine ⟨18412661621324912014922723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12275107747549941343281815 18412661621324912014922723)
          ·
            refine ⟨27618992431987368022384085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18412661621324912014922723 27618992431987368022384085)
            ·
              refine ⟨647320135124703938024627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27618992431987368022384085 647320135124703938024627)
              ·
                refine ⟨970980202687055907036941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647320135124703938024627 970980202687055907036941)
                ·
                  refine ⟨364117576007645965138853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970980202687055907036941 364117576007645965138853)
                  ·
                    refine ⟨68272045501433618463535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364117576007645965138853 68272045501433618463535)
                    ·
                      rfl

theorem cell22_199439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_199439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199439 prefixEnd_199439 := by exact prefixLift 199439
  have htrace : WordTrace (prefixWord ++ tailWord_199439) baseStart_199439 baseEnd_199439 := by
    simpa [prefixWord, tailWord_199439, baseEnd_199439] using wordTrace_append hprefix tailTrace_199439
  have hstable : (prefixWord ++ tailWord_199439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199439).length < 2 ^ (prefixWord ++ tailWord_199439).sum := by decide
  have hdescent : baseEnd_199439 < baseStart_199439 := by decide
  rcases family_descends (prefixWord ++ tailWord_199439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199484 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_199484 : Nat := 118140960795 + 199484 * 2 ^ 59
def prefixEnd_199484 : Nat := 4983230072969 + 3 ^ 40 * 199484 * 2
def baseEnd_199484 : Nat := 68287449921068501088397

theorem tailTrace_199484 : CollatzResearch.WordTrace tailWord_199484 prefixEnd_199484 68287449921068501088397 := by
  unfold tailWord_199484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637889604655505999962753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4850519472874007999950337 3637889604655505999962753)
  ·
    refine ⟨2728417203491629499972065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3637889604655505999962753 2728417203491629499972065)
    ·
      refine ⟨2046312902618722124979049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2728417203491629499972065 2046312902618722124979049)
      ·
        refine ⟨1534734676964041593734287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2046312902618722124979049 1534734676964041593734287)
        ·
          refine ⟨2302102015446062390601431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534734676964041593734287 2302102015446062390601431)
          ·
            refine ⟨3453153023169093585902147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302102015446062390601431 3453153023169093585902147)
            ·
              refine ⟨5179729534753640378853221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3453153023169093585902147 5179729534753640378853221)
              ·
                refine ⟨971199287766307571034979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5179729534753640378853221 971199287766307571034979)
                ·
                  refine ⟨1456798931649461356552469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971199287766307571034979 1456798931649461356552469)
                  ·
                    refine ⟨68287449921068501088397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1456798931649461356552469 68287449921068501088397)
                    ·
                      rfl

theorem cell22_199484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_199484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199484 prefixEnd_199484 := by exact prefixLift 199484
  have htrace : WordTrace (prefixWord ++ tailWord_199484) baseStart_199484 baseEnd_199484 := by
    simpa [prefixWord, tailWord_199484, baseEnd_199484] using wordTrace_append hprefix tailTrace_199484
  have hstable : (prefixWord ++ tailWord_199484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199484).length < 2 ^ (prefixWord ++ tailWord_199484).sum := by decide
  have hdescent : baseEnd_199484 < baseStart_199484 := by decide
  rcases family_descends (prefixWord ++ tailWord_199484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199516 : List Nat := [2, 2, 4, 2, 1, 2, 9]
def baseStart_199516 : Nat := 118140960795 + 199516 * 2 ^ 59
def prefixEnd_199516 : Nat := 4983230072969 + 3 ^ 40 * 199516 * 2
def baseEnd_199516 : Nat := 2529570525001151269937

theorem tailTrace_199516 : CollatzResearch.WordTrace tailWord_199516 prefixEnd_199516 2529570525001151269937 := by
  unfold tailWord_199516
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638473172597540732545201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4851297563463387643393601 3638473172597540732545201)
  ·
    refine ⟨2728854879448155549408901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3638473172597540732545201 2728854879448155549408901)
    ·
      refine ⟨511660289896529165514169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2728854879448155549408901 511660289896529165514169)
      ·
        refine ⟨383745217422396874135627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511660289896529165514169 383745217422396874135627)
        ·
          refine ⟨575617826133595311203441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383745217422396874135627 575617826133595311203441)
          ·
            refine ⟨431713369600196483402581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575617826133595311203441 431713369600196483402581)
            ·
              refine ⟨2529570525001151269937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 431713369600196483402581 2529570525001151269937)
              ·
                rfl

theorem cell22_199516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 9].length) (baseStart_199516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199516 prefixEnd_199516 := by exact prefixLift 199516
  have htrace : WordTrace (prefixWord ++ tailWord_199516) baseStart_199516 baseEnd_199516 := by
    simpa [prefixWord, tailWord_199516, baseEnd_199516] using wordTrace_append hprefix tailTrace_199516
  have hstable : (prefixWord ++ tailWord_199516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199516).length < 2 ^ (prefixWord ++ tailWord_199516).sum := by decide
  have hdescent : baseEnd_199516 < baseStart_199516 := by decide
  rcases family_descends (prefixWord ++ tailWord_199516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199531 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 3, 3]
def baseStart_199531 : Nat := 118140960795 + 199531 * 2 ^ 59
def prefixEnd_199531 : Nat := 4983230072969 + 3 ^ 40 * 199531 * 2
def baseEnd_199531 : Nat := 68303538981576045163253

theorem tailTrace_199531 : CollatzResearch.WordTrace tailWord_199531 prefixEnd_199531 68303538981576045163253 := by
  unfold tailWord_199531
  simp only [CollatzResearch.WordTrace]
  refine ⟨7277493440140739026886447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4851662293427159351257631 7277493440140739026886447)
  ·
    refine ⟨10916240160211108540329671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7277493440140739026886447 10916240160211108540329671)
    ·
      refine ⟨16374360240316662810494507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10916240160211108540329671 16374360240316662810494507)
      ·
        refine ⟨24561540360474994215741761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16374360240316662810494507 24561540360474994215741761)
        ·
          refine ⟨18421155270356245661806321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24561540360474994215741761 18421155270356245661806321)
          ·
            refine ⟨13815866452767184246354741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18421155270356245661806321 13815866452767184246354741)
            ·
              refine ⟨1295237479946923523095757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13815866452767184246354741 1295237479946923523095757)
              ·
                refine ⟨485714054980096321160909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1295237479946923523095757 485714054980096321160909)
                ·
                  refine ⟨182142770617536120435341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485714054980096321160909 182142770617536120435341)
                  ·
                    refine ⟨68303538981576045163253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182142770617536120435341 68303538981576045163253)
                    ·
                      rfl

theorem cell22_199531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 3].length) (baseStart_199531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199531 prefixEnd_199531 := by exact prefixLift 199531
  have htrace : WordTrace (prefixWord ++ tailWord_199531) baseStart_199531 baseEnd_199531 := by
    simpa [prefixWord, tailWord_199531, baseEnd_199531] using wordTrace_append hprefix tailTrace_199531
  have hstable : (prefixWord ++ tailWord_199531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199531).length < 2 ^ (prefixWord ++ tailWord_199531).sum := by decide
  have hdescent : baseEnd_199531 < baseStart_199531 := by decide
  rcases family_descends (prefixWord ++ tailWord_199531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199608 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_199608 : Nat := 118140960795 + 199608 * 2 ^ 59
def prefixEnd_199608 : Nat := 4983230072969 + 3 ^ 40 * 199608 * 2
def baseEnd_199608 : Nat := 68329897655173510988017

theorem tailTrace_199608 : CollatzResearch.WordTrace tailWord_199608 prefixEnd_199608 68329897655173510988017 := by
  unfold tailWord_199608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640150930430890588719739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4853534573907854118292985 3640150930430890588719739)
  ·
    refine ⟨5460226395646335883079609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640150930430890588719739 5460226395646335883079609)
    ·
      refine ⟨4095169796734751912309707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5460226395646335883079609 4095169796734751912309707)
      ·
        refine ⟨6142754695102127868464561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4095169796734751912309707 6142754695102127868464561)
        ·
          refine ⟨4607066021326595901348421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6142754695102127868464561 4607066021326595901348421)
          ·
            refine ⟨863824878998736731502829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4607066021326595901348421 863824878998736731502829)
            ·
              refine ⟨323934329624526274313561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 863824878998736731502829 323934329624526274313561)
              ·
                refine ⟨242950747218394705735171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323934329624526274313561 242950747218394705735171)
                ·
                  refine ⟨364426120827592058602757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242950747218394705735171 364426120827592058602757)
                  ·
                    refine ⟨68329897655173510988017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364426120827592058602757 68329897655173510988017)
                    ·
                      rfl

theorem cell22_199608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_199608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199608 prefixEnd_199608 := by exact prefixLift 199608
  have htrace : WordTrace (prefixWord ++ tailWord_199608) baseStart_199608 baseEnd_199608 := by
    simpa [prefixWord, tailWord_199608, baseEnd_199608] using wordTrace_append hprefix tailTrace_199608
  have hstable : (prefixWord ++ tailWord_199608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199608).length < 2 ^ (prefixWord ++ tailWord_199608).sum := by decide
  have hdescent : baseEnd_199608 < baseStart_199608 := by decide
  rcases family_descends (prefixWord ++ tailWord_199608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199629 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 5]
def baseStart_199629 : Nat := 118140960795 + 199629 * 2 ^ 59
def prefixEnd_199629 : Nat := 4983230072969 + 3 ^ 40 * 199629 * 2
def baseEnd_199629 : Nat := 22779028794778818737651

theorem tailTrace_199629 : CollatzResearch.WordTrace tailWord_199629 prefixEnd_199629 22779028794778818737651 := by
  unfold tailWord_199629
  simp only [CollatzResearch.WordTrace]
  refine ⟨7281067793785701763953941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4854045195857134509302627 7281067793785701763953941)
  ·
    refine ⟨341300052833704770185341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7281067793785701763953941 341300052833704770185341)
    ·
      refine ⟨127987519812639288819503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341300052833704770185341 127987519812639288819503)
      ·
        refine ⟨191981279718958933229255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127987519812639288819503 191981279718958933229255)
        ·
          refine ⟨287971919578438399843883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191981279718958933229255 287971919578438399843883)
          ·
            refine ⟨431957879367657599765825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287971919578438399843883 431957879367657599765825)
            ·
              refine ⟨323968409525743199824369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431957879367657599765825 323968409525743199824369)
              ·
                refine ⟨242976307144307399868277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323968409525743199824369 242976307144307399868277)
                ·
                  refine ⟨22779028794778818737651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242976307144307399868277 22779028794778818737651)
                  ·
                    rfl

theorem cell22_199629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_199629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199629 prefixEnd_199629 := by exact prefixLift 199629
  have htrace : WordTrace (prefixWord ++ tailWord_199629) baseStart_199629 baseEnd_199629 := by
    simpa [prefixWord, tailWord_199629, baseEnd_199629] using wordTrace_append hprefix tailTrace_199629
  have hstable : (prefixWord ++ tailWord_199629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199629).length < 2 ^ (prefixWord ++ tailWord_199629).sum := by decide
  have hdescent : baseEnd_199629 < baseStart_199629 := by decide
  rcases family_descends (prefixWord ++ tailWord_199629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199640 : List Nat := [2, 1, 2, 2, 2, 3, 4, 2, 4]
def baseStart_199640 : Nat := 118140960795 + 199640 * 2 ^ 59
def prefixEnd_199640 : Nat := 4983230072969 + 3 ^ 40 * 199640 * 2
def baseEnd_199640 : Nat := 22780283969712031395973

theorem tailTrace_199640 : CollatzResearch.WordTrace tailWord_199640 prefixEnd_199640 22780283969712031395973 := by
  unfold tailWord_199640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640734498372925321302187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4854312664497233761736249 3640734498372925321302187)
  ·
    refine ⟨5461101747559387981953281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640734498372925321302187 5461101747559387981953281)
    ·
      refine ⟨4095826310669540986464961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5461101747559387981953281 4095826310669540986464961)
      ·
        refine ⟨3071869733002155739848721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4095826310669540986464961 3071869733002155739848721)
        ·
          refine ⟨2303902299751616804886541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3071869733002155739848721 2303902299751616804886541)
          ·
            refine ⟨863963362406856301832453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2303902299751616804886541 863963362406856301832453)
            ·
              refine ⟨161993130451285556593585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 863963362406856301832453 161993130451285556593585)
              ·
                refine ⟨121494847838464167445189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161993130451285556593585 121494847838464167445189)
                ·
                  refine ⟨22780283969712031395973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121494847838464167445189 22780283969712031395973)
                  ·
                    rfl

theorem cell22_199640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_199640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199640 prefixEnd_199640 := by exact prefixLift 199640
  have htrace : WordTrace (prefixWord ++ tailWord_199640) baseStart_199640 baseEnd_199640 := by
    simpa [prefixWord, tailWord_199640, baseEnd_199640] using wordTrace_append hprefix tailTrace_199640
  have hstable : (prefixWord ++ tailWord_199640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199640).length < 2 ^ (prefixWord ++ tailWord_199640).sum := by decide
  have hdescent : baseEnd_199640 < baseStart_199640 := by decide
  rcases family_descends (prefixWord ++ tailWord_199640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199655 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 2, 3]
def baseStart_199655 : Nat := 118140960795 + 199655 * 2 ^ 59
def prefixEnd_199655 : Nat := 4983230072969 + 3 ^ 40 * 199655 * 2
def baseEnd_199655 : Nat := 68345986715681055062873

theorem tailTrace_199655 : CollatzResearch.WordTrace tailWord_199655 prefixEnd_199655 68345986715681055062873 := by
  unfold tailWord_199655
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282016091691508204400419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4854677394461005469600279 7282016091691508204400419)
  ·
    refine ⟨10923024137537262306600629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7282016091691508204400419 10923024137537262306600629)
    ·
      refine ⟨1024033512894118341243809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10923024137537262306600629 1024033512894118341243809)
      ·
        refine ⟨768025134670588755932857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024033512894118341243809 768025134670588755932857)
        ·
          refine ⟨576018851002941566949643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768025134670588755932857 576018851002941566949643)
          ·
            refine ⟨864028276504412350424465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576018851002941566949643 864028276504412350424465)
            ·
              refine ⟨648021207378309262818349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864028276504412350424465 648021207378309262818349)
              ·
                refine ⟨243007952766865973556881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648021207378309262818349 243007952766865973556881)
                ·
                  refine ⟨182255964575149480167661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243007952766865973556881 182255964575149480167661)
                  ·
                    refine ⟨68345986715681055062873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182255964575149480167661 68345986715681055062873)
                    ·
                      rfl

theorem cell22_199655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_199655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199655 prefixEnd_199655 := by exact prefixLift 199655
  have htrace : WordTrace (prefixWord ++ tailWord_199655) baseStart_199655 baseEnd_199655 := by
    simpa [prefixWord, tailWord_199655, baseEnd_199655] using wordTrace_append hprefix tailTrace_199655
  have hstable : (prefixWord ++ tailWord_199655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199655).length < 2 ^ (prefixWord ++ tailWord_199655).sum := by decide
  have hdescent : baseEnd_199655 < baseStart_199655 := by decide
  rcases family_descends (prefixWord ++ tailWord_199655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199670 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_199670 : Nat := 118140960795 + 199670 * 2 ^ 59
def prefixEnd_199670 : Nat := 4983230072969 + 3 ^ 40 * 199670 * 2
def baseEnd_199670 : Nat := 68351121522226015937827

theorem tailTrace_199670 : CollatzResearch.WordTrace tailWord_199670 prefixEnd_199670 68351121522226015937827 := by
  unfold tailWord_199670
  simp only [CollatzResearch.WordTrace]
  refine ⟨455160199164822860387279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4855042124424777177464309 455160199164822860387279)
  ·
    refine ⟨682740298747234290580919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455160199164822860387279 682740298747234290580919)
    ·
      refine ⟨1024110448120851435871379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682740298747234290580919 1024110448120851435871379)
      ·
        refine ⟨1536165672181277153807069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024110448120851435871379 1536165672181277153807069)
        ·
          refine ⟨576062127067978932677651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1536165672181277153807069 576062127067978932677651)
          ·
            refine ⟨864093190601968399016477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576062127067978932677651 864093190601968399016477)
            ·
              refine ⟨324034946475738149631179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 864093190601968399016477 324034946475738149631179)
              ·
                refine ⟨486052419713607224446769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324034946475738149631179 486052419713607224446769)
                ·
                  refine ⟨364539314785205418335077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486052419713607224446769 364539314785205418335077)
                  ·
                    refine ⟨68351121522226015937827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364539314785205418335077 68351121522226015937827)
                    ·
                      rfl

theorem cell22_199670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_199670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199670 prefixEnd_199670 := by exact prefixLift 199670
  have htrace : WordTrace (prefixWord ++ tailWord_199670) baseStart_199670 baseEnd_199670 := by
    simpa [prefixWord, tailWord_199670, baseEnd_199670] using wordTrace_append hprefix tailTrace_199670
  have hstable : (prefixWord ++ tailWord_199670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199670).length < 2 ^ (prefixWord ++ tailWord_199670).sum := by decide
  have hdescent : baseEnd_199670 < baseStart_199670 := by decide
  rcases family_descends (prefixWord ++ tailWord_199670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199734 : List Nat := [5, 1, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_199734 : Nat := 118140960795 + 199734 * 2 ^ 59
def prefixEnd_199734 : Nat := 4983230072969 + 3 ^ 40 * 199734 * 2
def baseEnd_199734 : Nat := 68373030030151182337631

theorem tailTrace_199734 : CollatzResearch.WordTrace tailWord_199734 prefixEnd_199734 68373030030151182337631 := by
  unfold tailWord_199734
  simp only [CollatzResearch.WordTrace]
  refine ⟨455306091150331543532891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4856598305603536464350837 455306091150331543532891)
  ·
    refine ⟨682959136725497315299337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455306091150331543532891 682959136725497315299337)
    ·
      refine ⟨512219352544122986474503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 682959136725497315299337 512219352544122986474503)
      ·
        refine ⟨768329028816184479711755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512219352544122986474503 768329028816184479711755)
        ·
          refine ⟨1152493543224276719567633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768329028816184479711755 1152493543224276719567633)
          ·
            refine ⟨864370157418207539675725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152493543224276719567633 864370157418207539675725)
            ·
              refine ⟨324138809031827827378397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 864370157418207539675725 324138809031827827378397)
              ·
                refine ⟨121552053386935435266899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324138809031827827378397 121552053386935435266899)
                ·
                  refine ⟨182328080080403152900349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121552053386935435266899 182328080080403152900349)
                  ·
                    refine ⟨68373030030151182337631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182328080080403152900349 68373030030151182337631)
                    ·
                      rfl

theorem cell22_199734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_199734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199734 prefixEnd_199734 := by exact prefixLift 199734
  have htrace : WordTrace (prefixWord ++ tailWord_199734) baseStart_199734 baseEnd_199734 := by
    simpa [prefixWord, tailWord_199734, baseEnd_199734] using wordTrace_append hprefix tailTrace_199734
  have hstable : (prefixWord ++ tailWord_199734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199734).length < 2 ^ (prefixWord ++ tailWord_199734).sum := by decide
  have hdescent : baseEnd_199734 < baseStart_199734 := by decide
  rcases family_descends (prefixWord ++ tailWord_199734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199790 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_199790 : Nat := 118140960795 + 199790 * 2 ^ 59
def prefixEnd_199790 : Nat := 4983230072969 + 3 ^ 40 * 199790 * 2
def baseEnd_199790 : Nat := 68392199974585702937459

theorem tailTrace_199790 : CollatzResearch.WordTrace tailWord_199790 prefixEnd_199790 68392199974585702937459 := by
  unfold tailWord_199790
  simp only [CollatzResearch.WordTrace]
  refine ⟨910867493275303282570603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4857959964134950840376549 910867493275303282570603)
  ·
    refine ⟨1366301239912954923855905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910867493275303282570603 1366301239912954923855905)
    ·
      refine ⟨1024725929934716192891929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1366301239912954923855905 1024725929934716192891929)
      ·
        refine ⟨768544447451037144668947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024725929934716192891929 768544447451037144668947)
        ·
          refine ⟨1152816671176555717003421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768544447451037144668947 1152816671176555717003421)
          ·
            refine ⟨432306251691208393876283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1152816671176555717003421 432306251691208393876283)
            ·
              refine ⟨648459377536812590814425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432306251691208393876283 648459377536812590814425)
              ·
                refine ⟨486344533152609443110819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648459377536812590814425 486344533152609443110819)
                ·
                  refine ⟨729516799728914164666229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486344533152609443110819 729516799728914164666229)
                  ·
                    refine ⟨68392199974585702937459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 729516799728914164666229 68392199974585702937459)
                    ·
                      rfl

theorem cell22_199790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_199790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199790 prefixEnd_199790 := by exact prefixLift 199790
  have htrace : WordTrace (prefixWord ++ tailWord_199790) baseStart_199790 baseEnd_199790 := by
    simpa [prefixWord, tailWord_199790, baseEnd_199790] using wordTrace_append hprefix tailTrace_199790
  have hstable : (prefixWord ++ tailWord_199790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199790).length < 2 ^ (prefixWord ++ tailWord_199790).sum := by decide
  have hdescent : baseEnd_199790 < baseStart_199790 := by decide
  rcases family_descends (prefixWord ++ tailWord_199790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199809 : List Nat := [1, 2, 4, 2, 2, 3, 2, 2, 4]
def baseStart_199809 : Nat := 118140960795 + 199809 * 2 ^ 59
def prefixEnd_199809 : Nat := 4983230072969 + 3 ^ 40 * 199809 * 2
def baseEnd_199809 : Nat := 22799568020958662237467

theorem tailTrace_199809 : CollatzResearch.WordTrace tailWord_199809 prefixEnd_199809 22799568020958662237467 := by
  unfold tailWord_199809
  simp only [CollatzResearch.WordTrace]
  refine ⟨7287632933133592505506481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4858421955422395003670987 7287632933133592505506481)
  ·
    refine ⟨5465724699850194379129861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7287632933133592505506481 5465724699850194379129861)
    ·
      refine ⟨1024823381221911446086849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5465724699850194379129861 1024823381221911446086849)
      ·
        refine ⟨768617535916433584565137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024823381221911446086849 768617535916433584565137)
        ·
          refine ⟨576463151937325188423853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768617535916433584565137 576463151937325188423853)
          ·
            refine ⟨216173681976496945658945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576463151937325188423853 216173681976496945658945)
            ·
              refine ⟨162130261482372709244209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216173681976496945658945 162130261482372709244209)
              ·
                refine ⟨121597696111779531933157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162130261482372709244209 121597696111779531933157)
                ·
                  refine ⟨22799568020958662237467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121597696111779531933157 22799568020958662237467)
                  ·
                    rfl

theorem cell22_199809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_199809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199809 prefixEnd_199809 := by exact prefixLift 199809
  have htrace : WordTrace (prefixWord ++ tailWord_199809) baseStart_199809 baseEnd_199809 := by
    simpa [prefixWord, tailWord_199809, baseEnd_199809] using wordTrace_append hprefix tailTrace_199809
  have hstable : (prefixWord ++ tailWord_199809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199809).length < 2 ^ (prefixWord ++ tailWord_199809).sum := by decide
  have hdescent : baseEnd_199809 < baseStart_199809 := by decide
  rcases family_descends (prefixWord ++ tailWord_199809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199839 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 2, 4]
def baseStart_199839 : Nat := 118140960795 + 199839 * 2 ^ 59
def prefixEnd_199839 : Nat := 4983230072969 + 3 ^ 40 * 199839 * 2
def baseEnd_199839 : Nat := 68408973675965908462309

theorem tailTrace_199839 : CollatzResearch.WordTrace tailWord_199839 prefixEnd_199839 68408973675965908462309 := by
  unfold tailWord_199839
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288727123024907629098571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4859151415349938419399047 7288727123024907629098571)
  ·
    refine ⟨10933090684537361443647857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7288727123024907629098571 10933090684537361443647857)
    ·
      refine ⟨8199818013403021082735893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10933090684537361443647857 8199818013403021082735893)
      ·
        refine ⟨384366469378266613253245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8199818013403021082735893 384366469378266613253245)
        ·
          refine ⟨144137426016849979969967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384366469378266613253245 144137426016849979969967)
          ·
            refine ⟨216206139025274969954951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144137426016849979969967 216206139025274969954951)
            ·
              refine ⟨324309208537912454932427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216206139025274969954951 324309208537912454932427)
              ·
                refine ⟨486463812806868682398641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324309208537912454932427 486463812806868682398641)
                ·
                  refine ⟨364847859605151511798981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486463812806868682398641 364847859605151511798981)
                  ·
                    refine ⟨68408973675965908462309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364847859605151511798981 68408973675965908462309)
                    ·
                      rfl

theorem cell22_199839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_199839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199839 prefixEnd_199839 := by exact prefixLift 199839
  have htrace : WordTrace (prefixWord ++ tailWord_199839) baseStart_199839 baseEnd_199839 := by
    simpa [prefixWord, tailWord_199839, baseEnd_199839] using wordTrace_append hprefix tailTrace_199839
  have hstable : (prefixWord ++ tailWord_199839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199839).length < 2 ^ (prefixWord ++ tailWord_199839).sum := by decide
  have hdescent : baseEnd_199839 < baseStart_199839 := by decide
  rcases family_descends (prefixWord ++ tailWord_199839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199863 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 4, 5]
def baseStart_199863 : Nat := 118140960795 + 199863 * 2 ^ 59
def prefixEnd_199863 : Nat := 4983230072969 + 3 ^ 40 * 199863 * 2
def baseEnd_199863 : Nat := 68417189366437845862235

theorem tailTrace_199863 : CollatzResearch.WordTrace tailWord_199863 prefixEnd_199863 68417189366437845862235 := by
  unfold tailWord_199863
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289602474937959727972243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4859734983291973151981495 7289602474937959727972243)
  ·
    refine ⟨10934403712406939591958365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7289602474937959727972243 10934403712406939591958365)
    ·
      refine ⟨4100401392152602346984387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10934403712406939591958365 4100401392152602346984387)
      ·
        refine ⟨6150602088228903520476581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100401392152602346984387 6150602088228903520476581)
        ·
          refine ⟨1153237891542919410089359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6150602088228903520476581 1153237891542919410089359)
          ·
            refine ⟨1729856837314379115134039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153237891542919410089359 1729856837314379115134039)
            ·
              refine ⟨2594785255971568672701059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729856837314379115134039 2594785255971568672701059)
              ·
                refine ⟨3892177883957353009051589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594785255971568672701059 3892177883957353009051589)
                ·
                  refine ⟨729783353242003689197173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3892177883957353009051589 729783353242003689197173)
                  ·
                    refine ⟨68417189366437845862235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 729783353242003689197173 68417189366437845862235)
                    ·
                      rfl

theorem cell22_199863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_199863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199863 prefixEnd_199863 := by exact prefixLift 199863
  have htrace : WordTrace (prefixWord ++ tailWord_199863) baseStart_199863 baseEnd_199863 := by
    simpa [prefixWord, tailWord_199863, baseEnd_199863] using wordTrace_append hprefix tailTrace_199863
  have hstable : (prefixWord ++ tailWord_199863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199863).length < 2 ^ (prefixWord ++ tailWord_199863).sum := by decide
  have hdescent : baseEnd_199863 < baseStart_199863 := by decide
  rcases family_descends (prefixWord ++ tailWord_199863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199865 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 5]
def baseStart_199865 : Nat := 118140960795 + 199865 * 2 ^ 59
def prefixEnd_199865 : Nat := 4983230072969 + 3 ^ 40 * 199865 * 2
def baseEnd_199865 : Nat := 22805958002436835770743

theorem tailTrace_199865 : CollatzResearch.WordTrace tailWord_199865 prefixEnd_199865 22805958002436835770743 := by
  unfold tailWord_199865
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289675420930714069545049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4859783613953809379696699 7289675420930714069545049)
  ·
    refine ⟨5467256565698035552158787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7289675420930714069545049 5467256565698035552158787)
    ·
      refine ⟨8200884848547053328238181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5467256565698035552158787 8200884848547053328238181)
      ·
        refine ⟨1537665909102572499044659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8200884848547053328238181 1537665909102572499044659)
        ·
          refine ⟨2306498863653858748566989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537665909102572499044659 2306498863653858748566989)
          ·
            refine ⟨864937073870197030712621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2306498863653858748566989 864937073870197030712621)
            ·
              refine ⟨324351402701323886517233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 864937073870197030712621 324351402701323886517233)
              ·
                refine ⟨243263552025992914887925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324351402701323886517233 243263552025992914887925)
                ·
                  refine ⟨22805958002436835770743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243263552025992914887925 22805958002436835770743)
                  ·
                    rfl

theorem cell22_199865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_199865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199865 prefixEnd_199865 := by exact prefixLift 199865
  have htrace : WordTrace (prefixWord ++ tailWord_199865) baseStart_199865 baseEnd_199865 := by
    simpa [prefixWord, tailWord_199865, baseEnd_199865] using wordTrace_append hprefix tailTrace_199865
  have hstable : (prefixWord ++ tailWord_199865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199865).length < 2 ^ (prefixWord ++ tailWord_199865).sum := by decide
  have hdescent : baseEnd_199865 < baseStart_199865 := by decide
  rcases family_descends (prefixWord ++ tailWord_199865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199882 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_199882 : Nat := 118140960795 + 199882 * 2 ^ 59
def prefixEnd_199882 : Nat := 4983230072969 + 3 ^ 40 * 199882 * 2
def baseEnd_199882 : Nat := 22807897818242709879059

theorem tailTrace_199882 : CollatzResearch.WordTrace tailWord_199882 prefixEnd_199882 22807897818242709879059 := by
  unfold tailWord_199882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822573865467281493228475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4860196974579417315275933 1822573865467281493228475)
  ·
    refine ⟨2733860798200922239842713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822573865467281493228475 2733860798200922239842713)
    ·
      refine ⟨2050395598650691679882035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2733860798200922239842713 2050395598650691679882035)
      ·
        refine ⟨3075593397976037519823053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050395598650691679882035 3075593397976037519823053)
        ·
          refine ⟨1153347524241014069933645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3075593397976037519823053 1153347524241014069933645)
          ·
            refine ⟨432505321590380276225117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1153347524241014069933645 432505321590380276225117)
            ·
              refine ⟨162189495596392603584419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432505321590380276225117 162189495596392603584419)
              ·
                refine ⟨243284243394588905376629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162189495596392603584419 243284243394588905376629)
                ·
                  refine ⟨22807897818242709879059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243284243394588905376629 22807897818242709879059)
                  ·
                    rfl

theorem cell22_199882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_199882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199882 prefixEnd_199882 := by exact prefixLift 199882
  have htrace : WordTrace (prefixWord ++ tailWord_199882) baseStart_199882 baseEnd_199882 := by
    simpa [prefixWord, tailWord_199882, baseEnd_199882] using wordTrace_append hprefix tailTrace_199882
  have hstable : (prefixWord ++ tailWord_199882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199882).length < 2 ^ (prefixWord ++ tailWord_199882).sum := by decide
  have hdescent : baseEnd_199882 < baseStart_199882 := by decide
  rcases family_descends (prefixWord ++ tailWord_199882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199895 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 1, 4]
def baseStart_199895 : Nat := 118140960795 + 199895 * 2 ^ 59
def prefixEnd_199895 : Nat := 4983230072969 + 3 ^ 40 * 199895 * 2
def baseEnd_199895 : Nat := 68428143620400429062137

theorem tailTrace_199895 : CollatzResearch.WordTrace tailWord_199895 prefixEnd_199895 68428143620400429062137 := by
  unfold tailWord_199895
  simp only [CollatzResearch.WordTrace]
  refine ⟨7290769610822029193137139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4860513073881352795424759 7290769610822029193137139)
  ·
    refine ⟨10936154416233043789705709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7290769610822029193137139 10936154416233043789705709)
    ·
      refine ⟨4101057906087391421139641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10936154416233043789705709 4101057906087391421139641)
      ·
        refine ⟨3075793429565543565854731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4101057906087391421139641 3075793429565543565854731)
        ·
          refine ⟨4613690144348315348782097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075793429565543565854731 4613690144348315348782097)
          ·
            refine ⟨3460267608261236511586573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4613690144348315348782097 3460267608261236511586573)
            ·
              refine ⟨1297600353097963691844965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3460267608261236511586573 1297600353097963691844965)
              ·
                refine ⟨243300066205868192220931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1297600353097963691844965 243300066205868192220931)
                ·
                  refine ⟨364950099308802288331397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243300066205868192220931 364950099308802288331397)
                  ·
                    refine ⟨68428143620400429062137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364950099308802288331397 68428143620400429062137)
                    ·
                      rfl

theorem cell22_199895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_199895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199895 prefixEnd_199895 := by exact prefixLift 199895
  have htrace : WordTrace (prefixWord ++ tailWord_199895) baseStart_199895 baseEnd_199895 := by
    simpa [prefixWord, tailWord_199895, baseEnd_199895] using wordTrace_append hprefix tailTrace_199895
  have hstable : (prefixWord ++ tailWord_199895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199895).length < 2 ^ (prefixWord ++ tailWord_199895).sum := by decide
  have hdescent : baseEnd_199895 < baseStart_199895 := by decide
  rcases family_descends (prefixWord ++ tailWord_199895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199985 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_199985 : Nat := 118140960795 + 199985 * 2 ^ 59
def prefixEnd_199985 : Nat := 4983230072969 + 3 ^ 40 * 199985 * 2
def baseEnd_199985 : Nat := 68458952459670194311861

theorem tailTrace_199985 : CollatzResearch.WordTrace tailWord_199985 prefixEnd_199985 68458952459670194311861 := by
  unfold tailWord_199985
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294052180495974563913409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4862701453663983042608939 7294052180495974563913409)
  ·
    refine ⟨5470539135371980922935057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7294052180495974563913409 5470539135371980922935057)
    ·
      refine ⟨4102904351528985692201293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5470539135371980922935057 4102904351528985692201293)
      ·
        refine ⟨1538589131823369634575485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4102904351528985692201293 1538589131823369634575485)
        ·
          refine ⟨576970924433763612965807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1538589131823369634575485 576970924433763612965807)
          ·
            refine ⟨865456386650645419448711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576970924433763612965807 865456386650645419448711)
            ·
              refine ⟨1298184579975968129173067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865456386650645419448711 1298184579975968129173067)
              ·
                refine ⟨1947276869963952193759601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298184579975968129173067 1947276869963952193759601)
                ·
                  refine ⟨1460457652472964145319701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947276869963952193759601 1460457652472964145319701)
                  ·
                    refine ⟨68458952459670194311861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1460457652472964145319701 68458952459670194311861)
                    ·
                      rfl

theorem cell22_199985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_199985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_199985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_199985 prefixEnd_199985 := by exact prefixLift 199985
  have htrace : WordTrace (prefixWord ++ tailWord_199985) baseStart_199985 baseEnd_199985 := by
    simpa [prefixWord, tailWord_199985, baseEnd_199985] using wordTrace_append hprefix tailTrace_199985
  have hstable : (prefixWord ++ tailWord_199985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199985).length < 2 ^ (prefixWord ++ tailWord_199985).sum := by decide
  have hdescent : baseEnd_199985 < baseStart_199985 := by decide
  rcases family_descends (prefixWord ++ tailWord_199985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200000 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 5]
def baseStart_200000 : Nat := 118140960795 + 200000 * 2 ^ 59
def prefixEnd_200000 : Nat := 4983230072969 + 3 ^ 40 * 200000 * 2
def baseEnd_200000 : Nat := 22821362422071718395605

theorem tailTrace_200000 : CollatzResearch.WordTrace tailWord_200000 prefixEnd_200000 22821362422071718395605 := by
  unfold tailWord_200000
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647299637720816062854727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4863066183627754750472969 3647299637720816062854727)
  ·
    refine ⟨5470949456581224094282091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3647299637720816062854727 5470949456581224094282091)
    ·
      refine ⟨8206424184871836141423137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5470949456581224094282091 8206424184871836141423137)
      ·
        refine ⟨6154818138653877106067353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8206424184871836141423137 6154818138653877106067353)
        ·
          refine ⟨4616113603990407829550515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6154818138653877106067353 4616113603990407829550515)
          ·
            refine ⟨6924170405985611744325773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4616113603990407829550515 6924170405985611744325773)
            ·
              refine ⟨2596563902244604404122165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6924170405985611744325773 2596563902244604404122165)
              ·
                refine ⟨243427865835431662886453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2596563902244604404122165 243427865835431662886453)
                ·
                  refine ⟨22821362422071718395605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243427865835431662886453 22821362422071718395605)
                  ·
                    rfl

theorem cell22_200000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_200000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200000 prefixEnd_200000 := by exact prefixLift 200000
  have htrace : WordTrace (prefixWord ++ tailWord_200000) baseStart_200000 baseEnd_200000 := by
    simpa [prefixWord, tailWord_200000, baseEnd_200000] using wordTrace_append hprefix tailTrace_200000
  have hstable : (prefixWord ++ tailWord_200000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200000).length < 2 ^ (prefixWord ++ tailWord_200000).sum := by decide
  have hdescent : baseEnd_200000 < baseStart_200000 := by decide
  rcases family_descends (prefixWord ++ tailWord_200000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200004 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_200004 : Nat := 118140960795 + 200004 * 2 ^ 59
def prefixEnd_200004 : Nat := 4983230072969 + 3 ^ 40 * 200004 * 2
def baseEnd_200004 : Nat := 68465456547960478086803

theorem tailTrace_200004 : CollatzResearch.WordTrace tailWord_200004 prefixEnd_200004 68465456547960478086803 := by
  unfold tailWord_200004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647372583713570404427533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4863163444951427205903377 3647372583713570404427533)
  ·
    refine ⟨1367764718892588901660325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3647372583713570404427533 1367764718892588901660325)
    ·
      refine ⟨256455884792360419061311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1367764718892588901660325 256455884792360419061311)
      ·
        refine ⟨384683827188540628591967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256455884792360419061311 384683827188540628591967)
        ·
          refine ⟨577025740782810942887951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384683827188540628591967 577025740782810942887951)
          ·
            refine ⟨865538611174216414331927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577025740782810942887951 865538611174216414331927)
            ·
              refine ⟨1298307916761324621497891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865538611174216414331927 1298307916761324621497891)
              ·
                refine ⟨1947461875141986932246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298307916761324621497891 1947461875141986932246837)
                ·
                  refine ⟨182574550794561274898141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1947461875141986932246837 182574550794561274898141)
                  ·
                    refine ⟨68465456547960478086803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182574550794561274898141 68465456547960478086803)
                    ·
                      rfl

theorem cell22_200004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_200004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200004 prefixEnd_200004 := by exact prefixLift 200004
  have htrace : WordTrace (prefixWord ++ tailWord_200004) baseStart_200004 baseEnd_200004 := by
    simpa [prefixWord, tailWord_200004, baseEnd_200004] using wordTrace_append hprefix tailTrace_200004
  have hstable : (prefixWord ++ tailWord_200004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200004).length < 2 ^ (prefixWord ++ tailWord_200004).sum := by decide
  have hdescent : baseEnd_200004 < baseStart_200004 := by decide
  rcases family_descends (prefixWord ++ tailWord_200004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200021 : List Nat := [1, 3, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_200021 : Nat := 118140960795 + 200021 * 2 ^ 59
def prefixEnd_200021 : Nat := 4983230072969 + 3 ^ 40 * 200021 * 2
def baseEnd_200021 : Nat := 68471275995378100411751

theorem tailTrace_200021 : CollatzResearch.WordTrace tailWord_200021 prefixEnd_200021 68471275995378100411751 := by
  unfold tailWord_200021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7295365208365552712223917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4863576805577035141482611 7295365208365552712223917)
  ·
    refine ⟨2735761953137082267083969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7295365208365552712223917 2735761953137082267083969)
    ·
      refine ⟨2051821464852811700312977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2735761953137082267083969 2051821464852811700312977)
      ·
        refine ⟨1538866098639608775234733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051821464852811700312977 1538866098639608775234733)
        ·
          refine ⟨577074786989853290713025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1538866098639608775234733 577074786989853290713025)
          ·
            refine ⟨432806090242389968034769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577074786989853290713025 432806090242389968034769)
            ·
              refine ⟨324604567681792476026077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432806090242389968034769 324604567681792476026077)
              ·
                refine ⟨121726712880672178509779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324604567681792476026077 121726712880672178509779)
                ·
                  refine ⟨182590069321008267764669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121726712880672178509779 182590069321008267764669)
                  ·
                    refine ⟨68471275995378100411751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182590069321008267764669 68471275995378100411751)
                    ·
                      rfl

theorem cell22_200021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_200021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200021 prefixEnd_200021 := by exact prefixLift 200021
  have htrace : WordTrace (prefixWord ++ tailWord_200021) baseStart_200021 baseEnd_200021 := by
    simpa [prefixWord, tailWord_200021, baseEnd_200021] using wordTrace_append hprefix tailTrace_200021
  have hstable : (prefixWord ++ tailWord_200021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200021).length < 2 ^ (prefixWord ++ tailWord_200021).sum := by decide
  have hdescent : baseEnd_200021 < baseStart_200021 := by decide
  rcases family_descends (prefixWord ++ tailWord_200021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200075 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 1, 6]
def baseStart_200075 : Nat := 118140960795 + 200075 * 2 ^ 59
def prefixEnd_200075 : Nat := 4983230072969 + 3 ^ 40 * 200075 * 2
def baseEnd_200075 : Nat := 68489761298939959561585

theorem tailTrace_200075 : CollatzResearch.WordTrace tailWord_200075 prefixEnd_200075 68489761298939959561585 := by
  unfold tailWord_200075
  simp only [CollatzResearch.WordTrace]
  refine ⟨7297334750169919934689679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4864889833446613289793119 7297334750169919934689679)
  ·
    refine ⟨10946002125254879902034519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7297334750169919934689679 10946002125254879902034519)
    ·
      refine ⟨16419003187882319853051779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10946002125254879902034519 16419003187882319853051779)
      ·
        refine ⟨24628504781823479779577669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16419003187882319853051779 24628504781823479779577669)
        ·
          refine ⟨4617844646591902458670813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24628504781823479779577669 4617844646591902458670813)
          ·
            refine ⟨1731691742471963422001555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4617844646591902458670813 1731691742471963422001555)
            ·
              refine ⟨2597537613707945133002333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731691742471963422001555 2597537613707945133002333)
              ·
                refine ⟨974076605140479424875875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2597537613707945133002333 974076605140479424875875)
                ·
                  refine ⟨1461114907710719137313813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974076605140479424875875 1461114907710719137313813)
                  ·
                    refine ⟨68489761298939959561585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1461114907710719137313813 68489761298939959561585)
                    ·
                      rfl

theorem cell22_200075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_200075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200075 prefixEnd_200075 := by exact prefixLift 200075
  have htrace : WordTrace (prefixWord ++ tailWord_200075) baseStart_200075 baseEnd_200075 := by
    simpa [prefixWord, tailWord_200075, baseEnd_200075] using wordTrace_append hprefix tailTrace_200075
  have hstable : (prefixWord ++ tailWord_200075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200075).length < 2 ^ (prefixWord ++ tailWord_200075).sum := by decide
  have hdescent : baseEnd_200075 < baseStart_200075 := by decide
  rcases family_descends (prefixWord ++ tailWord_200075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200152 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 5]
def baseStart_200152 : Nat := 118140960795 + 200152 * 2 ^ 59
def prefixEnd_200152 : Nat := 4983230072969 + 3 ^ 40 * 200152 * 2
def baseEnd_200152 : Nat := 22838706657512475128783

theorem tailTrace_200152 : CollatzResearch.WordTrace tailWord_200152 prefixEnd_200152 22838706657512475128783 := by
  unfold tailWord_200152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650071585445481042621355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4866762113927308056828473 3650071585445481042621355)
  ·
    refine ⟨5475107378168221563932033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3650071585445481042621355 5475107378168221563932033)
    ·
      refine ⟨4106330533626166172949025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5475107378168221563932033 4106330533626166172949025)
      ·
        refine ⟨3079747900219624629711769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4106330533626166172949025 3079747900219624629711769)
        ·
          refine ⟨2309810925164718472283827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3079747900219624629711769 2309810925164718472283827)
          ·
            refine ⟨3464716387747077708425741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309810925164718472283827 3464716387747077708425741)
            ·
              refine ⟨1299268645405154140659653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3464716387747077708425741 1299268645405154140659653)
              ·
                refine ⟨243612871013466401373685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1299268645405154140659653 243612871013466401373685)
                ·
                  refine ⟨22838706657512475128783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243612871013466401373685 22838706657512475128783)
                  ·
                    rfl

theorem cell22_200152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_200152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200152 prefixEnd_200152 := by exact prefixLift 200152
  have htrace : WordTrace (prefixWord ++ tailWord_200152) baseStart_200152 baseEnd_200152 := by
    simpa [prefixWord, tailWord_200152, baseEnd_200152] using wordTrace_append hprefix tailTrace_200152
  have hstable : (prefixWord ++ tailWord_200152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200152).length < 2 ^ (prefixWord ++ tailWord_200152).sum := by decide
  have hdescent : baseEnd_200152 < baseStart_200152 := by decide
  rcases family_descends (prefixWord ++ tailWord_200152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200167 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 1, 7]
def baseStart_200167 : Nat := 118140960795 + 200167 * 2 ^ 59
def prefixEnd_200167 : Nat := 4983230072969 + 3 ^ 40 * 200167 * 2
def baseEnd_200167 : Nat := 68521254779082386261303

theorem tailTrace_200167 : CollatzResearch.WordTrace tailWord_200167 prefixEnd_200167 68521254779082386261303 := by
  unfold tailWord_200167
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300690265836619647038755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4867126843891079764692503 7300690265836619647038755)
  ·
    refine ⟨10951035398754929470558133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300690265836619647038755 10951035398754929470558133)
    ·
      refine ⟨1026659568633274637864825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10951035398754929470558133 1026659568633274637864825)
      ·
        refine ⟨769994676474955978398619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1026659568633274637864825 769994676474955978398619)
        ·
          refine ⟨1154992014712433967597929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769994676474955978398619 1154992014712433967597929)
          ·
            refine ⟨866244011034325475698447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154992014712433967597929 866244011034325475698447)
            ·
              refine ⟨1299366016551488213547671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866244011034325475698447 1299366016551488213547671)
              ·
                refine ⟨1949049024827232320321507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299366016551488213547671 1949049024827232320321507)
                ·
                  refine ⟨2923573537240848480482261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949049024827232320321507 2923573537240848480482261)
                  ·
                    refine ⟨68521254779082386261303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2923573537240848480482261 68521254779082386261303)
                    ·
                      rfl

theorem cell22_200167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_200167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200167 prefixEnd_200167 := by exact prefixLift 200167
  have htrace : WordTrace (prefixWord ++ tailWord_200167) baseStart_200167 baseEnd_200167 := by
    simpa [prefixWord, tailWord_200167, baseEnd_200167] using wordTrace_append hprefix tailTrace_200167
  have hstable : (prefixWord ++ tailWord_200167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200167).length < 2 ^ (prefixWord ++ tailWord_200167).sum := by decide
  have hdescent : baseEnd_200167 < baseStart_200167 := by decide
  rcases family_descends (prefixWord ++ tailWord_200167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200272 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_200272 : Nat := 118140960795 + 200272 * 2 ^ 59
def prefixEnd_200272 : Nat := 4983230072969 + 3 ^ 40 * 200272 * 2
def baseEnd_200272 : Nat := 68557198424897112385981

theorem tailTrace_200272 : CollatzResearch.WordTrace tailWord_200272 prefixEnd_200272 68557198424897112385981 := by
  unfold tailWord_200272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652259965228111289805535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4869679953637481719740713 3652259965228111289805535)
  ·
    refine ⟨5478389947842166934708303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3652259965228111289805535 5478389947842166934708303)
    ·
      refine ⟨8217584921763250402062455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5478389947842166934708303 8217584921763250402062455)
      ·
        refine ⟨12326377382644875603093683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8217584921763250402062455 12326377382644875603093683)
        ·
          refine ⟨18489566073967313404640525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12326377382644875603093683 18489566073967313404640525)
          ·
            refine ⟨6933587277737742526740197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18489566073967313404640525 6933587277737742526740197)
            ·
              refine ⟨1300047614575826723763787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6933587277737742526740197 1300047614575826723763787)
              ·
                refine ⟨1950071421863740085645681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300047614575826723763787 1950071421863740085645681)
                ·
                  refine ⟨1462553566397805064234261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1950071421863740085645681 1462553566397805064234261)
                  ·
                    refine ⟨68557198424897112385981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1462553566397805064234261 68557198424897112385981)
                    ·
                      rfl

theorem cell22_200272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_200272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200272 prefixEnd_200272 := by exact prefixLift 200272
  have htrace : WordTrace (prefixWord ++ tailWord_200272) baseStart_200272 baseEnd_200272 := by
    simpa [prefixWord, tailWord_200272, baseEnd_200272] using wordTrace_append hprefix tailTrace_200272
  have hstable : (prefixWord ++ tailWord_200272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200272).length < 2 ^ (prefixWord ++ tailWord_200272).sum := by decide
  have hdescent : baseEnd_200272 < baseStart_200272 := by decide
  rcases family_descends (prefixWord ++ tailWord_200272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200321 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 5]
def baseStart_200321 : Nat := 118140960795 + 200321 * 2 ^ 59
def prefixEnd_200321 : Nat := 4983230072969 + 3 ^ 40 * 200321 * 2
def baseEnd_200321 : Nat := 22857990708759105970277

theorem tailTrace_200321 : CollatzResearch.WordTrace tailWord_200321 prefixEnd_200321 22857990708759105970277 := by
  unfold tailWord_200321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306307107278703948144817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4870871404852469298763211 7306307107278703948144817)
  ·
    refine ⟨5479730330459027961108613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7306307107278703948144817 5479730330459027961108613)
    ·
      refine ⟨1027449436961067742707865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5479730330459027961108613 1027449436961067742707865)
      ·
        refine ⟨770587077720800807030899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027449436961067742707865 770587077720800807030899)
        ·
          refine ⟨1155880616581201210546349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770587077720800807030899 1155880616581201210546349)
          ·
            refine ⟨433455231217950453954881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1155880616581201210546349 433455231217950453954881)
            ·
              refine ⟨325091423413462840466161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433455231217950453954881 325091423413462840466161)
              ·
                refine ⟨243818567560097130349621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325091423413462840466161 243818567560097130349621)
                ·
                  refine ⟨22857990708759105970277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243818567560097130349621 22857990708759105970277)
                  ·
                    rfl

theorem cell22_200321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_200321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200321 prefixEnd_200321 := by exact prefixLift 200321
  have htrace : WordTrace (prefixWord ++ tailWord_200321) baseStart_200321 baseEnd_200321 := by
    simpa [prefixWord, tailWord_200321, baseEnd_200321] using wordTrace_append hprefix tailTrace_200321
  have hstable : (prefixWord ++ tailWord_200321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200321).length < 2 ^ (prefixWord ++ tailWord_200321).sum := by decide
  have hdescent : baseEnd_200321 < baseStart_200321 := by decide
  rcases family_descends (prefixWord ++ tailWord_200321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200347 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 11]
def baseStart_200347 : Nat := 118140960795 + 200347 * 2 ^ 59
def prefixEnd_200347 : Nat := 4983230072969 + 3 ^ 40 * 200347 * 2
def baseEnd_200347 : Nat := 68582872457621916760751

theorem tailTrace_200347 : CollatzResearch.WordTrace tailWord_200347 prefixEnd_200347 68582872457621916760751 := by
  unfold tailWord_200347
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307255405184510388591295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4871503603456340259060863 7307255405184510388591295)
  ·
    refine ⟨10960883107776765582886943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7307255405184510388591295 10960883107776765582886943)
    ·
      refine ⟨16441324661665148374330415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10960883107776765582886943 16441324661665148374330415)
      ·
        refine ⟨24661986992497722561495623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16441324661665148374330415 24661986992497722561495623)
        ·
          refine ⟨36992980488746583842243435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24661986992497722561495623 36992980488746583842243435)
          ·
            refine ⟨55489470733119875763365153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36992980488746583842243435 55489470733119875763365153)
            ·
              refine ⟨41617103049839906822523865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55489470733119875763365153 41617103049839906822523865)
              ·
                refine ⟨31212827287379930116892899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41617103049839906822523865 31212827287379930116892899)
                ·
                  refine ⟨46819240931069895175339349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31212827287379930116892899 46819240931069895175339349)
                  ·
                    refine ⟨68582872457621916760751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 46819240931069895175339349 68582872457621916760751)
                    ·
                      rfl

theorem cell22_200347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_200347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200347 prefixEnd_200347 := by exact prefixLift 200347
  have htrace : WordTrace (prefixWord ++ tailWord_200347) baseStart_200347 baseEnd_200347 := by
    simpa [prefixWord, tailWord_200347, baseEnd_200347] using wordTrace_append hprefix tailTrace_200347
  have hstable : (prefixWord ++ tailWord_200347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200347).length < 2 ^ (prefixWord ++ tailWord_200347).sum := by decide
  have hdescent : baseEnd_200347 < baseStart_200347 := by decide
  rcases family_descends (prefixWord ++ tailWord_200347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200379 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 2, 4]
def baseStart_200379 : Nat := 118140960795 + 200379 * 2 ^ 59
def prefixEnd_200379 : Nat := 4983230072969 + 3 ^ 40 * 200379 * 2
def baseEnd_200379 : Nat := 68593826711584499960653

theorem tailTrace_200379 : CollatzResearch.WordTrace tailWord_200379 prefixEnd_200379 68593826711584499960653 := by
  unfold tailWord_200379
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308422541068579853756191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4872281694045719902504127 7308422541068579853756191)
  ·
    refine ⟨10962633811602869780634287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7308422541068579853756191 10962633811602869780634287)
    ·
      refine ⟨16443950717404304670951431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10962633811602869780634287 16443950717404304670951431)
      ·
        refine ⟨24665926076106457006427147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16443950717404304670951431 24665926076106457006427147)
        ·
          refine ⟨36998889114159685509640721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24665926076106457006427147 36998889114159685509640721)
          ·
            refine ⟨27749166835619764132230541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36998889114159685509640721 27749166835619764132230541)
            ·
              refine ⟨10405937563357411549586453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27749166835619764132230541 10405937563357411549586453)
              ·
                refine ⟨487778323282378666386865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10405937563357411549586453 487778323282378666386865)
                ·
                  refine ⟨365833742461783999790149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487778323282378666386865 365833742461783999790149)
                  ·
                    refine ⟨68593826711584499960653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 365833742461783999790149 68593826711584499960653)
                    ·
                      rfl

theorem cell22_200379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_200379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200379 prefixEnd_200379 := by exact prefixLift 200379
  have htrace : WordTrace (prefixWord ++ tailWord_200379) baseStart_200379 baseEnd_200379 := by
    simpa [prefixWord, tailWord_200379, baseEnd_200379] using wordTrace_append hprefix tailTrace_200379
  have hstable : (prefixWord ++ tailWord_200379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200379).length < 2 ^ (prefixWord ++ tailWord_200379).sum := by decide
  have hdescent : baseEnd_200379 < baseStart_200379 := by decide
  rcases family_descends (prefixWord ++ tailWord_200379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200381 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_200381 : Nat := 118140960795 + 200381 * 2 ^ 59
def prefixEnd_200381 : Nat := 4983230072969 + 3 ^ 40 * 200381 * 2
def baseEnd_200381 : Nat := 68594511352457161410647

theorem tailTrace_200381 : CollatzResearch.WordTrace tailWord_200381 prefixEnd_200381 68594511352457161410647 := by
  unfold tailWord_200381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308495487061334195328997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4872330324707556130219331 7308495487061334195328997)
  ·
    refine ⟨1370342903824000161624187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7308495487061334195328997 1370342903824000161624187)
    ·
      refine ⟨2055514355736000242436281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370342903824000161624187 2055514355736000242436281)
      ·
        refine ⟨1541635766802000181827211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2055514355736000242436281 1541635766802000181827211)
        ·
          refine ⟨2312453650203000272740817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541635766802000181827211 2312453650203000272740817)
          ·
            refine ⟨1734340237652250204555613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312453650203000272740817 1734340237652250204555613)
            ·
              refine ⟨650377589119593826708355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1734340237652250204555613 650377589119593826708355)
              ·
                refine ⟨975566383679390740062533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650377589119593826708355 975566383679390740062533)
                ·
                  refine ⟨182918696939885763761725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 975566383679390740062533 182918696939885763761725)
                  ·
                    refine ⟨68594511352457161410647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182918696939885763761725 68594511352457161410647)
                    ·
                      rfl

theorem cell22_200381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_200381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200381 prefixEnd_200381 := by exact prefixLift 200381
  have htrace : WordTrace (prefixWord ++ tailWord_200381) baseStart_200381 baseEnd_200381 := by
    simpa [prefixWord, tailWord_200381, baseEnd_200381] using wordTrace_append hprefix tailTrace_200381
  have hstable : (prefixWord ++ tailWord_200381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200381).length < 2 ^ (prefixWord ++ tailWord_200381).sum := by decide
  have hdescent : baseEnd_200381 < baseStart_200381 := by decide
  rcases family_descends (prefixWord ++ tailWord_200381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200426 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_200426 : Nat := 118140960795 + 200426 * 2 ^ 59
def prefixEnd_200426 : Nat := 4983230072969 + 3 ^ 40 * 200426 * 2
def baseEnd_200426 : Nat := 68609915772092044035509

theorem tailTrace_200426 : CollatzResearch.WordTrace tailWord_200426 prefixEnd_200426 68609915772092044035509 := by
  unfold tailWord_200426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827534192974576720179283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4873424514598871253811421 1827534192974576720179283)
  ·
    refine ⟨2741301289461865080268925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1827534192974576720179283 2741301289461865080268925)
    ·
      refine ⟨1027987983548199405100847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2741301289461865080268925 1027987983548199405100847)
      ·
        refine ⟨1541981975322299107651271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027987983548199405100847 1541981975322299107651271)
        ·
          refine ⟨2312972962983448661476907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541981975322299107651271 2312972962983448661476907)
          ·
            refine ⟨3469459444475172992215361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312972962983448661476907 3469459444475172992215361)
            ·
              refine ⟨2602094583356379744161521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3469459444475172992215361 2602094583356379744161521)
              ·
                refine ⟨1951570937517284808121141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602094583356379744161521 1951570937517284808121141)
                ·
                  refine ⟨182959775392245450761357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1951570937517284808121141 182959775392245450761357)
                  ·
                    refine ⟨68609915772092044035509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182959775392245450761357 68609915772092044035509)
                    ·
                      rfl

theorem cell22_200426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_200426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200426 prefixEnd_200426 := by exact prefixLift 200426
  have htrace : WordTrace (prefixWord ++ tailWord_200426) baseStart_200426 baseEnd_200426 := by
    simpa [prefixWord, tailWord_200426, baseEnd_200426] using wordTrace_append hprefix tailTrace_200426
  have hstable : (prefixWord ++ tailWord_200426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200426).length < 2 ^ (prefixWord ++ tailWord_200426).sum := by decide
  have hdescent : baseEnd_200426 < baseStart_200426 := by decide
  rcases family_descends (prefixWord ++ tailWord_200426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200439 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 7]
def baseStart_200439 : Nat := 118140960795 + 200439 * 2 ^ 59
def prefixEnd_200439 : Nat := 4983230072969 + 3 ^ 40 * 200439 * 2
def baseEnd_200439 : Nat := 22871455312588114486823

theorem tailTrace_200439 : CollatzResearch.WordTrace tailWord_200439 prefixEnd_200439 22871455312588114486823 := by
  unfold tailWord_200439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310610920851210100940371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4873740613900806733960247 7310610920851210100940371)
  ·
    refine ⟨10965916381276815151410557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7310610920851210100940371 10965916381276815151410557)
    ·
      refine ⟨4112218642978805681778959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10965916381276815151410557 4112218642978805681778959)
      ·
        refine ⟨6168327964468208522668439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112218642978805681778959 6168327964468208522668439)
        ·
          refine ⟨9252491946702312784002659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6168327964468208522668439 9252491946702312784002659)
          ·
            refine ⟨13878737920053469176003989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9252491946702312784002659 13878737920053469176003989)
            ·
              refine ⟨650565840002506367625187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13878737920053469176003989 650565840002506367625187)
              ·
                refine ⟨975848760003759551437781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650565840002506367625187 975848760003759551437781)
                ·
                  refine ⟨22871455312588114486823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 975848760003759551437781 22871455312588114486823)
                  ·
                    rfl

theorem cell22_200439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 7].length) (baseStart_200439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200439 prefixEnd_200439 := by exact prefixLift 200439
  have htrace : WordTrace (prefixWord ++ tailWord_200439) baseStart_200439 baseEnd_200439 := by
    simpa [prefixWord, tailWord_200439, baseEnd_200439] using wordTrace_append hprefix tailTrace_200439
  have hstable : (prefixWord ++ tailWord_200439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200439).length < 2 ^ (prefixWord ++ tailWord_200439).sum := by decide
  have hdescent : baseEnd_200439 < baseStart_200439 := by decide
  rcases family_descends (prefixWord ++ tailWord_200439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200456 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 5]
def baseStart_200456 : Nat := 118140960795 + 200456 * 2 ^ 59
def prefixEnd_200456 : Nat := 4983230072969 + 3 ^ 40 * 200456 * 2
def baseEnd_200456 : Nat := 22873395128393988595139

theorem tailTrace_200456 : CollatzResearch.WordTrace tailWord_200456 prefixEnd_200456 22873395128393988595139 := by
  unfold tailWord_200456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655615480894811002154611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4874153974526414669539481 3655615480894811002154611)
  ·
    refine ⟨5483423221342216503231917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3655615480894811002154611 5483423221342216503231917)
    ·
      refine ⟨2056283708003331188711969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5483423221342216503231917 2056283708003331188711969)
      ·
        refine ⟨1542212781002498391533977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2056283708003331188711969 1542212781002498391533977)
        ·
          refine ⟨1156659585751873793650483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1542212781002498391533977 1156659585751873793650483)
          ·
            refine ⟨1734989378627810690475725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156659585751873793650483 1734989378627810690475725)
            ·
              refine ⟨650621016985429008928397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1734989378627810690475725 650621016985429008928397)
              ·
                refine ⟨243982881369535878348149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650621016985429008928397 243982881369535878348149)
                ·
                  refine ⟨22873395128393988595139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243982881369535878348149 22873395128393988595139)
                  ·
                    rfl

theorem cell22_200456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_200456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200456 prefixEnd_200456 := by exact prefixLift 200456
  have htrace : WordTrace (prefixWord ++ tailWord_200456) baseStart_200456 baseEnd_200456 := by
    simpa [prefixWord, tailWord_200456, baseEnd_200456] using wordTrace_append hprefix tailTrace_200456
  have hstable : (prefixWord ++ tailWord_200456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200456).length < 2 ^ (prefixWord ++ tailWord_200456).sum := by decide
  have hdescent : baseEnd_200456 < baseStart_200456 := by decide
  rcases family_descends (prefixWord ++ tailWord_200456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200535 : List Nat := [1, 1, 3, 2, 5, 1, 2, 3, 4]
def baseStart_200535 : Nat := 118140960795 + 200535 * 2 ^ 59
def prefixEnd_200535 : Nat := 4983230072969 + 3 ^ 40 * 200535 * 2
def baseEnd_200535 : Nat := 22882409566550697686725

theorem tailTrace_200535 : CollatzResearch.WordTrace tailWord_200535 prefixEnd_200535 22882409566550697686725 := by
  unfold tailWord_200535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314112328503418496435059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4876074885668945664290039 7314112328503418496435059)
  ·
    refine ⟨10971168492755127744652589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314112328503418496435059 10971168492755127744652589)
    ·
      refine ⟨4114188184783172904244721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10971168492755127744652589 4114188184783172904244721)
      ·
        refine ⟨3085641138587379678183541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4114188184783172904244721 3085641138587379678183541)
        ·
          refine ⟨289278856742566844829707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3085641138587379678183541 289278856742566844829707)
          ·
            refine ⟨433918285113850267244561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289278856742566844829707 433918285113850267244561)
            ·
              refine ⟨325438713835387700433421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433918285113850267244561 325438713835387700433421)
              ·
                refine ⟨122039517688270387662533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325438713835387700433421 122039517688270387662533)
                ·
                  refine ⟨22882409566550697686725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122039517688270387662533 22882409566550697686725)
                  ·
                    rfl

theorem cell22_200535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 4].length) (baseStart_200535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200535 prefixEnd_200535 := by exact prefixLift 200535
  have htrace : WordTrace (prefixWord ++ tailWord_200535) baseStart_200535 baseEnd_200535 := by
    simpa [prefixWord, tailWord_200535, baseEnd_200535] using wordTrace_append hprefix tailTrace_200535
  have hstable : (prefixWord ++ tailWord_200535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200535).length < 2 ^ (prefixWord ++ tailWord_200535).sum := by decide
  have hdescent : baseEnd_200535 < baseStart_200535 := by decide
  rcases family_descends (prefixWord ++ tailWord_200535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200625 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 5]
def baseStart_200625 : Nat := 118140960795 + 200625 * 2 ^ 59
def prefixEnd_200625 : Nat := 4983230072969 + 3 ^ 40 * 200625 * 2
def baseEnd_200625 : Nat := 22892679179640619436633

theorem tailTrace_200625 : CollatzResearch.WordTrace tailWord_200625 prefixEnd_200625 22892679179640619436633 := by
  unfold tailWord_200625
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317394898177363867211329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4878263265451575911474219 7317394898177363867211329)
  ·
    refine ⟨5488046173633022900408497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7317394898177363867211329 5488046173633022900408497)
    ·
      refine ⟨4116034630224767175306373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5488046173633022900408497 4116034630224767175306373)
      ·
        refine ⟨771756493167143845369945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4116034630224767175306373 771756493167143845369945)
        ·
          refine ⟨578817369875357884027459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771756493167143845369945 578817369875357884027459)
          ·
            refine ⟨868226054813036826041189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578817369875357884027459 868226054813036826041189)
            ·
              refine ⟨162792385277444404882723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 868226054813036826041189 162792385277444404882723)
              ·
                refine ⟨244188577916166607324085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162792385277444404882723 244188577916166607324085)
                ·
                  refine ⟨22892679179640619436633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244188577916166607324085 22892679179640619436633)
                  ·
                    rfl

theorem cell22_200625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_200625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200625 prefixEnd_200625 := by exact prefixLift 200625
  have htrace : WordTrace (prefixWord ++ tailWord_200625) baseStart_200625 baseEnd_200625 := by
    simpa [prefixWord, tailWord_200625, baseEnd_200625] using wordTrace_append hprefix tailTrace_200625
  have hstable : (prefixWord ++ tailWord_200625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200625).length < 2 ^ (prefixWord ++ tailWord_200625).sum := by decide
  have hdescent : baseEnd_200625 < baseStart_200625 := by decide
  rcases family_descends (prefixWord ++ tailWord_200625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200655 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 1, 4]
def baseStart_200655 : Nat := 118140960795 + 200655 * 2 ^ 59
def prefixEnd_200655 : Nat := 4983230072969 + 3 ^ 40 * 200655 * 2
def baseEnd_200655 : Nat := 68688307152011780059807

theorem tailTrace_200655 : CollatzResearch.WordTrace tailWord_200655 prefixEnd_200655 68688307152011780059807 := by
  unfold tailWord_200655
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318489088068678990803419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4878992725379119327202279 7318489088068678990803419)
  ·
    refine ⟨10977733632103018486205129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7318489088068678990803419 10977733632103018486205129)
    ·
      refine ⟨8233300224077263864653847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10977733632103018486205129 8233300224077263864653847)
      ·
        refine ⟨12349950336115895796980771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233300224077263864653847 12349950336115895796980771)
        ·
          refine ⟨18524925504173843695471157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349950336115895796980771 18524925504173843695471157)
          ·
            refine ⟨1736711766016297846450421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18524925504173843695471157 1736711766016297846450421)
            ·
              refine ⟨162816728064027923104727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1736711766016297846450421 162816728064027923104727)
              ·
                refine ⟨244225092096041884657091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162816728064027923104727 244225092096041884657091)
                ·
                  refine ⟨366337638144062826985637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244225092096041884657091 366337638144062826985637)
                  ·
                    refine ⟨68688307152011780059807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366337638144062826985637 68688307152011780059807)
                    ·
                      rfl

theorem cell22_200655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_200655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200655 prefixEnd_200655 := by exact prefixLift 200655
  have htrace : WordTrace (prefixWord ++ tailWord_200655) baseStart_200655 baseEnd_200655 := by
    simpa [prefixWord, tailWord_200655, baseEnd_200655] using wordTrace_append hprefix tailTrace_200655
  have hstable : (prefixWord ++ tailWord_200655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200655).length < 2 ^ (prefixWord ++ tailWord_200655).sum := by decide
  have hdescent : baseEnd_200655 < baseStart_200655 := by decide
  rcases family_descends (prefixWord ++ tailWord_200655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200730 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_200730 : Nat := 118140960795 + 200730 * 2 ^ 59
def prefixEnd_200730 : Nat := 4983230072969 + 3 ^ 40 * 200730 * 2
def baseEnd_200730 : Nat := 68713981184736584434577

theorem tailTrace_200730 : CollatzResearch.WordTrace tailWord_200730 prefixEnd_200730 68713981184736584434577 := by
  unfold tailWord_200730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830306140699241699945911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4880816375197977866522429 1830306140699241699945911)
  ·
    refine ⟨2745459211048862549918867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1830306140699241699945911 2745459211048862549918867)
    ·
      refine ⟨4118188816573293824878301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2745459211048862549918867 4118188816573293824878301)
      ·
        refine ⟨1544320806214985184329363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4118188816573293824878301 1544320806214985184329363)
        ·
          refine ⟨2316481209322477776494045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544320806214985184329363 2316481209322477776494045)
          ·
            refine ⟨868680453495929166185267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2316481209322477776494045 868680453495929166185267)
            ·
              refine ⟨1303020680243893749277901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868680453495929166185267 1303020680243893749277901)
              ·
                refine ⟨488632755091460155979213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1303020680243893749277901 488632755091460155979213)
                ·
                  refine ⟨183237283159297558492205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488632755091460155979213 183237283159297558492205)
                  ·
                    refine ⟨68713981184736584434577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183237283159297558492205 68713981184736584434577)
                    ·
                      rfl

theorem cell22_200730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_200730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200730 prefixEnd_200730 := by exact prefixLift 200730
  have htrace : WordTrace (prefixWord ++ tailWord_200730) baseStart_200730 baseEnd_200730 := by
    simpa [prefixWord, tailWord_200730, baseEnd_200730] using wordTrace_append hprefix tailTrace_200730
  have hstable : (prefixWord ++ tailWord_200730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200730).length < 2 ^ (prefixWord ++ tailWord_200730).sum := by decide
  have hdescent : baseEnd_200730 < baseStart_200730 := by decide
  rcases family_descends (prefixWord ++ tailWord_200730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200773 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_200773 : Nat := 118140960795 + 200773 * 2 ^ 59
def prefixEnd_200773 : Nat := 4983230072969 + 3 ^ 40 * 200773 * 2
def baseEnd_200773 : Nat := 68728700963498805609445

theorem tailTrace_200773 : CollatzResearch.WordTrace tailWord_200773 prefixEnd_200773 68728700963498805609445 := by
  unfold tailWord_200773
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322792901641185143598973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4881861934427456762399315 7322792901641185143598973)
  ·
    refine ⟨2746047338115444428849615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7322792901641185143598973 2746047338115444428849615)
    ·
      refine ⟨4119071007173166643274423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746047338115444428849615 4119071007173166643274423)
      ·
        refine ⟨6178606510759749964911635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119071007173166643274423 6178606510759749964911635)
        ·
          refine ⟨9267909766139624947367453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178606510759749964911635 9267909766139624947367453)
          ·
            refine ⟨3475466162302359355262795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9267909766139624947367453 3475466162302359355262795)
            ·
              refine ⟨5213199243453539032894193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475466162302359355262795 5213199243453539032894193)
              ·
                refine ⟨3909899432590154274670645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5213199243453539032894193 3909899432590154274670645)
                ·
                  refine ⟨366553071805326963250373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3909899432590154274670645 366553071805326963250373)
                  ·
                    refine ⟨68728700963498805609445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366553071805326963250373 68728700963498805609445)
                    ·
                      rfl

theorem cell22_200773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_200773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200773 prefixEnd_200773 := by exact prefixLift 200773
  have htrace : WordTrace (prefixWord ++ tailWord_200773) baseStart_200773 baseEnd_200773 := by
    simpa [prefixWord, tailWord_200773, baseEnd_200773] using wordTrace_append hprefix tailTrace_200773
  have hstable : (prefixWord ++ tailWord_200773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200773).length < 2 ^ (prefixWord ++ tailWord_200773).sum := by decide
  have hdescent : baseEnd_200773 < baseStart_200773 := by decide
  rcases family_descends (prefixWord ++ tailWord_200773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200781 : List Nat := [1, 6, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_200781 : Nat := 118140960795 + 200781 * 2 ^ 59
def prefixEnd_200781 : Nat := 4983230072969 + 3 ^ 40 * 200781 * 2
def baseEnd_200781 : Nat := 68731439526989451409421

theorem tailTrace_200781 : CollatzResearch.WordTrace tailWord_200781 prefixEnd_200781 68731439526989451409421 := by
  unfold tailWord_200781
  simp only [CollatzResearch.WordTrace]
  refine ⟨7323084685612202509890197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4882056457074801673260131 7323084685612202509890197)
  ·
    refine ⟨343269594638071992651103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7323084685612202509890197 343269594638071992651103)
    ·
      refine ⟨514904391957107988976655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343269594638071992651103 514904391957107988976655)
      ·
        refine ⟨772356587935661983464983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514904391957107988976655 772356587935661983464983)
        ·
          refine ⟨1158534881903492975197475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772356587935661983464983 1158534881903492975197475)
          ·
            refine ⟨1737802322855239462796213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158534881903492975197475 1737802322855239462796213)
            ·
              refine ⟨162918967767678699637145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1737802322855239462796213 162918967767678699637145)
              ·
                refine ⟨122189225825759024727859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162918967767678699637145 122189225825759024727859)
                ·
                  refine ⟨183283838738638537091789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122189225825759024727859 183283838738638537091789)
                  ·
                    refine ⟨68731439526989451409421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183283838738638537091789 68731439526989451409421)
                    ·
                      rfl

theorem cell22_200781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_200781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200781 prefixEnd_200781 := by exact prefixLift 200781
  have htrace : WordTrace (prefixWord ++ tailWord_200781) baseStart_200781 baseEnd_200781 := by
    simpa [prefixWord, tailWord_200781, baseEnd_200781] using wordTrace_append hprefix tailTrace_200781
  have hstable : (prefixWord ++ tailWord_200781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200781).length < 2 ^ (prefixWord ++ tailWord_200781).sum := by decide
  have hdescent : baseEnd_200781 < baseStart_200781 := by decide
  rcases family_descends (prefixWord ++ tailWord_200781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200833 : List Nat := [1, 2, 4, 2, 13]
def baseStart_200833 : Nat := 118140960795 + 200833 * 2 ^ 59
def prefixEnd_200833 : Nat := 4983230072969 + 3 ^ 40 * 200833 * 2
def baseEnd_200833 : Nat := 282918683908142588927

theorem tailTrace_200833 : CollatzResearch.WordTrace tailWord_200833 prefixEnd_200833 282918683908142588927 := by
  unfold tailWord_200833
  simp only [CollatzResearch.WordTrace]
  refine ⟨7324981281423815390783153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4883320854282543593855435 7324981281423815390783153)
  ·
    refine ⟨5493735961067861543087365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7324981281423815390783153 5493735961067861543087365)
    ·
      refine ⟨1030075492700224039328881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5493735961067861543087365 1030075492700224039328881)
      ·
        refine ⟨772556619525168029496661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1030075492700224039328881 772556619525168029496661)
        ·
          refine ⟨282918683908142588927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 772556619525168029496661 282918683908142588927)
          ·
            rfl

theorem cell22_200833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 13].length) (baseStart_200833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200833 prefixEnd_200833 := by exact prefixLift 200833
  have htrace : WordTrace (prefixWord ++ tailWord_200833) baseStart_200833 baseEnd_200833 := by
    simpa [prefixWord, tailWord_200833, baseEnd_200833] using wordTrace_append hprefix tailTrace_200833
  have hstable : (prefixWord ++ tailWord_200833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200833).length < 2 ^ (prefixWord ++ tailWord_200833).sum := by decide
  have hdescent : baseEnd_200833 < baseStart_200833 := by decide
  rcases family_descends (prefixWord ++ tailWord_200833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200835 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 2, 4]
def baseStart_200835 : Nat := 118140960795 + 200835 * 2 ^ 59
def prefixEnd_200835 : Nat := 4983230072969 + 3 ^ 40 * 200835 * 2
def baseEnd_200835 : Nat := 68749924830551310559255

theorem tailTrace_200835 : CollatzResearch.WordTrace tailWord_200835 prefixEnd_200835 68749924830551310559255 := by
  unfold tailWord_200835
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325054227416569732355959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4883369484944379821570639 7325054227416569732355959)
  ·
    refine ⟨10987581341124854598533939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7325054227416569732355959 10987581341124854598533939)
    ·
      refine ⟨16481372011687281897800909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10987581341124854598533939 16481372011687281897800909)
      ·
        refine ⟨6180514504382730711675341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16481372011687281897800909 6180514504382730711675341)
        ·
          refine ⟨2317692939143524016878253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6180514504382730711675341 2317692939143524016878253)
          ·
            refine ⟨869134852178821506329345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2317692939143524016878253 869134852178821506329345)
            ·
              refine ⟨651851139134116129747009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869134852178821506329345 651851139134116129747009)
              ·
                refine ⟨488888354350587097310257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651851139134116129747009 488888354350587097310257)
                ·
                  refine ⟨366666265762940322982693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488888354350587097310257 366666265762940322982693)
                  ·
                    refine ⟨68749924830551310559255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366666265762940322982693 68749924830551310559255)
                    ·
                      rfl

theorem cell22_200835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_200835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200835 prefixEnd_200835 := by exact prefixLift 200835
  have htrace : WordTrace (prefixWord ++ tailWord_200835) baseStart_200835 baseEnd_200835 := by
    simpa [prefixWord, tailWord_200835, baseEnd_200835] using wordTrace_append hprefix tailTrace_200835
  have hstable : (prefixWord ++ tailWord_200835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200835).length < 2 ^ (prefixWord ++ tailWord_200835).sum := by decide
  have hdescent : baseEnd_200835 < baseStart_200835 := by decide
  rcases family_descends (prefixWord ++ tailWord_200835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200837 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_200837 : Nat := 118140960795 + 200837 * 2 ^ 59
def prefixEnd_200837 : Nat := 4983230072969 + 3 ^ 40 * 200837 * 2
def baseEnd_200837 : Nat := 68750609471423972009249

theorem tailTrace_200837 : CollatzResearch.WordTrace tailWord_200837 prefixEnd_200837 68750609471423972009249 := by
  unfold tailWord_200837
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325127173409324073928765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4883418115606216049285843 7325127173409324073928765)
  ·
    refine ⟨2746922690028496527723287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7325127173409324073928765 2746922690028496527723287)
    ·
      refine ⟨4120384035042744791584931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746922690028496527723287 4120384035042744791584931)
      ·
        refine ⟨6180576052564117187377397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120384035042744791584931 6180576052564117187377397)
        ·
          refine ⟨579429004927885986316631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6180576052564117187377397 579429004927885986316631)
          ·
            refine ⟨869143507391828979474947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579429004927885986316631 869143507391828979474947)
            ·
              refine ⟨1303715261087743469212421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869143507391828979474947 1303715261087743469212421)
              ·
                refine ⟨244446611453951900477329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1303715261087743469212421 244446611453951900477329)
                ·
                  refine ⟨183334958590463925357997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244446611453951900477329 183334958590463925357997)
                  ·
                    refine ⟨68750609471423972009249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183334958590463925357997 68750609471423972009249)
                    ·
                      rfl

theorem cell22_200837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_200837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200837 prefixEnd_200837 := by exact prefixLift 200837
  have htrace : WordTrace (prefixWord ++ tailWord_200837) baseStart_200837 baseEnd_200837 := by
    simpa [prefixWord, tailWord_200837, baseEnd_200837] using wordTrace_append hprefix tailTrace_200837
  have hstable : (prefixWord ++ tailWord_200837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200837).length < 2 ^ (prefixWord ++ tailWord_200837).sum := by decide
  have hdescent : baseEnd_200837 < baseStart_200837 := by decide
  rcases family_descends (prefixWord ++ tailWord_200837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200957 : List Nat := [1, 4, 1, 1, 1, 1, 1, 8, 4]
def baseStart_200957 : Nat := 118140960795 + 200957 * 2 ^ 59
def prefixEnd_200957 : Nat := 4983230072969 + 3 ^ 40 * 200957 * 2
def baseEnd_200957 : Nat := 22930562641261219669627

theorem tailTrace_200957 : CollatzResearch.WordTrace tailWord_200957 prefixEnd_200957 22930562641261219669627 := by
  unfold tailWord_200957
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329503932974584568297125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4886335955316389712198083 7329503932974584568297125)
  ·
    refine ⟨1374281987432734606555711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7329503932974584568297125 1374281987432734606555711)
    ·
      refine ⟨2061422981149101909833567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374281987432734606555711 2061422981149101909833567)
      ·
        refine ⟨3092134471723652864750351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061422981149101909833567 3092134471723652864750351)
        ·
          refine ⟨4638201707585479297125527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092134471723652864750351 4638201707585479297125527)
          ·
            refine ⟨6957302561378218945688291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638201707585479297125527 6957302561378218945688291)
            ·
              refine ⟨10435953842067328418532437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957302561378218945688291 10435953842067328418532437)
              ·
                refine ⟨122296334086726504904677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10435953842067328418532437 122296334086726504904677)
                ·
                  refine ⟨22930562641261219669627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122296334086726504904677 22930562641261219669627)
                  ·
                    rfl

theorem cell22_200957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_200957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200957 prefixEnd_200957 := by exact prefixLift 200957
  have htrace : WordTrace (prefixWord ++ tailWord_200957) baseStart_200957 baseEnd_200957 := by
    simpa [prefixWord, tailWord_200957, baseEnd_200957] using wordTrace_append hprefix tailTrace_200957
  have hstable : (prefixWord ++ tailWord_200957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200957).length < 2 ^ (prefixWord ++ tailWord_200957).sum := by decide
  have hdescent : baseEnd_200957 < baseStart_200957 := by decide
  rcases family_descends (prefixWord ++ tailWord_200957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200970 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_200970 : Nat := 118140960795 + 200970 * 2 ^ 59
def prefixEnd_200970 : Nat := 4983230072969 + 3 ^ 40 * 200970 * 2
def baseEnd_200970 : Nat := 68796138089455958433841

theorem tailTrace_200970 : CollatzResearch.WordTrace tailWord_200970 prefixEnd_200970 68796138089455958433841 := by
  unfold tailWord_200970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832494520481871947130091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4886652054618325192346909 1832494520481871947130091)
  ·
    refine ⟨2748741780722807920695137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1832494520481871947130091 2748741780722807920695137)
    ·
      refine ⟨2061556335542105940521353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2748741780722807920695137 2061556335542105940521353)
      ·
        refine ⟨1546167251656579455391015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2061556335542105940521353 1546167251656579455391015)
        ·
          refine ⟨2319250877484869183086523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546167251656579455391015 2319250877484869183086523)
          ·
            refine ⟨3478876316227303774629785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319250877484869183086523 3478876316227303774629785)
            ·
              refine ⟨2609157237170477830972339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3478876316227303774629785 2609157237170477830972339)
              ·
                refine ⟨3913735855755716746458509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609157237170477830972339 3913735855755716746458509)
                ·
                  refine ⟨1467650945908393779921941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3913735855755716746458509 1467650945908393779921941)
                  ·
                    refine ⟨68796138089455958433841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1467650945908393779921941 68796138089455958433841)
                    ·
                      rfl

theorem cell22_200970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_200970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200970 prefixEnd_200970 := by exact prefixLift 200970
  have htrace : WordTrace (prefixWord ++ tailWord_200970) baseStart_200970 baseEnd_200970 := by
    simpa [prefixWord, tailWord_200970, baseEnd_200970] using wordTrace_append hprefix tailTrace_200970
  have hstable : (prefixWord ++ tailWord_200970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200970).length < 2 ^ (prefixWord ++ tailWord_200970).sum := by decide
  have hdescent : baseEnd_200970 < baseStart_200970 := by decide
  rcases family_descends (prefixWord ++ tailWord_200970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200989 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_200989 : Nat := 118140960795 + 200989 * 2 ^ 59
def prefixEnd_200989 : Nat := 4983230072969 + 3 ^ 40 * 200989 * 2
def baseEnd_200989 : Nat := 68802642177746242208783

theorem tailTrace_200989 : CollatzResearch.WordTrace tailWord_200989 prefixEnd_200989 68802642177746242208783 := by
  unfold tailWord_200989
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330671068858654033462021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4887114045905769355641347 7330671068858654033462021)
  ·
    refine ⟨1374500825410997631274129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7330671068858654033462021 1374500825410997631274129)
    ·
      refine ⟨1030875619058248223455597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1374500825410997631274129 1030875619058248223455597)
      ·
        refine ⟨386578357146843083795849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1030875619058248223455597 386578357146843083795849)
        ·
          refine ⟨289933767860132312846887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386578357146843083795849 289933767860132312846887)
          ·
            refine ⟨434900651790198469270331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289933767860132312846887 434900651790198469270331)
            ·
              refine ⟨652350977685297703905497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434900651790198469270331 652350977685297703905497)
              ·
                refine ⟨489263233263973277929123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652350977685297703905497 489263233263973277929123)
                ·
                  refine ⟨733894849895959916893685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489263233263973277929123 733894849895959916893685)
                  ·
                    refine ⟨68802642177746242208783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 733894849895959916893685 68802642177746242208783)
                    ·
                      rfl

theorem cell22_200989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_200989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_200989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_200989 prefixEnd_200989 := by exact prefixLift 200989
  have htrace : WordTrace (prefixWord ++ tailWord_200989) baseStart_200989 baseEnd_200989 := by
    simpa [prefixWord, tailWord_200989, baseEnd_200989] using wordTrace_append hprefix tailTrace_200989
  have hstable : (prefixWord ++ tailWord_200989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200989).length < 2 ^ (prefixWord ++ tailWord_200989).sum := by decide
  have hdescent : baseEnd_200989 < baseStart_200989 := by decide
  rcases family_descends (prefixWord ++ tailWord_200989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201002 : List Nat := [3, 1, 4, 2, 2, 10]
def baseStart_201002 : Nat := 118140960795 + 201002 * 2 ^ 59
def prefixEnd_201002 : Nat := 4983230072969 + 3 ^ 40 * 201002 * 2
def baseEnd_201002 : Nat := 849470275844673353503

theorem tailTrace_201002 : CollatzResearch.WordTrace tailWord_201002 prefixEnd_201002 849470275844673353503 := by
  unfold tailWord_201002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832786304452889313421315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4887430145207704835790173 1832786304452889313421315)
  ·
    refine ⟨2749179456679333970131973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1832786304452889313421315 2749179456679333970131973)
    ·
      refine ⟨515471148127375119399745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2749179456679333970131973 515471148127375119399745)
      ·
        refine ⟨386603361095531339549809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515471148127375119399745 386603361095531339549809)
        ·
          refine ⟨289952520821648504662357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386603361095531339549809 289952520821648504662357)
          ·
            refine ⟨849470275844673353503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 289952520821648504662357 849470275844673353503)
            ·
              rfl

theorem cell22_201002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 10].length) (baseStart_201002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201002 prefixEnd_201002 := by exact prefixLift 201002
  have htrace : WordTrace (prefixWord ++ tailWord_201002) baseStart_201002 baseEnd_201002 := by
    simpa [prefixWord, tailWord_201002, baseEnd_201002] using wordTrace_append hprefix tailTrace_201002
  have hstable : (prefixWord ++ tailWord_201002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201002).length < 2 ^ (prefixWord ++ tailWord_201002).sum := by decide
  have hdescent : baseEnd_201002 < baseStart_201002 := by decide
  rcases family_descends (prefixWord ++ tailWord_201002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201064 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 5]
def baseStart_201064 : Nat := 118140960795 + 201064 * 2 ^ 59
def prefixEnd_201064 : Nat := 4983230072969 + 3 ^ 40 * 201064 * 2
def baseEnd_201064 : Nat := 22942772070157015527851

theorem tailTrace_201064 : CollatzResearch.WordTrace tailWord_201064 prefixEnd_201064 22942772070157015527851 := by
  unfold tailWord_201064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666703271793470921221123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4888937695724627894961497 3666703271793470921221123)
  ·
    refine ⟨5500054907690206381831685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3666703271793470921221123 5500054907690206381831685)
    ·
      refine ⟨1031260295191913696593441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5500054907690206381831685 1031260295191913696593441)
      ·
        refine ⟨773445221393935272445081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1031260295191913696593441 773445221393935272445081)
        ·
          refine ⟨580083916045451454333811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773445221393935272445081 580083916045451454333811)
          ·
            refine ⟨870125874068177181500717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580083916045451454333811 870125874068177181500717)
            ·
              refine ⟨326297202775566443062769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 870125874068177181500717 326297202775566443062769)
              ·
                refine ⟨244722902081674832297077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326297202775566443062769 244722902081674832297077)
                ·
                  refine ⟨22942772070157015527851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244722902081674832297077 22942772070157015527851)
                  ·
                    rfl

theorem cell22_201064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_201064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201064 prefixEnd_201064 := by exact prefixLift 201064
  have htrace : WordTrace (prefixWord ++ tailWord_201064) baseStart_201064 baseEnd_201064 := by
    simpa [prefixWord, tailWord_201064, baseEnd_201064] using wordTrace_append hprefix tailTrace_201064
  have hstable : (prefixWord ++ tailWord_201064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201064).length < 2 ^ (prefixWord ++ tailWord_201064).sum := by decide
  have hdescent : baseEnd_201064 < baseStart_201064 := by decide
  rcases family_descends (prefixWord ++ tailWord_201064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201075 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 10]
def baseStart_201075 : Nat := 118140960795 + 201075 * 2 ^ 59
def prefixEnd_201075 : Nat := 4983230072969 + 3 ^ 40 * 201075 * 2
def baseEnd_201075 : Nat := 22944027245090228186173

theorem tailTrace_201075 : CollatzResearch.WordTrace tailWord_201075 prefixEnd_201075 22944027245090228186173 := by
  unfold tailWord_201075
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333807746547090721092679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4889205164364727147395119 7333807746547090721092679)
  ·
    refine ⟨11000711619820636081639019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7333807746547090721092679 11000711619820636081639019)
    ·
      refine ⟨16501067429730954122458529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11000711619820636081639019 16501067429730954122458529)
      ·
        refine ⟨12375800572298215591843897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16501067429730954122458529 12375800572298215591843897)
        ·
          refine ⟨9281850429223661693882923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12375800572298215591843897 9281850429223661693882923)
          ·
            refine ⟨13922775643835492540824385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9281850429223661693882923 13922775643835492540824385)
            ·
              refine ⟨10442081732876619405618289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13922775643835492540824385 10442081732876619405618289)
              ·
                refine ⟨7831561299657464554213717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10442081732876619405618289 7831561299657464554213717)
                ·
                  refine ⟨22944027245090228186173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 7831561299657464554213717 22944027245090228186173)
                  ·
                    rfl

theorem cell22_201075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_201075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201075 prefixEnd_201075 := by exact prefixLift 201075
  have htrace : WordTrace (prefixWord ++ tailWord_201075) baseStart_201075 baseEnd_201075 := by
    simpa [prefixWord, tailWord_201075, baseEnd_201075] using wordTrace_append hprefix tailTrace_201075
  have hstable : (prefixWord ++ tailWord_201075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201075).length < 2 ^ (prefixWord ++ tailWord_201075).sum := by decide
  have hdescent : baseEnd_201075 < baseStart_201075 := by decide
  rcases family_descends (prefixWord ++ tailWord_201075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201092 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 6]
def baseStart_201092 : Nat := 118140960795 + 201092 * 2 ^ 59
def prefixEnd_201092 : Nat := 4983230072969 + 3 ^ 40 * 201092 * 2
def baseEnd_201092 : Nat := 22945967060896102294489

theorem tailTrace_201092 : CollatzResearch.WordTrace tailWord_201092 prefixEnd_201092 22945967060896102294489 := by
  unfold tailWord_201092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3667213893742751312230765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4889618524990335082974353 3667213893742751312230765)
  ·
    refine ⟨1375205210153531742086537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3667213893742751312230765 1375205210153531742086537)
    ·
      refine ⟨1031403907615148806564903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1375205210153531742086537 1031403907615148806564903)
      ·
        refine ⟨1547105861422723209847355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031403907615148806564903 1547105861422723209847355)
        ·
          refine ⟨2320658792134084814771033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547105861422723209847355 2320658792134084814771033)
          ·
            refine ⟨1740494094100563611078275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2320658792134084814771033 1740494094100563611078275)
            ·
              refine ⟨2610741141150845416617413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740494094100563611078275 2610741141150845416617413)
              ·
                refine ⟨489513963965783515615765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2610741141150845416617413 489513963965783515615765)
                ·
                  refine ⟨22945967060896102294489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 489513963965783515615765 22945967060896102294489)
                  ·
                    rfl

theorem cell22_201092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_201092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201092 prefixEnd_201092 := by exact prefixLift 201092
  have htrace : WordTrace (prefixWord ++ tailWord_201092) baseStart_201092 baseEnd_201092 := by
    simpa [prefixWord, tailWord_201092, baseEnd_201092] using wordTrace_append hprefix tailTrace_201092
  have hstable : (prefixWord ++ tailWord_201092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201092).length < 2 ^ (prefixWord ++ tailWord_201092).sum := by decide
  have hdescent : baseEnd_201092 < baseStart_201092 := by decide
  rcases family_descends (prefixWord ++ tailWord_201092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201124 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_201124 : Nat := 118140960795 + 201124 * 2 ^ 59
def prefixEnd_201124 : Nat := 4983230072969 + 3 ^ 40 * 201124 * 2
def baseEnd_201124 : Nat := 68848855436650890083369

theorem tailTrace_201124 : CollatzResearch.WordTrace tailWord_201124 prefixEnd_201124 68848855436650890083369 := by
  unfold tailWord_201124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3667797461684786044813213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4890396615579714726417617 3667797461684786044813213)
  ·
    refine ⟨1375424048131794766804955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3667797461684786044813213 1375424048131794766804955)
    ·
      refine ⟨2063136072197692150207433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375424048131794766804955 2063136072197692150207433)
      ·
        refine ⟨1547352054148269112655575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2063136072197692150207433 1547352054148269112655575)
        ·
          refine ⟨2321028081222403668983363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547352054148269112655575 2321028081222403668983363)
          ·
            refine ⟨3481542121833605503475045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321028081222403668983363 3481542121833605503475045)
            ·
              refine ⟨652789147843801031901571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3481542121833605503475045 652789147843801031901571)
              ·
                refine ⟨979183721765701547852357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652789147843801031901571 979183721765701547852357)
                ·
                  refine ⟨183596947831069040222317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979183721765701547852357 183596947831069040222317)
                  ·
                    refine ⟨68848855436650890083369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183596947831069040222317 68848855436650890083369)
                    ·
                      rfl

theorem cell22_201124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_201124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201124 prefixEnd_201124 := by exact prefixLift 201124
  have htrace : WordTrace (prefixWord ++ tailWord_201124) baseStart_201124 baseEnd_201124 := by
    simpa [prefixWord, tailWord_201124, baseEnd_201124] using wordTrace_append hprefix tailTrace_201124
  have hstable : (prefixWord ++ tailWord_201124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201124).length < 2 ^ (prefixWord ++ tailWord_201124).sum := by decide
  have hdescent : baseEnd_201124 < baseStart_201124 := by decide
  rcases family_descends (prefixWord ++ tailWord_201124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201137 : List Nat := [1, 2, 2, 4, 1, 2, 1, 9]
def baseStart_201137 : Nat := 118140960795 + 201137 * 2 ^ 59
def prefixEnd_201137 : Nat := 4983230072969 + 3 ^ 40 * 201137 * 2
def baseEnd_201137 : Nat := 7650367289147021056481

theorem tailTrace_201137 : CollatzResearch.WordTrace tailWord_201137 prefixEnd_201137 7650367289147021056481 := by
  unfold tailWord_201137
  simp only [CollatzResearch.WordTrace]
  refine ⟨7336069072322475309849665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4890712714881650206566443 7336069072322475309849665)
  ·
    refine ⟨5502051804241856482387249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7336069072322475309849665 5502051804241856482387249)
    ·
      refine ⟨4126538853181392361790437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5502051804241856482387249 4126538853181392361790437)
      ·
        refine ⟨773726034971511067835707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4126538853181392361790437 773726034971511067835707)
        ·
          refine ⟨1160589052457266601753561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773726034971511067835707 1160589052457266601753561)
          ·
            refine ⟨870441789342949951315171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160589052457266601753561 870441789342949951315171)
            ·
              refine ⟨1305662684014424926972757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870441789342949951315171 1305662684014424926972757)
              ·
                refine ⟨7650367289147021056481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1305662684014424926972757 7650367289147021056481)
                ·
                  rfl

theorem cell22_201137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 9].length) (baseStart_201137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201137 prefixEnd_201137 := by exact prefixLift 201137
  have htrace : WordTrace (prefixWord ++ tailWord_201137) baseStart_201137 baseEnd_201137 := by
    simpa [prefixWord, tailWord_201137, baseEnd_201137] using wordTrace_append hprefix tailTrace_201137
  have hstable : (prefixWord ++ tailWord_201137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201137).length < 2 ^ (prefixWord ++ tailWord_201137).sum := by decide
  have hdescent : baseEnd_201137 < baseStart_201137 := by decide
  rcases family_descends (prefixWord ++ tailWord_201137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201220 : List Nat := [2, 3, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_201220 : Nat := 118140960795 + 201220 * 2 ^ 59
def prefixEnd_201220 : Nat := 4983230072969 + 3 ^ 40 * 201220 * 2
def baseEnd_201220 : Nat := 68881718198538639683075

theorem tailTrace_201220 : CollatzResearch.WordTrace tailWord_201220 prefixEnd_201220 68881718198538639683075 := by
  unfold tailWord_201220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669548165510890242560557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4892730887347853656747409 3669548165510890242560557)
  ·
    refine ⟨1376080562066583840960209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3669548165510890242560557 1376080562066583840960209)
    ·
      refine ⟨1032060421549937880720157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1376080562066583840960209 1032060421549937880720157)
      ·
        refine ⟨387022658081226705270059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1032060421549937880720157 387022658081226705270059)
        ·
          refine ⟨580533987121840057905089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387022658081226705270059 580533987121840057905089)
          ·
            refine ⟨435400490341380043428817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580533987121840057905089 435400490341380043428817)
            ·
              refine ⟨326550367756035032571613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435400490341380043428817 326550367756035032571613)
              ·
                refine ⟨122456387908513137214355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326550367756035032571613 122456387908513137214355)
                ·
                  refine ⟨183684581862769705821533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122456387908513137214355 183684581862769705821533)
                  ·
                    refine ⟨68881718198538639683075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183684581862769705821533 68881718198538639683075)
                    ·
                      rfl

theorem cell22_201220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_201220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201220 prefixEnd_201220 := by exact prefixLift 201220
  have htrace : WordTrace (prefixWord ++ tailWord_201220) baseStart_201220 baseEnd_201220 := by
    simpa [prefixWord, tailWord_201220, baseEnd_201220] using wordTrace_append hprefix tailTrace_201220
  have hstable : (prefixWord ++ tailWord_201220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201220).length < 2 ^ (prefixWord ++ tailWord_201220).sum := by decide
  have hdescent : baseEnd_201220 < baseStart_201220 := by decide
  rcases family_descends (prefixWord ++ tailWord_201220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201244 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 6]
def baseStart_201244 : Nat := 118140960795 + 201244 * 2 ^ 59
def prefixEnd_201244 : Nat := 4983230072969 + 3 ^ 40 * 201244 * 2
def baseEnd_201244 : Nat := 22963311296336859027667

theorem tailTrace_201244 : CollatzResearch.WordTrace tailWord_201244 prefixEnd_201244 22963311296336859027667 := by
  unfold tailWord_201244
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669985841467416291997393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4893314455289888389329857 3669985841467416291997393)
  ·
    refine ⟨2752489381100562218998045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3669985841467416291997393 2752489381100562218998045)
    ·
      refine ⟨1032183517912710832124267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2752489381100562218998045 1032183517912710832124267)
      ·
        refine ⟨1548275276869066248186401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032183517912710832124267 1548275276869066248186401)
        ·
          refine ⟨1161206457651799686139801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1548275276869066248186401 1161206457651799686139801)
          ·
            refine ⟨870904843238849764604851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1161206457651799686139801 870904843238849764604851)
            ·
              refine ⟨1306357264858274646907277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870904843238849764604851 1306357264858274646907277)
              ·
                refine ⟨489883974321852992590229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1306357264858274646907277 489883974321852992590229)
                ·
                  refine ⟨22963311296336859027667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 489883974321852992590229 22963311296336859027667)
                  ·
                    rfl

theorem cell22_201244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_201244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201244 prefixEnd_201244 := by exact prefixLift 201244
  have htrace : WordTrace (prefixWord ++ tailWord_201244) baseStart_201244 baseEnd_201244 := by
    simpa [prefixWord, tailWord_201244, baseEnd_201244] using wordTrace_append hprefix tailTrace_201244
  have hstable : (prefixWord ++ tailWord_201244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201244).length < 2 ^ (prefixWord ++ tailWord_201244).sum := by decide
  have hdescent : baseEnd_201244 < baseStart_201244 := by decide
  rcases family_descends (prefixWord ++ tailWord_201244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201274 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_201274 : Nat := 118140960795 + 201274 * 2 ^ 59
def prefixEnd_201274 : Nat := 4983230072969 + 3 ^ 40 * 201274 * 2
def baseEnd_201274 : Nat := 68900203502100498832909

theorem tailTrace_201274 : CollatzResearch.WordTrace tailWord_201274 prefixEnd_201274 68900203502100498832909 := by
  unfold tailWord_201274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835266468206536926896719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4894043915217431805057917 1835266468206536926896719)
  ·
    refine ⟨2752899702309805390345079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1835266468206536926896719 2752899702309805390345079)
    ·
      refine ⟨4129349553464708085517619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752899702309805390345079 4129349553464708085517619)
      ·
        refine ⟨6194024330197062128276429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129349553464708085517619 6194024330197062128276429)
        ·
          refine ⟨2322759123823898298103661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6194024330197062128276429 2322759123823898298103661)
          ·
            refine ⟨871034671433961861788873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2322759123823898298103661 871034671433961861788873)
            ·
              refine ⟨653276003575471396341655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871034671433961861788873 653276003575471396341655)
              ·
                refine ⟨979914005363207094512483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653276003575471396341655 979914005363207094512483)
                ·
                  refine ⟨1469871008044810641768725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979914005363207094512483 1469871008044810641768725)
                  ·
                    refine ⟨68900203502100498832909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1469871008044810641768725 68900203502100498832909)
                    ·
                      rfl

theorem cell22_201274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_201274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201274 prefixEnd_201274 := by exact prefixLift 201274
  have htrace : WordTrace (prefixWord ++ tailWord_201274) baseStart_201274 baseEnd_201274 := by
    simpa [prefixWord, tailWord_201274, baseEnd_201274] using wordTrace_append hprefix tailTrace_201274
  have hstable : (prefixWord ++ tailWord_201274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201274).length < 2 ^ (prefixWord ++ tailWord_201274).sum := by decide
  have hdescent : baseEnd_201274 < baseStart_201274 := by decide
  rcases family_descends (prefixWord ++ tailWord_201274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201276 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_201276 : Nat := 118140960795 + 201276 * 2 ^ 59
def prefixEnd_201276 : Nat := 4983230072969 + 3 ^ 40 * 201276 * 2
def baseEnd_201276 : Nat := 68900888142973160282903

theorem tailTrace_201276 : CollatzResearch.WordTrace tailWord_201276 prefixEnd_201276 68900888142973160282903 := by
  unfold tailWord_201276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3670569409409451024579841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4894092545879268032773121 3670569409409451024579841)
  ·
    refine ⟨2752927057057088268434881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3670569409409451024579841 2752927057057088268434881)
    ·
      refine ⟨2064695292792816201326161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2752927057057088268434881 2064695292792816201326161)
      ·
        refine ⟨1548521469594612150994621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2064695292792816201326161 1548521469594612150994621)
        ·
          refine ⟨580695551097979556622983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1548521469594612150994621 580695551097979556622983)
          ·
            refine ⟨871043326646969334934475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580695551097979556622983 871043326646969334934475)
            ·
              refine ⟨1306564989970454002401713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871043326646969334934475 1306564989970454002401713)
              ·
                refine ⟨979923742477840501801285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306564989970454002401713 979923742477840501801285)
                ·
                  refine ⟨183735701714595094087741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979923742477840501801285 183735701714595094087741)
                  ·
                    refine ⟨68900888142973160282903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183735701714595094087741 68900888142973160282903)
                    ·
                      rfl

theorem cell22_201276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_201276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201276 prefixEnd_201276 := by exact prefixLift 201276
  have htrace : WordTrace (prefixWord ++ tailWord_201276) baseStart_201276 baseEnd_201276 := by
    simpa [prefixWord, tailWord_201276, baseEnd_201276] using wordTrace_append hprefix tailTrace_201276
  have hstable : (prefixWord ++ tailWord_201276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201276).length < 2 ^ (prefixWord ++ tailWord_201276).sum := by decide
  have hdescent : baseEnd_201276 < baseStart_201276 := by decide
  rcases family_descends (prefixWord ++ tailWord_201276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201293 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_201293 : Nat := 118140960795 + 201293 * 2 ^ 59
def prefixEnd_201293 : Nat := 4983230072969 + 3 ^ 40 * 201293 * 2
def baseEnd_201293 : Nat := 68906707590390782607851

theorem tailTrace_201293 : CollatzResearch.WordTrace tailWord_201293 prefixEnd_201293 68906707590390782607851 := by
  unfold tailWord_201293
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341758859757313952528533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4894505906504875968352355 7341758859757313952528533)
  ·
    refine ⟨344144946551124091524775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7341758859757313952528533 344144946551124091524775)
    ·
      refine ⟨516217419826686137287163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344144946551124091524775 516217419826686137287163)
      ·
        refine ⟨774326129740029205930745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516217419826686137287163 774326129740029205930745)
        ·
          refine ⟨580744597305021904448059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774326129740029205930745 580744597305021904448059)
          ·
            refine ⟨871116895957532856672089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580744597305021904448059 871116895957532856672089)
            ·
              refine ⟨653337671968149642504067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871116895957532856672089 653337671968149642504067)
              ·
                refine ⟨980006507952224463756101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653337671968149642504067 980006507952224463756101)
                ·
                  refine ⟨183751220241042086954269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980006507952224463756101 183751220241042086954269)
                  ·
                    refine ⟨68906707590390782607851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183751220241042086954269 68906707590390782607851)
                    ·
                      rfl

theorem cell22_201293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_201293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201293 prefixEnd_201293 := by exact prefixLift 201293
  have htrace : WordTrace (prefixWord ++ tailWord_201293) baseStart_201293 baseEnd_201293 := by
    simpa [prefixWord, tailWord_201293, baseEnd_201293] using wordTrace_append hprefix tailTrace_201293
  have hstable : (prefixWord ++ tailWord_201293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201293).length < 2 ^ (prefixWord ++ tailWord_201293).sum := by decide
  have hdescent : baseEnd_201293 < baseStart_201293 := by decide
  rcases family_descends (prefixWord ++ tailWord_201293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201346 : List Nat := [3, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_201346 : Nat := 118140960795 + 201346 * 2 ^ 59
def prefixEnd_201346 : Nat := 4983230072969 + 3 ^ 40 * 201346 * 2
def baseEnd_201346 : Nat := 22974950191172103677563

theorem tailTrace_201346 : CollatzResearch.WordTrace tailWord_201346 prefixEnd_201346 22974950191172103677563 := by
  unfold tailWord_201346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835922982141326001051973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4895794619043536002805261 1835922982141326001051973)
  ·
    refine ⟨344235559151498625197245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1835922982141326001051973 344235559151498625197245)
    ·
      refine ⟨129088334681811984448967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344235559151498625197245 129088334681811984448967)
      ·
        refine ⟨193632502022717976673451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129088334681811984448967 193632502022717976673451)
        ·
          refine ⟨290448753034076965010177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193632502022717976673451 290448753034076965010177)
          ·
            refine ⟨217836564775557723757633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290448753034076965010177 217836564775557723757633)
            ·
              refine ⟨163377423581668292818225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217836564775557723757633 163377423581668292818225)
              ·
                refine ⟨122533067686251219613669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163377423581668292818225 122533067686251219613669)
                ·
                  refine ⟨22974950191172103677563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122533067686251219613669 22974950191172103677563)
                  ·
                    rfl

theorem cell22_201346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_201346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201346 prefixEnd_201346 := by exact prefixLift 201346
  have htrace : WordTrace (prefixWord ++ tailWord_201346) baseStart_201346 baseEnd_201346 := by
    simpa [prefixWord, tailWord_201346, baseEnd_201346] using wordTrace_append hprefix tailTrace_201346
  have hstable : (prefixWord ++ tailWord_201346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201346).length < 2 ^ (prefixWord ++ tailWord_201346).sum := by decide
  have hdescent : baseEnd_201346 < baseStart_201346 := by decide
  rcases family_descends (prefixWord ++ tailWord_201346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201351 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 5]
def baseStart_201351 : Nat := 118140960795 + 201351 * 2 ^ 59
def prefixEnd_201351 : Nat := 4983230072969 + 3 ^ 40 * 201351 * 2
def baseEnd_201351 : Nat := 22975520725232654885891

theorem tailTrace_201351 : CollatzResearch.WordTrace tailWord_201351 prefixEnd_201351 22975520725232654885891 := by
  unfold tailWord_201351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7343874293547189858139907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4895916195698126572093271 7343874293547189858139907)
  ·
    refine ⟨11015811440320784787209861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7343874293547189858139907 11015811440320784787209861)
    ·
      refine ⟨2065464645060147147601849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11015811440320784787209861 2065464645060147147601849)
      ·
        refine ⟨1549098483795110360701387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2065464645060147147601849 1549098483795110360701387)
        ·
          refine ⟨2323647725692665541052081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549098483795110360701387 2323647725692665541052081)
          ·
            refine ⟨1742735794269499155789061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323647725692665541052081 1742735794269499155789061)
            ·
              refine ⟨326762961425531091710449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1742735794269499155789061 326762961425531091710449)
              ·
                refine ⟨245072221069148318782837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326762961425531091710449 245072221069148318782837)
                ·
                  refine ⟨22975520725232654885891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245072221069148318782837 22975520725232654885891)
                  ·
                    rfl

theorem cell22_201351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 5].length) (baseStart_201351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201351 prefixEnd_201351 := by exact prefixLift 201351
  have htrace : WordTrace (prefixWord ++ tailWord_201351) baseStart_201351 baseEnd_201351 := by
    simpa [prefixWord, tailWord_201351, baseEnd_201351] using wordTrace_append hprefix tailTrace_201351
  have hstable : (prefixWord ++ tailWord_201351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201351).length < 2 ^ (prefixWord ++ tailWord_201351).sum := by decide
  have hdescent : baseEnd_201351 < baseStart_201351 := by decide
  rcases family_descends (prefixWord ++ tailWord_201351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201381 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_201381 : Nat := 118140960795 + 201381 * 2 ^ 59
def prefixEnd_201381 : Nat := 4983230072969 + 3 ^ 40 * 201381 * 2
def baseEnd_201381 : Nat := 68936831788787886407581

theorem tailTrace_201381 : CollatzResearch.WordTrace tailWord_201381 prefixEnd_201381 68936831788787886407581 := by
  unfold tailWord_201381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344968483438504981731997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4896645655625669987821331 7344968483438504981731997)
  ·
    refine ⟨2754363181289439368149499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7344968483438504981731997 2754363181289439368149499)
    ·
      refine ⟨4131544771934159052224249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2754363181289439368149499 4131544771934159052224249)
      ·
        refine ⟨3098658578950619289168187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4131544771934159052224249 3098658578950619289168187)
        ·
          refine ⟨4647987868425928933752281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098658578950619289168187 4647987868425928933752281)
          ·
            refine ⟨3485990901319446700314211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4647987868425928933752281 3485990901319446700314211)
            ·
              refine ⟨5228986351979170050471317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485990901319446700314211 5228986351979170050471317)
              ·
                refine ⟨245108735249023596115843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5228986351979170050471317 245108735249023596115843)
                ·
                  refine ⟨367663102873535394173765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245108735249023596115843 367663102873535394173765)
                  ·
                    refine ⟨68936831788787886407581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 367663102873535394173765 68936831788787886407581)
                    ·
                      rfl

theorem cell22_201381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_201381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201381 prefixEnd_201381 := by exact prefixLift 201381
  have htrace : WordTrace (prefixWord ++ tailWord_201381) baseStart_201381 baseEnd_201381 := by
    simpa [prefixWord, tailWord_201381, baseEnd_201381] using wordTrace_append hprefix tailTrace_201381
  have hstable : (prefixWord ++ tailWord_201381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201381).length < 2 ^ (prefixWord ++ tailWord_201381).sum := by decide
  have hdescent : baseEnd_201381 < baseStart_201381 := by decide
  rcases family_descends (prefixWord ++ tailWord_201381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201441 : List Nat := [1, 2, 3, 1, 4, 2, 1, 8]
def baseStart_201441 : Nat := 118140960795 + 201441 * 2 ^ 59
def prefixEnd_201441 : Nat := 4983230072969 + 3 ^ 40 * 201441 * 2
def baseEnd_201441 : Nat := 7661930112774192211933

theorem tailTrace_201441 : CollatzResearch.WordTrace tailWord_201441 prefixEnd_201441 7661930112774192211933 := by
  unfold tailWord_201441
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347156863221135228916177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4898104575480756819277451 7347156863221135228916177)
  ·
    refine ⟨5510367647415851421687133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7347156863221135228916177 5510367647415851421687133)
    ·
      refine ⟨2066387867780944283132675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5510367647415851421687133 2066387867780944283132675)
      ·
        refine ⟨3099581801671416424699013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066387867780944283132675 3099581801671416424699013)
        ·
          refine ⟨581171587813390579631065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3099581801671416424699013 581171587813390579631065)
          ·
            refine ⟨435878690860042934723299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581171587813390579631065 435878690860042934723299)
            ·
              refine ⟨653818036290064402084949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435878690860042934723299 653818036290064402084949)
              ·
                refine ⟨7661930112774192211933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 653818036290064402084949 7661930112774192211933)
                ·
                  rfl

theorem cell22_201441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 8].length) (baseStart_201441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201441 prefixEnd_201441 := by exact prefixLift 201441
  have htrace : WordTrace (prefixWord ++ tailWord_201441) baseStart_201441 baseEnd_201441 := by
    simpa [prefixWord, tailWord_201441, baseEnd_201441] using wordTrace_append hprefix tailTrace_201441
  have hstable : (prefixWord ++ tailWord_201441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201441).length < 2 ^ (prefixWord ++ tailWord_201441).sum := by decide
  have hdescent : baseEnd_201441 < baseStart_201441 := by decide
  rcases family_descends (prefixWord ++ tailWord_201441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201524 : List Nat := [2, 5, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_201524 : Nat := 118140960795 + 201524 * 2 ^ 59
def prefixEnd_201524 : Nat := 4983230072969 + 3 ^ 40 * 201524 * 2
def baseEnd_201524 : Nat := 68985783611183180082143

theorem tailTrace_201524 : CollatzResearch.WordTrace tailWord_201524 prefixEnd_201524 68985783611183180082143 := by
  unfold tailWord_201524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675092060960220202093813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4900122747946960269458417 3675092060960220202093813)
  ·
    refine ⟨344539880715020643946295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3675092060960220202093813 344539880715020643946295)
    ·
      refine ⟨516809821072530965919443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344539880715020643946295 516809821072530965919443)
      ·
        refine ⟨775214731608796448879165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516809821072530965919443 775214731608796448879165)
        ·
          refine ⟨290705524353298668329687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 775214731608796448879165 290705524353298668329687)
          ·
            refine ⟨436058286529948002494531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290705524353298668329687 436058286529948002494531)
            ·
              refine ⟨654087429794922003741797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436058286529948002494531 654087429794922003741797)
              ·
                refine ⟨122641393086547875701587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654087429794922003741797 122641393086547875701587)
                ·
                  refine ⟨183962089629821813552381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122641393086547875701587 183962089629821813552381)
                  ·
                    refine ⟨68985783611183180082143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183962089629821813552381 68985783611183180082143)
                    ·
                      rfl

theorem cell22_201524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_201524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201524 prefixEnd_201524 := by exact prefixLift 201524
  have htrace : WordTrace (prefixWord ++ tailWord_201524) baseStart_201524 baseEnd_201524 := by
    simpa [prefixWord, tailWord_201524, baseEnd_201524] using wordTrace_append hprefix tailTrace_201524
  have hstable : (prefixWord ++ tailWord_201524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201524).length < 2 ^ (prefixWord ++ tailWord_201524).sum := by decide
  have hdescent : baseEnd_201524 < baseStart_201524 := by decide
  rcases family_descends (prefixWord ++ tailWord_201524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201548 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 6]
def baseStart_201548 : Nat := 118140960795 + 201548 * 2 ^ 59
def prefixEnd_201548 : Nat := 4983230072969 + 3 ^ 40 * 201548 * 2
def baseEnd_201548 : Nat := 22997999767218372494023

theorem tailTrace_201548 : CollatzResearch.WordTrace tailWord_201548 prefixEnd_201548 22997999767218372494023 := by
  unfold tailWord_201548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675529736916746251530649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4900706315888995002040865 3675529736916746251530649)
  ·
    refine ⟨2756647302687559688647987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3675529736916746251530649 2756647302687559688647987)
    ·
      refine ⟨4134970954031339532971981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2756647302687559688647987 4134970954031339532971981)
      ·
        refine ⟨1550614107761752324864493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4134970954031339532971981 1550614107761752324864493)
        ·
          refine ⟨581480290410657121824185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1550614107761752324864493 581480290410657121824185)
          ·
            refine ⟨436110217807992841368139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581480290410657121824185 436110217807992841368139)
            ·
              refine ⟨654165326711989262052209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436110217807992841368139 654165326711989262052209)
              ·
                refine ⟨490623995033991946539157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654165326711989262052209 490623995033991946539157)
                ·
                  refine ⟨22997999767218372494023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 490623995033991946539157 22997999767218372494023)
                  ·
                    rfl

theorem cell22_201548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_201548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201548 prefixEnd_201548 := by exact prefixLift 201548
  have htrace : WordTrace (prefixWord ++ tailWord_201548) baseStart_201548 baseEnd_201548 := by
    simpa [prefixWord, tailWord_201548, baseEnd_201548] using wordTrace_append hprefix tailTrace_201548
  have hstable : (prefixWord ++ tailWord_201548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201548).length < 2 ^ (prefixWord ++ tailWord_201548).sum := by decide
  have hdescent : baseEnd_201548 < baseStart_201548 := by decide
  rcases family_descends (prefixWord ++ tailWord_201548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201610 : List Nat := [3, 1, 2, 4, 1, 1, 4, 6]
def baseStart_201610 : Nat := 118140960795 + 201610 * 2 ^ 59
def prefixEnd_201610 : Nat := 4983230072969 + 3 ^ 40 * 201610 * 2
def baseEnd_201610 : Nat := 7668358129856402492431

theorem tailTrace_201610 : CollatzResearch.WordTrace tailWord_201610 prefixEnd_201610 7668358129856402492431 := by
  unfold tailWord_201610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838330199902219272954571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4902213866405918061212189 1838330199902219272954571)
  ·
    refine ⟨2757495299853328909431857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1838330199902219272954571 2757495299853328909431857)
    ·
      refine ⟨2068121474889996682073893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2757495299853328909431857 2068121474889996682073893)
      ·
        refine ⟨387772776541874377888855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2068121474889996682073893 387772776541874377888855)
        ·
          refine ⟨581659164812811566833283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387772776541874377888855 581659164812811566833283)
          ·
            refine ⟨872488747219217350249925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581659164812811566833283 872488747219217350249925)
            ·
              refine ⟨163591640103603253171861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 872488747219217350249925 163591640103603253171861)
              ·
                refine ⟨7668358129856402492431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163591640103603253171861 7668358129856402492431)
                ·
                  rfl

theorem cell22_201610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_201610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201610 prefixEnd_201610 := by exact prefixLift 201610
  have htrace : WordTrace (prefixWord ++ tailWord_201610) baseStart_201610 baseEnd_201610 := by
    simpa [prefixWord, tailWord_201610, baseEnd_201610] using wordTrace_append hprefix tailTrace_201610
  have hstable : (prefixWord ++ tailWord_201610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201610).length < 2 ^ (prefixWord ++ tailWord_201610).sum := by decide
  have hdescent : baseEnd_201610 < baseStart_201610 := by decide
  rcases family_descends (prefixWord ++ tailWord_201610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201653 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_201653 : Nat := 118140960795 + 201653 * 2 ^ 59
def prefixEnd_201653 : Nat := 4983230072969 + 3 ^ 40 * 201653 * 2
def baseEnd_201653 : Nat := 69029942947469843606747

theorem tailTrace_201653 : CollatzResearch.WordTrace tailWord_201653 prefixEnd_201653 69029942947469843606747 := by
  unfold tailWord_201653
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354889138453095435633613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4903259425635396957089075 7354889138453095435633613)
  ·
    refine ⟨2758083426919910788362605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7354889138453095435633613 2758083426919910788362605)
    ·
      refine ⟨1034281285094966545635977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2758083426919910788362605 1034281285094966545635977)
      ·
        refine ⟨775710963821224909226983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1034281285094966545635977 775710963821224909226983)
        ·
          refine ⟨1163566445731837363840475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775710963821224909226983 1163566445731837363840475)
          ·
            refine ⟨1745349668597756045760713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163566445731837363840475 1745349668597756045760713)
            ·
              refine ⟨1309012251448317034320535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745349668597756045760713 1309012251448317034320535)
              ·
                refine ⟨1963518377172475551480803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309012251448317034320535 1963518377172475551480803)
                ·
                  refine ⟨2945277565758713327221205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963518377172475551480803 2945277565758713327221205)
                  ·
                    refine ⟨69029942947469843606747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2945277565758713327221205 69029942947469843606747)
                    ·
                      rfl

theorem cell22_201653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_201653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201653 prefixEnd_201653 := by exact prefixLift 201653
  have htrace : WordTrace (prefixWord ++ tailWord_201653) baseStart_201653 baseEnd_201653 := by
    simpa [prefixWord, tailWord_201653, baseEnd_201653] using wordTrace_append hprefix tailTrace_201653
  have hstable : (prefixWord ++ tailWord_201653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201653).length < 2 ^ (prefixWord ++ tailWord_201653).sum := by decide
  have hdescent : baseEnd_201653 < baseStart_201653 := by decide
  rcases family_descends (prefixWord ++ tailWord_201653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201655 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 5]
def baseStart_201655 : Nat := 118140960795 + 201655 * 2 ^ 59
def prefixEnd_201655 : Nat := 4983230072969 + 3 ^ 40 * 201655 * 2
def baseEnd_201655 : Nat := 23010209196114168352247

theorem tailTrace_201655 : CollatzResearch.WordTrace tailWord_201655 prefixEnd_201655 23010209196114168352247 := by
  unfold tailWord_201655
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354962084445849777206419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4903308056297233184804279 7354962084445849777206419)
  ·
    refine ⟨11032443126668774665809629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7354962084445849777206419 11032443126668774665809629)
    ·
      refine ⟨4137166172500790499678611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11032443126668774665809629 4137166172500790499678611)
      ·
        refine ⟨6205749258751185749517917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137166172500790499678611 6205749258751185749517917)
        ·
          refine ⟨2327155972031694656069219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6205749258751185749517917 2327155972031694656069219)
          ·
            refine ⟨3490733958047541984103829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327155972031694656069219 3490733958047541984103829)
            ·
              refine ⟨163628154283478530504867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3490733958047541984103829 163628154283478530504867)
              ·
                refine ⟨245442231425217795757301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163628154283478530504867 245442231425217795757301)
                ·
                  refine ⟨23010209196114168352247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245442231425217795757301 23010209196114168352247)
                  ·
                    rfl

theorem cell22_201655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 5].length) (baseStart_201655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201655 prefixEnd_201655 := by exact prefixLift 201655
  have htrace : WordTrace (prefixWord ++ tailWord_201655) baseStart_201655 baseEnd_201655 := by
    simpa [prefixWord, tailWord_201655, baseEnd_201655] using wordTrace_append hprefix tailTrace_201655
  have hstable : (prefixWord ++ tailWord_201655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201655).length < 2 ^ (prefixWord ++ tailWord_201655).sum := by decide
  have hdescent : baseEnd_201655 < baseStart_201655 := by decide
  rcases family_descends (prefixWord ++ tailWord_201655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201749 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_201749 : Nat := 118140960795 + 201749 * 2 ^ 59
def prefixEnd_201749 : Nat := 4983230072969 + 3 ^ 40 * 201749 * 2
def baseEnd_201749 : Nat := 69062805709357593206453

theorem tailTrace_201749 : CollatzResearch.WordTrace tailWord_201749 prefixEnd_201749 69062805709357593206453 := by
  unfold tailWord_201749
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358390546105303831128301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4905593697403535887418867 7358390546105303831128301)
  ·
    refine ⟨2759396454789488936673113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7358390546105303831128301 2759396454789488936673113)
    ·
      refine ⟨2069547341092116702504835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2759396454789488936673113 2069547341092116702504835)
      ·
        refine ⟨3104321011638175053757253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069547341092116702504835 3104321011638175053757253)
        ·
          refine ⟨582060189682157822579485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3104321011638175053757253 582060189682157822579485)
          ·
            refine ⟨218272571130809183467307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 582060189682157822579485 218272571130809183467307)
            ·
              refine ⟨327408856696213775200961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218272571130809183467307 327408856696213775200961)
              ·
                refine ⟨245556642522160331400721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327408856696213775200961 245556642522160331400721)
                ·
                  refine ⟨184167481891620248550541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245556642522160331400721 184167481891620248550541)
                  ·
                    refine ⟨69062805709357593206453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184167481891620248550541 69062805709357593206453)
                    ·
                      rfl

theorem cell22_201749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_201749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201749 prefixEnd_201749 := by exact prefixLift 201749
  have htrace : WordTrace (prefixWord ++ tailWord_201749) baseStart_201749 baseEnd_201749 := by
    simpa [prefixWord, tailWord_201749, baseEnd_201749] using wordTrace_append hprefix tailTrace_201749
  have hstable : (prefixWord ++ tailWord_201749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201749).length < 2 ^ (prefixWord ++ tailWord_201749).sum := by decide
  have hdescent : baseEnd_201749 < baseStart_201749 := by decide
  rcases family_descends (prefixWord ++ tailWord_201749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201837 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_201837 : Nat := 118140960795 + 201837 * 2 ^ 59
def prefixEnd_201837 : Nat := 4983230072969 + 3 ^ 40 * 201837 * 2
def baseEnd_201837 : Nat := 69092929907754697006183

theorem tailTrace_201837 : CollatzResearch.WordTrace tailWord_201837 prefixEnd_201837 69092929907754697006183 := by
  unfold tailWord_201837
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361600169786494860331765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4907733446524329906887843 7361600169786494860331765)
  ·
    refine ⟨690150015917483893156103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7361600169786494860331765 690150015917483893156103)
    ·
      refine ⟨1035225023876225839734155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 690150015917483893156103 1035225023876225839734155)
      ·
        refine ⟨1552837535814338759601233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035225023876225839734155 1552837535814338759601233)
        ·
          refine ⟨1164628151860754069700925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552837535814338759601233 1164628151860754069700925)
          ·
            refine ⟨436735556947782776137847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1164628151860754069700925 436735556947782776137847)
            ·
              refine ⟨655103335421674164206771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436735556947782776137847 655103335421674164206771)
              ·
                refine ⟨982655003132511246310157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655103335421674164206771 982655003132511246310157)
                ·
                  refine ⟨368495626174691717366309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982655003132511246310157 368495626174691717366309)
                  ·
                    refine ⟨69092929907754697006183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 368495626174691717366309 69092929907754697006183)
                    ·
                      rfl

theorem cell22_201837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_201837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201837 prefixEnd_201837 := by exact prefixLift 201837
  have htrace : WordTrace (prefixWord ++ tailWord_201837) baseStart_201837 baseEnd_201837 := by
    simpa [prefixWord, tailWord_201837, baseEnd_201837] using wordTrace_append hprefix tailTrace_201837
  have hstable : (prefixWord ++ tailWord_201837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201837).length < 2 ^ (prefixWord ++ tailWord_201837).sum := by decide
  have hdescent : baseEnd_201837 < baseStart_201837 := by decide
  rcases family_descends (prefixWord ++ tailWord_201837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201852 : List Nat := [2, 2, 2, 1, 1, 3, 2, 5, 4]
def baseStart_201852 : Nat := 118140960795 + 201852 * 2 ^ 59
def prefixEnd_201852 : Nat := 4983230072969 + 3 ^ 40 * 201852 * 2
def baseEnd_201852 : Nat := 23032688238099885960379

theorem tailTrace_201852 : CollatzResearch.WordTrace tailWord_201852 prefixEnd_201852 23032688238099885960379 := by
  unfold tailWord_201852
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681073632366076211063905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4908098176488101614751873 3681073632366076211063905)
  ·
    refine ⟨2760805224274557158297929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3681073632366076211063905 2760805224274557158297929)
    ·
      refine ⟨2070603918205917868723447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2760805224274557158297929 2070603918205917868723447)
      ·
        refine ⟨3105905877308876803085171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070603918205917868723447 3105905877308876803085171)
        ·
          refine ⟨4658858815963315204627757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105905877308876803085171 4658858815963315204627757)
          ·
            refine ⟨1747072055986243201735409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4658858815963315204627757 1747072055986243201735409)
            ·
              refine ⟨1310304041989682401301557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1747072055986243201735409 1310304041989682401301557)
              ·
                refine ⟨122841003936532725122021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1310304041989682401301557 122841003936532725122021)
                ·
                  refine ⟨23032688238099885960379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122841003936532725122021 23032688238099885960379)
                  ·
                    rfl

theorem cell22_201852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_201852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201852 prefixEnd_201852 := by exact prefixLift 201852
  have htrace : WordTrace (prefixWord ++ tailWord_201852) baseStart_201852 baseEnd_201852 := by
    simpa [prefixWord, tailWord_201852, baseEnd_201852] using wordTrace_append hprefix tailTrace_201852
  have hstable : (prefixWord ++ tailWord_201852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201852).length < 2 ^ (prefixWord ++ tailWord_201852).sum := by decide
  have hdescent : baseEnd_201852 < baseStart_201852 := by decide
  rcases family_descends (prefixWord ++ tailWord_201852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201884 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_201884 : Nat := 118140960795 + 201884 * 2 ^ 59
def prefixEnd_201884 : Nat := 4983230072969 + 3 ^ 40 * 201884 * 2
def baseEnd_201884 : Nat := 69109018968262241081039

theorem tailTrace_201884 : CollatzResearch.WordTrace tailWord_201884 prefixEnd_201884 69109018968262241081039 := by
  unfold tailWord_201884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681657200308110943646353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4908876267077481258195137 3681657200308110943646353)
  ·
    refine ⟨2761242900231083207734765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3681657200308110943646353 2761242900231083207734765)
    ·
      refine ⟨1035466087586656202900537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2761242900231083207734765 1035466087586656202900537)
      ·
        refine ⟨776599565689992152175403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1035466087586656202900537 776599565689992152175403)
        ·
          refine ⟨1164899348534988228263105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776599565689992152175403 1164899348534988228263105)
          ·
            refine ⟨873674511401241171197329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164899348534988228263105 873674511401241171197329)
            ·
              refine ⟨655255883550930878397997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873674511401241171197329 655255883550930878397997)
              ·
                refine ⟨245720956331599079399249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 655255883550930878397997 245720956331599079399249)
                ·
                  refine ⟨184290717248699309549437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245720956331599079399249 184290717248699309549437)
                  ·
                    refine ⟨69109018968262241081039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184290717248699309549437 69109018968262241081039)
                    ·
                      rfl

theorem cell22_201884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_201884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201884 prefixEnd_201884 := by exact prefixLift 201884
  have htrace : WordTrace (prefixWord ++ tailWord_201884) baseStart_201884 baseEnd_201884 := by
    simpa [prefixWord, tailWord_201884, baseEnd_201884] using wordTrace_append hprefix tailTrace_201884
  have hstable : (prefixWord ++ tailWord_201884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201884).length < 2 ^ (prefixWord ++ tailWord_201884).sum := by decide
  have hdescent : baseEnd_201884 < baseStart_201884 := by decide
  rcases family_descends (prefixWord ++ tailWord_201884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201987 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 6]
def baseStart_201987 : Nat := 118140960795 + 201987 * 2 ^ 59
def prefixEnd_201987 : Nat := 4983230072969 + 3 ^ 40 * 201987 * 2
def baseEnd_201987 : Nat := 23048092657734768585241

theorem tailTrace_201987 : CollatzResearch.WordTrace tailWord_201987 prefixEnd_201987 23048092657734768585241 := by
  unfold tailWord_201987
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367071119243070478292215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4911380746162046985528143 7367071119243070478292215)
  ·
    refine ⟨11050606678864605717438323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7367071119243070478292215 11050606678864605717438323)
    ·
      refine ⟨16575910018296908576157485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11050606678864605717438323 16575910018296908576157485)
      ·
        refine ⟨6215966256861340716059057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16575910018296908576157485 6215966256861340716059057)
        ·
          refine ⟨4661974692646005537044293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6215966256861340716059057 4661974692646005537044293)
          ·
            refine ⟨874120254871126038195805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4661974692646005537044293 874120254871126038195805)
            ·
              refine ⟨327795095576672264323427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874120254871126038195805 327795095576672264323427)
              ·
                refine ⟨491692643365008396485141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327795095576672264323427 491692643365008396485141)
                ·
                  refine ⟨23048092657734768585241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 491692643365008396485141 23048092657734768585241)
                  ·
                    rfl

theorem cell22_201987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 6].length) (baseStart_201987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_201987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_201987 prefixEnd_201987 := by exact prefixLift 201987
  have htrace : WordTrace (prefixWord ++ tailWord_201987) baseStart_201987 baseEnd_201987 := by
    simpa [prefixWord, tailWord_201987, baseEnd_201987] using wordTrace_append hprefix tailTrace_201987
  have hstable : (prefixWord ++ tailWord_201987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201987).length < 2 ^ (prefixWord ++ tailWord_201987).sum := by decide
  have hdescent : baseEnd_201987 < baseStart_201987 := by decide
  rcases family_descends (prefixWord ++ tailWord_201987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202034 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_202034 : Nat := 118140960795 + 202034 * 2 ^ 59
def prefixEnd_202034 : Nat := 4983230072969 + 3 ^ 40 * 202034 * 2
def baseEnd_202034 : Nat := 69160367033711849830579

theorem tailTrace_202034 : CollatzResearch.WordTrace tailWord_202034 prefixEnd_202034 69160367033711849830579 := by
  unfold tailWord_202034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842196337518199376313289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4912523566715198336835437 1842196337518199376313289)
  ·
    refine ⟨1381647253138649532234967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1842196337518199376313289 1381647253138649532234967)
    ·
      refine ⟨2072470879707974298352451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381647253138649532234967 2072470879707974298352451)
      ·
        refine ⟨3108706319561961447528677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072470879707974298352451 3108706319561961447528677)
        ·
          refine ⟨582882434917867771411627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3108706319561961447528677 582882434917867771411627)
          ·
            refine ⟨874323652376801657117441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582882434917867771411627 874323652376801657117441)
            ·
              refine ⟨655742739282601242838081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874323652376801657117441 655742739282601242838081)
              ·
                refine ⟨491807054461950932128561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655742739282601242838081 491807054461950932128561)
                ·
                  refine ⟨368855290846463199096421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491807054461950932128561 368855290846463199096421)
                  ·
                    refine ⟨69160367033711849830579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 368855290846463199096421 69160367033711849830579)
                    ·
                      rfl

theorem cell22_202034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_202034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202034 prefixEnd_202034 := by exact prefixLift 202034
  have htrace : WordTrace (prefixWord ++ tailWord_202034) baseStart_202034 baseEnd_202034 := by
    simpa [prefixWord, tailWord_202034, baseEnd_202034] using wordTrace_append hprefix tailTrace_202034
  have hstable : (prefixWord ++ tailWord_202034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202034).length < 2 ^ (prefixWord ++ tailWord_202034).sum := by decide
  have hdescent : baseEnd_202034 < baseStart_202034 := by decide
  rcases family_descends (prefixWord ++ tailWord_202034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202049 : List Nat := [1, 2, 5, 2, 1, 1, 3, 7]
def baseStart_202049 : Nat := 118140960795 + 202049 * 2 ^ 59
def prefixEnd_202049 : Nat := 4983230072969 + 3 ^ 40 * 202049 * 2
def baseEnd_202049 : Nat := 7685055760028534522837

theorem tailTrace_202049 : CollatzResearch.WordTrace tailWord_202049 prefixEnd_202049 7685055760028534522837 := by
  unfold tailWord_202049
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369332445018455067049201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4912888296678970044699467 7369332445018455067049201)
  ·
    refine ⟨5526999333763841300286901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7369332445018455067049201 5526999333763841300286901)
    ·
      refine ⟨518156187540360121901897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5526999333763841300286901 518156187540360121901897)
      ·
        refine ⟨388617140655270091426423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518156187540360121901897 388617140655270091426423)
        ·
          refine ⟨582925710982905137139635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388617140655270091426423 582925710982905137139635)
          ·
            refine ⟨874388566474357705709453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582925710982905137139635 874388566474357705709453)
            ·
              refine ⟨327895712427884139641045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874388566474357705709453 327895712427884139641045)
              ·
                refine ⟨7685055760028534522837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 327895712427884139641045 7685055760028534522837)
                ·
                  rfl

theorem cell22_202049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 7].length) (baseStart_202049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202049 prefixEnd_202049 := by exact prefixLift 202049
  have htrace : WordTrace (prefixWord ++ tailWord_202049) baseStart_202049 baseEnd_202049 := by
    simpa [prefixWord, tailWord_202049, baseEnd_202049] using wordTrace_append hprefix tailTrace_202049
  have hstable : (prefixWord ++ tailWord_202049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202049).length < 2 ^ (prefixWord ++ tailWord_202049).sum := by decide
  have hdescent : baseEnd_202049 < baseStart_202049 := by decide
  rcases family_descends (prefixWord ++ tailWord_202049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202062 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_202062 : Nat := 118140960795 + 202062 * 2 ^ 59
def prefixEnd_202062 : Nat := 4983230072969 + 3 ^ 40 * 202062 * 2
def baseEnd_202062 : Nat := 69169952005929110130493

theorem tailTrace_202062 : CollatzResearch.WordTrace tailWord_202062 prefixEnd_202062 69169952005929110130493 := by
  unfold tailWord_202062
  simp only [CollatzResearch.WordTrace]
  refine ⟨921225824246419785909055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4913204395980905524848293 921225824246419785909055)
  ·
    refine ⟨1381838736369629678863583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 921225824246419785909055 1381838736369629678863583)
    ·
      refine ⟨2072758104554444518295375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381838736369629678863583 2072758104554444518295375)
      ·
        refine ⟨3109137156831666777443063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072758104554444518295375 3109137156831666777443063)
        ·
          refine ⟨4663705735247500166164595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3109137156831666777443063 4663705735247500166164595)
          ·
            refine ⟨6995558602871250249246893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663705735247500166164595 6995558602871250249246893)
            ·
              refine ⟨2623334476076718843467585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6995558602871250249246893 2623334476076718843467585)
              ·
                refine ⟨1967500857057539132600689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623334476076718843467585 1967500857057539132600689)
                ·
                  refine ⟨1475625642793154349450517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967500857057539132600689 1475625642793154349450517)
                  ·
                    refine ⟨69169952005929110130493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1475625642793154349450517 69169952005929110130493)
                    ·
                      rfl

theorem cell22_202062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_202062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202062 prefixEnd_202062 := by exact prefixLift 202062
  have htrace : WordTrace (prefixWord ++ tailWord_202062) baseStart_202062 baseEnd_202062 := by
    simpa [prefixWord, tailWord_202062, baseEnd_202062] using wordTrace_append hprefix tailTrace_202062
  have hstable : (prefixWord ++ tailWord_202062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202062).length < 2 ^ (prefixWord ++ tailWord_202062).sum := by decide
  have hdescent : baseEnd_202062 < baseStart_202062 := by decide
  rcases family_descends (prefixWord ++ tailWord_202062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202064 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 3, 3]
def baseStart_202064 : Nat := 118140960795 + 202064 * 2 ^ 59
def prefixEnd_202064 : Nat := 4983230072969 + 3 ^ 40 * 202064 * 2
def baseEnd_202064 : Nat := 69170636646801771580487

theorem tailTrace_202064 : CollatzResearch.WordTrace tailWord_202064 prefixEnd_202064 69170636646801771580487 := by
  unfold tailWord_202064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3684939769982056314422623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4913253026642741752563497 3684939769982056314422623)
  ·
    refine ⟨5527409654973084471633935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3684939769982056314422623 5527409654973084471633935)
    ·
      refine ⟨8291114482459626707450903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527409654973084471633935 8291114482459626707450903)
      ·
        refine ⟨12436671723689440061176355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291114482459626707450903 12436671723689440061176355)
        ·
          refine ⟨18655007585534160091764533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12436671723689440061176355 18655007585534160091764533)
          ·
            refine ⟨1748906961143827508602925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18655007585534160091764533 1748906961143827508602925)
            ·
              refine ⟨655840110428935315726097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1748906961143827508602925 655840110428935315726097)
              ·
                refine ⟨491880082821701486794573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655840110428935315726097 491880082821701486794573)
                ·
                  refine ⟨184455031058138057547965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491880082821701486794573 184455031058138057547965)
                  ·
                    refine ⟨69170636646801771580487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184455031058138057547965 69170636646801771580487)
                    ·
                      rfl

theorem cell22_202064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_202064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202064 prefixEnd_202064 := by exact prefixLift 202064
  have htrace : WordTrace (prefixWord ++ tailWord_202064) baseStart_202064 baseEnd_202064 := by
    simpa [prefixWord, tailWord_202064, baseEnd_202064] using wordTrace_append hprefix tailTrace_202064
  have hstable : (prefixWord ++ tailWord_202064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202064).length < 2 ^ (prefixWord ++ tailWord_202064).sum := by decide
  have hdescent : baseEnd_202064 < baseStart_202064 := by decide
  rcases family_descends (prefixWord ++ tailWord_202064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202141 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_202141 : Nat := 118140960795 + 202141 * 2 ^ 59
def prefixEnd_202141 : Nat := 4983230072969 + 3 ^ 40 * 202141 * 2
def baseEnd_202141 : Nat := 69196995320399237405251

theorem tailTrace_202141 : CollatzResearch.WordTrace tailWord_202141 prefixEnd_202141 69196995320399237405251 := by
  unfold tailWord_202141
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372687960685154779398277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4915125307123436519598851 7372687960685154779398277)
  ·
    refine ⟨1382378992628466521137177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7372687960685154779398277 1382378992628466521137177)
    ·
      refine ⟨1036784244471349890852883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1382378992628466521137177 1036784244471349890852883)
      ·
        refine ⟨1555176366707024836279325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036784244471349890852883 1555176366707024836279325)
        ·
          refine ⟨583191137515134313604747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1555176366707024836279325 583191137515134313604747)
          ·
            refine ⟨874786706272701470407121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583191137515134313604747 874786706272701470407121)
            ·
              refine ⟨656090029704526102805341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874786706272701470407121 656090029704526102805341)
              ·
                refine ⟨246033761139197288552003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656090029704526102805341 246033761139197288552003)
                ·
                  refine ⟨369050641708795932828005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246033761139197288552003 369050641708795932828005)
                  ·
                    refine ⟨69196995320399237405251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369050641708795932828005 69196995320399237405251)
                    ·
                      rfl

theorem cell22_202141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_202141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202141 prefixEnd_202141 := by exact prefixLift 202141
  have htrace : WordTrace (prefixWord ++ tailWord_202141) baseStart_202141 baseEnd_202141 := by
    simpa [prefixWord, tailWord_202141, baseEnd_202141] using wordTrace_append hprefix tailTrace_202141
  have hstable : (prefixWord ++ tailWord_202141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202141).length < 2 ^ (prefixWord ++ tailWord_202141).sum := by decide
  have hdescent : baseEnd_202141 < baseStart_202141 := by decide
  rcases family_descends (prefixWord ++ tailWord_202141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202186 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_202186 : Nat := 118140960795 + 202186 * 2 ^ 59
def prefixEnd_202186 : Nat := 4983230072969 + 3 ^ 40 * 202186 * 2
def baseEnd_202186 : Nat := 69212399740034120030113

theorem tailTrace_202186 : CollatzResearch.WordTrace tailWord_202186 prefixEnd_202186 69212399740034120030113 := by
  unfold tailWord_202186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843582311380531866196603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4916219497014751643190941 1843582311380531866196603)
  ·
    refine ⟨2765373467070797799294905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1843582311380531866196603 2765373467070797799294905)
    ·
      refine ⟨2074030100303098349471179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2765373467070797799294905 2074030100303098349471179)
      ·
        refine ⟨3111045150454647524206769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074030100303098349471179 3111045150454647524206769)
        ·
          refine ⟨2333283862840985643155077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111045150454647524206769 2333283862840985643155077)
          ·
            refine ⟨437490724282684808091577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2333283862840985643155077 437490724282684808091577)
            ·
              refine ⟨328118043212013606068683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437490724282684808091577 328118043212013606068683)
              ·
                refine ⟨492177064818020409103025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328118043212013606068683 492177064818020409103025)
                ·
                  refine ⟨369132798613515306827269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492177064818020409103025 369132798613515306827269)
                  ·
                    refine ⟨69212399740034120030113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369132798613515306827269 69212399740034120030113)
                    ·
                      rfl

theorem cell22_202186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_202186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202186 prefixEnd_202186 := by exact prefixLift 202186
  have htrace : WordTrace (prefixWord ++ tailWord_202186) baseStart_202186 baseEnd_202186 := by
    simpa [prefixWord, tailWord_202186, baseEnd_202186] using wordTrace_append hprefix tailTrace_202186
  have hstable : (prefixWord ++ tailWord_202186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202186).length < 2 ^ (prefixWord ++ tailWord_202186).sum := by decide
  have hdescent : baseEnd_202186 < baseStart_202186 := by decide
  rcases family_descends (prefixWord ++ tailWord_202186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202216 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 3, 3]
def baseStart_202216 : Nat := 118140960795 + 202216 * 2 ^ 59
def prefixEnd_202216 : Nat := 4983230072969 + 3 ^ 40 * 202216 * 2
def baseEnd_202216 : Nat := 69222669353124041780021

theorem tailTrace_202216 : CollatzResearch.WordTrace tailWord_202216 prefixEnd_202216 69222669353124041780021 := by
  unfold tailWord_202216
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687711717706721294189251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4916948956942295058919001 3687711717706721294189251)
  ·
    refine ⟨5531567576560081941283877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3687711717706721294189251 5531567576560081941283877)
    ·
      refine ⟨1037168920605015363990727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5531567576560081941283877 1037168920605015363990727)
      ·
        refine ⟨1555753380907523045986091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037168920605015363990727 1555753380907523045986091)
        ·
          refine ⟨2333630071361284568979137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555753380907523045986091 2333630071361284568979137)
          ·
            refine ⟨1750222553520963426734353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2333630071361284568979137 1750222553520963426734353)
            ·
              refine ⟨1312666915140722570050765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750222553520963426734353 1312666915140722570050765)
              ·
                refine ⟨492250093177770963769037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1312666915140722570050765 492250093177770963769037)
                ·
                  refine ⟨184593784941664111413389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492250093177770963769037 184593784941664111413389)
                  ·
                    refine ⟨69222669353124041780021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184593784941664111413389 69222669353124041780021)
                    ·
                      rfl

theorem cell22_202216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_202216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202216 prefixEnd_202216 := by exact prefixLift 202216
  have htrace : WordTrace (prefixWord ++ tailWord_202216) baseStart_202216 baseEnd_202216 := by
    simpa [prefixWord, tailWord_202216, baseEnd_202216] using wordTrace_append hprefix tailTrace_202216
  have hstable : (prefixWord ++ tailWord_202216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202216).length < 2 ^ (prefixWord ++ tailWord_202216).sum := by decide
  have hdescent : baseEnd_202216 < baseStart_202216 := by decide
  rcases family_descends (prefixWord ++ tailWord_202216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202218 : List Nat := [3, 1, 3, 1, 5, 1, 1, 7]
def baseStart_202218 : Nat := 118140960795 + 202218 * 2 ^ 59
def prefixEnd_202218 : Nat := 4983230072969 + 3 ^ 40 * 202218 * 2
def baseEnd_202218 : Nat := 7691483777110744803335

theorem tailTrace_202218 : CollatzResearch.WordTrace tailWord_202218 prefixEnd_202218 7691483777110744803335 := by
  unfold tailWord_202218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843874095351549232487827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4916997587604131286634205 1843874095351549232487827)
  ·
    refine ⟨2765811143027323848731741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1843874095351549232487827 2765811143027323848731741)
    ·
      refine ⟨1037179178635246443274403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2765811143027323848731741 1037179178635246443274403)
      ·
        refine ⟨1555768767952869664911605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037179178635246443274403 1555768767952869664911605)
        ·
          refine ⟨145853321995581531085463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1555768767952869664911605 145853321995581531085463)
          ·
            refine ⟨218779982993372296628195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145853321995581531085463 218779982993372296628195)
            ·
              refine ⟨328169974490058444942293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218779982993372296628195 328169974490058444942293)
              ·
                refine ⟨7691483777110744803335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 328169974490058444942293 7691483777110744803335)
                ·
                  rfl

theorem cell22_202218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_202218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202218 prefixEnd_202218 := by exact prefixLift 202218
  have htrace : WordTrace (prefixWord ++ tailWord_202218) baseStart_202218 baseEnd_202218 := by
    simpa [prefixWord, tailWord_202218, baseEnd_202218] using wordTrace_append hprefix tailTrace_202218
  have hstable : (prefixWord ++ tailWord_202218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202218).length < 2 ^ (prefixWord ++ tailWord_202218).sum := by decide
  have hdescent : baseEnd_202218 < baseStart_202218 := by decide
  rcases family_descends (prefixWord ++ tailWord_202218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202250 : List Nat := [3, 1, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_202250 : Nat := 118140960795 + 202250 * 2 ^ 59
def prefixEnd_202250 : Nat := 4983230072969 + 3 ^ 40 * 202250 * 2
def baseEnd_202250 : Nat := 69234308247959286429917

theorem tailTrace_202250 : CollatzResearch.WordTrace tailWord_202250 prefixEnd_202250 69234308247959286429917 := by
  unfold tailWord_202250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844165879322566598779051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4917775678193510930077469 1844165879322566598779051)
  ·
    refine ⟨2766248818983849898168577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844165879322566598779051 2766248818983849898168577)
    ·
      refine ⟨2074686614237887423626433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2766248818983849898168577 2074686614237887423626433)
      ·
        refine ⟨1556014960678415567719825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2074686614237887423626433 1556014960678415567719825)
        ·
          refine ⟨1167011220508811675789869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1556014960678415567719825 1167011220508811675789869)
          ·
            refine ⟨437629207690804378421201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1167011220508811675789869 437629207690804378421201)
            ·
              refine ⟨328221905768103283815901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437629207690804378421201 328221905768103283815901)
              ·
                refine ⟨123083214663038731430963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328221905768103283815901 123083214663038731430963)
                ·
                  refine ⟨184624821994558097146445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123083214663038731430963 184624821994558097146445)
                  ·
                    refine ⟨69234308247959286429917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184624821994558097146445 69234308247959286429917)
                    ·
                      rfl

theorem cell22_202250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_202250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202250 prefixEnd_202250 := by exact prefixLift 202250
  have htrace : WordTrace (prefixWord ++ tailWord_202250) baseStart_202250 baseEnd_202250 := by
    simpa [prefixWord, tailWord_202250, baseEnd_202250] using wordTrace_append hprefix tailTrace_202250
  have hstable : (prefixWord ++ tailWord_202250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202250).length < 2 ^ (prefixWord ++ tailWord_202250).sum := by decide
  have hdescent : baseEnd_202250 < baseStart_202250 := by decide
  rcases family_descends (prefixWord ++ tailWord_202250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202280 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 5]
def baseStart_202280 : Nat := 118140960795 + 202280 * 2 ^ 59
def prefixEnd_202280 : Nat := 4983230072969 + 3 ^ 40 * 202280 * 2
def baseEnd_202280 : Nat := 23081525953683069393275

theorem tailTrace_202280 : CollatzResearch.WordTrace tailWord_202280 prefixEnd_202280 23081525953683069393275 := by
  unfold tailWord_202280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688878853590790759354147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4918505138121054345805529 3688878853590790759354147)
  ·
    refine ⟨5533318280386186139031221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3688878853590790759354147 5533318280386186139031221)
    ·
      refine ⟨518748588786204950534177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5533318280386186139031221 518748588786204950534177)
      ·
        refine ⟨389061441589653712900633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518748588786204950534177 389061441589653712900633)
        ·
          refine ⟨291796081192240284675475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389061441589653712900633 291796081192240284675475)
          ·
            refine ⟨437694121788360427013213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291796081192240284675475 437694121788360427013213)
            ·
              refine ⟨164135295670635160129955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 437694121788360427013213 164135295670635160129955)
              ·
                refine ⟨246202943505952740194933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164135295670635160129955 246202943505952740194933)
                ·
                  refine ⟨23081525953683069393275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246202943505952740194933 23081525953683069393275)
                  ·
                    rfl

theorem cell22_202280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_202280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202280 prefixEnd_202280 := by exact prefixLift 202280
  have htrace : WordTrace (prefixWord ++ tailWord_202280) baseStart_202280 baseEnd_202280 := by
    simpa [prefixWord, tailWord_202280, baseEnd_202280] using wordTrace_append hprefix tailTrace_202280
  have hstable : (prefixWord ++ tailWord_202280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202280).length < 2 ^ (prefixWord ++ tailWord_202280).sum := by decide
  have hdescent : baseEnd_202280 < baseStart_202280 := by decide
  rcases family_descends (prefixWord ++ tailWord_202280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202293 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_202293 : Nat := 118140960795 + 202293 * 2 ^ 59
def prefixEnd_202293 : Nat := 4983230072969 + 3 ^ 40 * 202293 * 2
def baseEnd_202293 : Nat := 69249028026721507604785

theorem tailTrace_202293 : CollatzResearch.WordTrace tailWord_202293 prefixEnd_202293 69249028026721507604785 := by
  unfold tailWord_202293
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378231856134484738931533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4918821237422989825954355 7378231856134484738931533)
  ·
    refine ⟨2766836946050431777099325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7378231856134484738931533 2766836946050431777099325)
    ·
      refine ⟨1037563854768911916412247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2766836946050431777099325 1037563854768911916412247)
      ·
        refine ⟨1556345782153367874618371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037563854768911916412247 1556345782153367874618371)
        ·
          refine ⟨2334518673230051811927557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556345782153367874618371 2334518673230051811927557)
          ·
            refine ⟨437722251230634714736417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2334518673230051811927557 437722251230634714736417)
            ·
              refine ⟨328291688422976036052313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437722251230634714736417 328291688422976036052313)
              ·
                refine ⟨246218766317232027039235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328291688422976036052313 246218766317232027039235)
                ·
                  refine ⟨369328149475848040558853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246218766317232027039235 369328149475848040558853)
                  ·
                    refine ⟨69249028026721507604785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369328149475848040558853 69249028026721507604785)
                    ·
                      rfl

theorem cell22_202293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_202293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202293 prefixEnd_202293 := by exact prefixLift 202293
  have htrace : WordTrace (prefixWord ++ tailWord_202293) baseStart_202293 baseEnd_202293 := by
    simpa [prefixWord, tailWord_202293, baseEnd_202293] using wordTrace_append hprefix tailTrace_202293
  have hstable : (prefixWord ++ tailWord_202293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202293).length < 2 ^ (prefixWord ++ tailWord_202293).sum := by decide
  have hdescent : baseEnd_202293 < baseStart_202293 := by decide
  rcases family_descends (prefixWord ++ tailWord_202293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202321 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_202321 : Nat := 118140960795 + 202321 * 2 ^ 59
def prefixEnd_202321 : Nat := 4983230072969 + 3 ^ 40 * 202321 * 2
def baseEnd_202321 : Nat := 69258612998938767904699

theorem tailTrace_202321 : CollatzResearch.WordTrace tailWord_202321 prefixEnd_202321 69258612998938767904699 := by
  unfold tailWord_202321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379253100033045520950817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4919502066688697013967211 7379253100033045520950817)
  ·
    refine ⟨5534439825024784140713113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7379253100033045520950817 5534439825024784140713113)
    ·
      refine ⟨4150829868768588105534835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5534439825024784140713113 4150829868768588105534835)
      ·
        refine ⟨6226244803152882158302253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4150829868768588105534835 6226244803152882158302253)
        ·
          refine ⟨2334841801182330809363345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6226244803152882158302253 2334841801182330809363345)
          ·
            refine ⟨1751131350886748107022509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334841801182330809363345 1751131350886748107022509)
            ·
              refine ⟨656674256582530540133441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1751131350886748107022509 656674256582530540133441)
              ·
                refine ⟨492505692436897905100081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656674256582530540133441 492505692436897905100081)
                ·
                  refine ⟨369379269327673428825061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492505692436897905100081 369379269327673428825061)
                  ·
                    refine ⟨69258612998938767904699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369379269327673428825061 69258612998938767904699)
                    ·
                      rfl

theorem cell22_202321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_202321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202321 prefixEnd_202321 := by exact prefixLift 202321
  have htrace : WordTrace (prefixWord ++ tailWord_202321) baseStart_202321 baseEnd_202321 := by
    simpa [prefixWord, tailWord_202321, baseEnd_202321] using wordTrace_append hprefix tailTrace_202321
  have hstable : (prefixWord ++ tailWord_202321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202321).length < 2 ^ (prefixWord ++ tailWord_202321).sum := by decide
  have hdescent : baseEnd_202321 < baseStart_202321 := by decide
  rcases family_descends (prefixWord ++ tailWord_202321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202340 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_202340 : Nat := 118140960795 + 202340 * 2 ^ 59
def prefixEnd_202340 : Nat := 4983230072969 + 3 ^ 40 * 202340 * 2
def baseEnd_202340 : Nat := 69265117087229051679641

theorem tailTrace_202340 : CollatzResearch.WordTrace tailWord_202340 prefixEnd_202340 69265117087229051679641 := by
  unfold tailWord_202340
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689973043482105882946237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4919964057976141177261649 3689973043482105882946237)
  ·
    refine ⟨1383739891305789706104839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3689973043482105882946237 1383739891305789706104839)
    ·
      refine ⟨2075609836958684559157259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1383739891305789706104839 2075609836958684559157259)
      ·
        refine ⟨3113414755438026838735889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075609836958684559157259 3113414755438026838735889)
        ·
          refine ⟨2335061066578520129051917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3113414755438026838735889 2335061066578520129051917)
          ·
            refine ⟨875647899966945048394469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2335061066578520129051917 875647899966945048394469)
            ·
              refine ⟨164183981243802196573963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 875647899966945048394469 164183981243802196573963)
              ·
                refine ⟨246275971865703294860945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164183981243802196573963 246275971865703294860945)
                ·
                  refine ⟨184706978899277471145709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246275971865703294860945 184706978899277471145709)
                  ·
                    refine ⟨69265117087229051679641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184706978899277471145709 69265117087229051679641)
                    ·
                      rfl

theorem cell22_202340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_202340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202340 prefixEnd_202340 := by exact prefixLift 202340
  have htrace : WordTrace (prefixWord ++ tailWord_202340) baseStart_202340 baseEnd_202340 := by
    simpa [prefixWord, tailWord_202340, baseEnd_202340] using wordTrace_append hprefix tailTrace_202340
  have hstable : (prefixWord ++ tailWord_202340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202340).length < 2 ^ (prefixWord ++ tailWord_202340).sum := by decide
  have hdescent : baseEnd_202340 < baseStart_202340 := by decide
  rcases family_descends (prefixWord ++ tailWord_202340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202351 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 5, 3]
def baseStart_202351 : Nat := 118140960795 + 202351 * 2 ^ 59
def prefixEnd_202351 : Nat := 4983230072969 + 3 ^ 40 * 202351 * 2
def baseEnd_202351 : Nat := 69268882612028689654607

theorem tailTrace_202351 : CollatzResearch.WordTrace tailWord_202351 prefixEnd_202351 69268882612028689654607 := by
  unfold tailWord_202351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7380347289924360644542907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4920231526616240429695271 7380347289924360644542907)
  ·
    refine ⟨11070520934886540966814361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7380347289924360644542907 11070520934886540966814361)
    ·
      refine ⟨8302890701164905725110771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11070520934886540966814361 8302890701164905725110771)
      ·
        refine ⟨12454336051747358587666157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8302890701164905725110771 12454336051747358587666157)
        ·
          refine ⟨4670376019405259470374809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12454336051747358587666157 4670376019405259470374809)
          ·
            refine ⟨3502782014553944602781107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670376019405259470374809 3502782014553944602781107)
            ·
              refine ⟨5254173021830916904171661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502782014553944602781107 5254173021830916904171661)
              ·
                refine ⟨1970314883186593839064373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5254173021830916904171661 1970314883186593839064373)
                ·
                  refine ⟨184717020298743172412285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1970314883186593839064373 184717020298743172412285)
                  ·
                    refine ⟨69268882612028689654607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184717020298743172412285 69268882612028689654607)
                    ·
                      rfl

theorem cell22_202351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_202351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202351 prefixEnd_202351 := by exact prefixLift 202351
  have htrace : WordTrace (prefixWord ++ tailWord_202351) baseStart_202351 baseEnd_202351 := by
    simpa [prefixWord, tailWord_202351, baseEnd_202351] using wordTrace_append hprefix tailTrace_202351
  have hstable : (prefixWord ++ tailWord_202351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202351).length < 2 ^ (prefixWord ++ tailWord_202351).sum := by decide
  have hdescent : baseEnd_202351 < baseStart_202351 := by decide
  rcases family_descends (prefixWord ++ tailWord_202351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202402 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_202402 : Nat := 118140960795 + 202402 * 2 ^ 59
def prefixEnd_202402 : Nat := 4983230072969 + 3 ^ 40 * 202402 * 2
def baseEnd_202402 : Nat := 69286340954281556629451

theorem tailTrace_202402 : CollatzResearch.WordTrace tailWord_202402 prefixEnd_202402 69286340954281556629451 := by
  unfold tailWord_202402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1845551853184899088662365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4921471608493064236432973 1845551853184899088662365)
  ·
    refine ⟨692081944944337158248387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1845551853184899088662365 692081944944337158248387)
    ·
      refine ⟨1038122917416505737372581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692081944944337158248387 1038122917416505737372581)
      ·
        refine ⟨194648047015594825757359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1038122917416505737372581 194648047015594825757359)
        ·
          refine ⟨291972070523392238636039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194648047015594825757359 291972070523392238636039)
          ·
            refine ⟨437958105785088357954059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291972070523392238636039 437958105785088357954059)
            ·
              refine ⟨656937158677632536931089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437958105785088357954059 656937158677632536931089)
              ·
                refine ⟨492702869008224402698317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656937158677632536931089 492702869008224402698317)
                ·
                  refine ⟨184763575878084151011869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492702869008224402698317 184763575878084151011869)
                  ·
                    refine ⟨69286340954281556629451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184763575878084151011869 69286340954281556629451)
                    ·
                      rfl

theorem cell22_202402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_202402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202402 prefixEnd_202402 := by exact prefixLift 202402
  have htrace : WordTrace (prefixWord ++ tailWord_202402) baseStart_202402 baseEnd_202402 := by
    simpa [prefixWord, tailWord_202402, baseEnd_202402] using wordTrace_append hprefix tailTrace_202402
  have hstable : (prefixWord ++ tailWord_202402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202402).length < 2 ^ (prefixWord ++ tailWord_202402).sum := by decide
  have hdescent : baseEnd_202402 < baseStart_202402 := by decide
  rcases family_descends (prefixWord ++ tailWord_202402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202456 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_202456 : Nat := 118140960795 + 202456 * 2 ^ 59
def prefixEnd_202456 : Nat := 4983230072969 + 3 ^ 40 * 202456 * 2
def baseEnd_202456 : Nat := 69304826257843415779285

theorem tailTrace_202456 : CollatzResearch.WordTrace tailWord_202456 prefixEnd_202456 69304826257843415779285 := by
  unfold tailWord_202456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692088477271981788557611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4922784636362642384743481 3692088477271981788557611)
  ·
    refine ⟨5538132715907972682836417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3692088477271981788557611 5538132715907972682836417)
    ·
      refine ⟨4153599536930979512127313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5538132715907972682836417 4153599536930979512127313)
      ·
        refine ⟨3115199652698234634095485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153599536930979512127313 3115199652698234634095485)
        ·
          refine ⟨1168199869761837987785807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3115199652698234634095485 1168199869761837987785807)
          ·
            refine ⟨1752299804642756981678711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168199869761837987785807 1752299804642756981678711)
            ·
              refine ⟨2628449706964135472518067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752299804642756981678711 2628449706964135472518067)
              ·
                refine ⟨3942674560446203208777101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628449706964135472518067 3942674560446203208777101)
                ·
                  refine ⟨1478502960167326203291413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3942674560446203208777101 1478502960167326203291413)
                  ·
                    refine ⟨69304826257843415779285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1478502960167326203291413 69304826257843415779285)
                    ·
                      rfl

theorem cell22_202456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_202456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202456 prefixEnd_202456 := by exact prefixLift 202456
  have htrace : WordTrace (prefixWord ++ tailWord_202456) baseStart_202456 baseEnd_202456 := by
    simpa [prefixWord, tailWord_202456, baseEnd_202456] using wordTrace_append hprefix tailTrace_202456
  have hstable : (prefixWord ++ tailWord_202456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202456).length < 2 ^ (prefixWord ++ tailWord_202456).sum := by decide
  have hdescent : baseEnd_202456 < baseStart_202456 := by decide
  rcases family_descends (prefixWord ++ tailWord_202456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202458 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_202458 : Nat := 118140960795 + 202458 * 2 ^ 59
def prefixEnd_202458 : Nat := 4983230072969 + 3 ^ 40 * 202458 * 2
def baseEnd_202458 : Nat := 69305510898716077229279

theorem tailTrace_202458 : CollatzResearch.WordTrace tailWord_202458 prefixEnd_202458 69305510898716077229279 := by
  unfold tailWord_202458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846062475134179479672007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4922833267024478612458685 1846062475134179479672007)
  ·
    refine ⟨2769093712701269219508011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1846062475134179479672007 2769093712701269219508011)
    ·
      refine ⟨4153640569051903829262017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769093712701269219508011 4153640569051903829262017)
      ·
        refine ⟨3115230426788927871946513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153640569051903829262017 3115230426788927871946513)
        ·
          refine ⟨2336422820091695903959885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3115230426788927871946513 2336422820091695903959885)
          ·
            refine ⟨876158557534385963984957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2336422820091695903959885 876158557534385963984957)
            ·
              refine ⟨328559459075394736494359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876158557534385963984957 328559459075394736494359)
              ·
                refine ⟨492839188613092104741539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328559459075394736494359 492839188613092104741539)
                ·
                  refine ⟨739258782919638157112309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492839188613092104741539 739258782919638157112309)
                  ·
                    refine ⟨69305510898716077229279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 739258782919638157112309 69305510898716077229279)
                    ·
                      rfl

theorem cell22_202458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_202458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202458 prefixEnd_202458 := by exact prefixLift 202458
  have htrace : WordTrace (prefixWord ++ tailWord_202458) baseStart_202458 baseEnd_202458 := by
    simpa [prefixWord, tailWord_202458, baseEnd_202458] using wordTrace_append hprefix tailTrace_202458
  have hstable : (prefixWord ++ tailWord_202458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202458).length < 2 ^ (prefixWord ++ tailWord_202458).sum := by decide
  have hdescent : baseEnd_202458 < baseStart_202458 := by decide
  rcases family_descends (prefixWord ++ tailWord_202458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202477 : List Nat := [1, 5, 1, 2, 1, 4, 1, 3, 4]
def baseStart_202477 : Nat := 118140960795 + 202477 * 2 ^ 59
def prefixEnd_202477 : Nat := 4983230072969 + 3 ^ 40 * 202477 * 2
def baseEnd_202477 : Nat := 23104004995668787001407

theorem tailTrace_202477 : CollatzResearch.WordTrace tailWord_202477 prefixEnd_202477 23104004995668787001407 := by
  unfold tailWord_202477
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384942887467884163629685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4923295258311922775753123 7384942887467884163629685)
  ·
    refine ⟨692338395700114140340283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7384942887467884163629685 692338395700114140340283)
    ·
      refine ⟨1038507593550171210510425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692338395700114140340283 1038507593550171210510425)
      ·
        refine ⟨778880695162628407882819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1038507593550171210510425 778880695162628407882819)
        ·
          refine ⟨1168321042743942611824229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778880695162628407882819 1168321042743942611824229)
          ·
            refine ⟨219060195514489239717043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1168321042743942611824229 219060195514489239717043)
            ·
              refine ⟨328590293271733859575565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219060195514489239717043 328590293271733859575565)
              ·
                refine ⟨123221359976900197340837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328590293271733859575565 123221359976900197340837)
                ·
                  refine ⟨23104004995668787001407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123221359976900197340837 23104004995668787001407)
                  ·
                    rfl

theorem cell22_202477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_202477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202477 prefixEnd_202477 := by exact prefixLift 202477
  have htrace : WordTrace (prefixWord ++ tailWord_202477) baseStart_202477 baseEnd_202477 := by
    simpa [prefixWord, tailWord_202477, baseEnd_202477] using wordTrace_append hprefix tailTrace_202477
  have hstable : (prefixWord ++ tailWord_202477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202477).length < 2 ^ (prefixWord ++ tailWord_202477).sum := by decide
  have hdescent : baseEnd_202477 < baseStart_202477 := by decide
  rcases family_descends (prefixWord ++ tailWord_202477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202494 : List Nat := [4, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_202494 : Nat := 118140960795 + 202494 * 2 ^ 59
def prefixEnd_202494 : Nat := 4983230072969 + 3 ^ 40 * 202494 * 2
def baseEnd_202494 : Nat := 23105944811474661109723

theorem tailTrace_202494 : CollatzResearch.WordTrace tailWord_202494 prefixEnd_202494 23105944811474661109723 := by
  unfold tailWord_202494
  simp only [CollatzResearch.WordTrace]
  refine ⟨923195366050787008374817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4923708618937530711332357 923195366050787008374817)
  ·
    refine ⟨692396524538090256281113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 923195366050787008374817 692396524538090256281113)
    ·
      refine ⟨519297393403567692210835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 692396524538090256281113 519297393403567692210835)
      ·
        refine ⟨778946090105351538316253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519297393403567692210835 778946090105351538316253)
        ·
          refine ⟨292104783789506826868595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 778946090105351538316253 292104783789506826868595)
          ·
            refine ⟨438157175684260240302893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292104783789506826868595 438157175684260240302893)
            ·
              refine ⟨164308940881597590113585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438157175684260240302893 164308940881597590113585)
              ·
                refine ⟨123231705661198192585189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164308940881597590113585 123231705661198192585189)
                ·
                  refine ⟨23105944811474661109723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123231705661198192585189 23105944811474661109723)
                  ·
                    rfl

theorem cell22_202494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_202494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202494 prefixEnd_202494 := by exact prefixLift 202494
  have htrace : WordTrace (prefixWord ++ tailWord_202494) baseStart_202494 baseEnd_202494 := by
    simpa [prefixWord, tailWord_202494, baseEnd_202494] using wordTrace_append hprefix tailTrace_202494
  have hstable : (prefixWord ++ tailWord_202494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202494).length < 2 ^ (prefixWord ++ tailWord_202494).sum := by decide
  have hdescent : baseEnd_202494 < baseStart_202494 := by decide
  rcases family_descends (prefixWord ++ tailWord_202494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202554 : List Nat := [3, 1, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_202554 : Nat := 118140960795 + 202554 * 2 ^ 59
def prefixEnd_202554 : Nat := 4983230072969 + 3 ^ 40 * 202554 * 2
def baseEnd_202554 : Nat := 69338373660603826828985

theorem tailTrace_202554 : CollatzResearch.WordTrace tailWord_202554 prefixEnd_202554 69338373660603826828985 := by
  unfold tailWord_202554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846937827047231578545679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4925167538792617542788477 1846937827047231578545679)
  ·
    refine ⟨2770406740570847367818519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1846937827047231578545679 2770406740570847367818519)
    ·
      refine ⟨4155610110856271051727779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2770406740570847367818519 4155610110856271051727779)
      ·
        refine ⟨6233415166284406577591669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155610110856271051727779 6233415166284406577591669)
        ·
          refine ⟨584382671839163116649219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6233415166284406577591669 584382671839163116649219)
          ·
            refine ⟨876574007758744674973829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584382671839163116649219 876574007758744674973829)
            ·
              refine ⟨164357626454764626557593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 876574007758744674973829 164357626454764626557593)
              ·
                refine ⟨123268219841073469918195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164357626454764626557593 123268219841073469918195)
                ·
                  refine ⟨184902329761610204877293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123268219841073469918195 184902329761610204877293)
                  ·
                    refine ⟨69338373660603826828985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184902329761610204877293 69338373660603826828985)
                    ·
                      rfl

theorem cell22_202554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_202554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202554 prefixEnd_202554 := by exact prefixLift 202554
  have htrace : WordTrace (prefixWord ++ tailWord_202554) baseStart_202554 baseEnd_202554 := by
    simpa [prefixWord, tailWord_202554, baseEnd_202554] using wordTrace_append hprefix tailTrace_202554
  have hstable : (prefixWord ++ tailWord_202554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202554).length < 2 ^ (prefixWord ++ tailWord_202554).sum := by decide
  have hdescent : baseEnd_202554 < baseStart_202554 := by decide
  rcases family_descends (prefixWord ++ tailWord_202554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202563 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 3, 4]
def baseStart_202563 : Nat := 118140960795 + 202563 * 2 ^ 59
def prefixEnd_202563 : Nat := 4983230072969 + 3 ^ 40 * 202563 * 2
def baseEnd_202563 : Nat := 69341454544530803353957

theorem tailTrace_202563 : CollatzResearch.WordTrace tailWord_202563 prefixEnd_202563 69341454544530803353957 := by
  unfold tailWord_202563
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388079565156320851260343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4925386376770880567506895 7388079565156320851260343)
  ·
    refine ⟨11082119347734481276890515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7388079565156320851260343 11082119347734481276890515)
    ·
      refine ⟨16623179021601721915335773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082119347734481276890515 16623179021601721915335773)
      ·
        refine ⟨6233692133100645718250915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16623179021601721915335773 6233692133100645718250915)
        ·
          refine ⟨9350538199650968577376373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233692133100645718250915 9350538199650968577376373)
          ·
            refine ⟨876612956217278304129035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9350538199650968577376373 876612956217278304129035)
            ·
              refine ⟨1314919434325917456193553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876612956217278304129035 1314919434325917456193553)
              ·
                refine ⟨986189575744438092145165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314919434325917456193553 986189575744438092145165)
                ·
                  refine ⟨369821090904164284554437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986189575744438092145165 369821090904164284554437)
                  ·
                    refine ⟨69341454544530803353957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369821090904164284554437 69341454544530803353957)
                    ·
                      rfl

theorem cell22_202563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_202563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202563 prefixEnd_202563 := by exact prefixLift 202563
  have htrace : WordTrace (prefixWord ++ tailWord_202563) baseStart_202563 baseEnd_202563 := by
    simpa [prefixWord, tailWord_202563, baseEnd_202563] using wordTrace_append hprefix tailTrace_202563
  have hstable : (prefixWord ++ tailWord_202563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202563).length < 2 ^ (prefixWord ++ tailWord_202563).sum := by decide
  have hdescent : baseEnd_202563 < baseStart_202563 := by decide
  rcases family_descends (prefixWord ++ tailWord_202563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202578 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_202578 : Nat := 118140960795 + 202578 * 2 ^ 59
def prefixEnd_202578 : Nat := 4983230072969 + 3 ^ 40 * 202578 * 2
def baseEnd_202578 : Nat := 23115529783691921409637

theorem tailTrace_202578 : CollatzResearch.WordTrace tailWord_202578 prefixEnd_202578 23115529783691921409637 := by
  unfold tailWord_202578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847156665025494603264097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4925751106734652275370925 1847156665025494603264097)
  ·
    refine ⟨1385367498769120952448073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1847156665025494603264097 1385367498769120952448073)
    ·
      refine ⟨1039025624076840714336055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1385367498769120952448073 1039025624076840714336055)
      ·
        refine ⟨1558538436115261071504083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039025624076840714336055 1558538436115261071504083)
        ·
          refine ⟨2337807654172891607256125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558538436115261071504083 2337807654172891607256125)
          ·
            refine ⟨876677870314834352721047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2337807654172891607256125 876677870314834352721047)
            ·
              refine ⟨1315016805472251529081571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876677870314834352721047 1315016805472251529081571)
              ·
                refine ⟨1972525208208377293622357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315016805472251529081571 1972525208208377293622357)
                ·
                  refine ⟨23115529783691921409637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1972525208208377293622357 23115529783691921409637)
                  ·
                    rfl

theorem cell22_202578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_202578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202578 prefixEnd_202578 := by exact prefixLift 202578
  have htrace : WordTrace (prefixWord ++ tailWord_202578) baseStart_202578 baseEnd_202578 := by
    simpa [prefixWord, tailWord_202578, baseEnd_202578] using wordTrace_append hprefix tailTrace_202578
  have hstable : (prefixWord ++ tailWord_202578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202578).length < 2 ^ (prefixWord ++ tailWord_202578).sum := by decide
  have hdescent : baseEnd_202578 < baseStart_202578 := by decide
  rcases family_descends (prefixWord ++ tailWord_202578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202580 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_202580 : Nat := 118140960795 + 202580 * 2 ^ 59
def prefixEnd_202580 : Nat := 4983230072969 + 3 ^ 40 * 202580 * 2
def baseEnd_202580 : Nat := 69347273991948425678905

theorem tailTrace_202580 : CollatzResearch.WordTrace tailWord_202580 prefixEnd_202580 69347273991948425678905 := by
  unfold tailWord_202580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694349803047366377314597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4925799737396488503086129 3694349803047366377314597)
  ·
    refine ⟨692690588071381195746487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3694349803047366377314597 692690588071381195746487)
    ·
      refine ⟨1039035882107071793619731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692690588071381195746487 1039035882107071793619731)
      ·
        refine ⟨1558553823160607690429597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039035882107071793619731 1558553823160607690429597)
        ·
          refine ⟨584457683685227883911099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1558553823160607690429597 584457683685227883911099)
          ·
            refine ⟨876686525527841825866649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584457683685227883911099 876686525527841825866649)
            ·
              refine ⟨657514894145881369399987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876686525527841825866649 657514894145881369399987)
              ·
                refine ⟨986272341218822054099981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657514894145881369399987 986272341218822054099981)
                ·
                  refine ⟨369852127957058270287493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986272341218822054099981 369852127957058270287493)
                  ·
                    refine ⟨69347273991948425678905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369852127957058270287493 69347273991948425678905)
                    ·
                      rfl

theorem cell22_202580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_202580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202580 prefixEnd_202580 := by exact prefixLift 202580
  have htrace : WordTrace (prefixWord ++ tailWord_202580) baseStart_202580 baseEnd_202580 := by
    simpa [prefixWord, tailWord_202580, baseEnd_202580] using wordTrace_append hprefix tailTrace_202580
  have hstable : (prefixWord ++ tailWord_202580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202580).length < 2 ^ (prefixWord ++ tailWord_202580).sum := by decide
  have hdescent : baseEnd_202580 < baseStart_202580 := by decide
  rcases family_descends (prefixWord ++ tailWord_202580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202593 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_202593 : Nat := 118140960795 + 202593 * 2 ^ 59
def prefixEnd_202593 : Nat := 4983230072969 + 3 ^ 40 * 202593 * 2
def baseEnd_202593 : Nat := 69351724157620725103865

theorem tailTrace_202593 : CollatzResearch.WordTrace tailWord_202593 prefixEnd_202593 69351724157620725103865 := by
  unfold tailWord_202593
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389173755047635974852433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4926115836698423983234955 7389173755047635974852433)
  ·
    refine ⟨5541880316285726981139325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7389173755047635974852433 5541880316285726981139325)
    ·
      refine ⟨2078205118607147617927247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5541880316285726981139325 2078205118607147617927247)
      ·
        refine ⟨3117307677910721426890871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078205118607147617927247 3117307677910721426890871)
        ·
          refine ⟨4675961516866082140336307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117307677910721426890871 4675961516866082140336307)
          ·
            refine ⟨7013942275299123210504461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4675961516866082140336307 7013942275299123210504461)
            ·
              refine ⟨2630228353237171203939173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7013942275299123210504461 2630228353237171203939173)
              ·
                refine ⟨493167816231969600738595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2630228353237171203939173 493167816231969600738595)
                ·
                  refine ⟨739751724347954401107893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493167816231969600738595 739751724347954401107893)
                  ·
                    refine ⟨69351724157620725103865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 739751724347954401107893 69351724157620725103865)
                    ·
                      rfl

theorem cell22_202593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_202593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202593 prefixEnd_202593 := by exact prefixLift 202593
  have htrace : WordTrace (prefixWord ++ tailWord_202593) baseStart_202593 baseEnd_202593 := by
    simpa [prefixWord, tailWord_202593, baseEnd_202593] using wordTrace_append hprefix tailTrace_202593
  have hstable : (prefixWord ++ tailWord_202593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202593).length < 2 ^ (prefixWord ++ tailWord_202593).sum := by decide
  have hdescent : baseEnd_202593 < baseStart_202593 := by decide
  rcases family_descends (prefixWord ++ tailWord_202593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202608 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_202608 : Nat := 118140960795 + 202608 * 2 ^ 59
def prefixEnd_202608 : Nat := 4983230072969 + 3 ^ 40 * 202608 * 2
def baseEnd_202608 : Nat := 69356858964165685978819

theorem tailTrace_202608 : CollatzResearch.WordTrace tailWord_202608 prefixEnd_202608 69356858964165685978819 := by
  unfold tailWord_202608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694860424996646768324239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4926480566662195691098985 3694860424996646768324239)
  ·
    refine ⟨5542290637494970152486359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3694860424996646768324239 5542290637494970152486359)
    ·
      refine ⟨8313435956242455228729539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5542290637494970152486359 8313435956242455228729539)
      ·
        refine ⟨12470153934363682843094309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8313435956242455228729539 12470153934363682843094309)
        ·
          refine ⟨2338153862693190533080183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12470153934363682843094309 2338153862693190533080183)
          ·
            refine ⟨3507230794039785799620275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338153862693190533080183 3507230794039785799620275)
            ·
              refine ⟨5260846191059678699430413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507230794039785799620275 5260846191059678699430413)
              ·
                refine ⟨1972817321647379512286405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5260846191059678699430413 1972817321647379512286405)
                ·
                  refine ⟨369903247808883658553701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972817321647379512286405 369903247808883658553701)
                  ·
                    refine ⟨69356858964165685978819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369903247808883658553701 69356858964165685978819)
                    ·
                      rfl

theorem cell22_202608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_202608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202608 prefixEnd_202608 := by exact prefixLift 202608
  have htrace : WordTrace (prefixWord ++ tailWord_202608) baseStart_202608 baseEnd_202608 := by
    simpa [prefixWord, tailWord_202608, baseEnd_202608] using wordTrace_append hprefix tailTrace_202608
  have hstable : (prefixWord ++ tailWord_202608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202608).length < 2 ^ (prefixWord ++ tailWord_202608).sum := by decide
  have hdescent : baseEnd_202608 < baseStart_202608 := by decide
  rcases family_descends (prefixWord ++ tailWord_202608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202657 : List Nat := [1, 2, 3, 4, 3, 1, 8]
def baseStart_202657 : Nat := 118140960795 + 202657 * 2 ^ 59
def prefixEnd_202657 : Nat := 4983230072969 + 3 ^ 40 * 202657 * 2
def baseEnd_202657 : Nat := 2569393802427625611247

theorem tailTrace_202657 : CollatzResearch.WordTrace tailWord_202657 prefixEnd_202657 2569393802427625611247 := by
  unfold tailWord_202657
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391508026815774905182225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4927672017877183270121483 7391508026815774905182225)
  ·
    refine ⟨5543631020111831178886669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7391508026815774905182225 5543631020111831178886669)
    ·
      refine ⟨2078861632541936692082501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5543631020111831178886669 2078861632541936692082501)
      ·
        refine ⟨389786556101613129765469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2078861632541936692082501 389786556101613129765469)
        ·
          refine ⟨146169958538104923662051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389786556101613129765469 146169958538104923662051)
          ·
            refine ⟨219254937807157385493077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146169958538104923662051 219254937807157385493077)
            ·
              refine ⟨2569393802427625611247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 219254937807157385493077 2569393802427625611247)
              ·
                rfl

theorem cell22_202657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 8].length) (baseStart_202657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202657 prefixEnd_202657 := by exact prefixLift 202657
  have htrace : WordTrace (prefixWord ++ tailWord_202657) baseStart_202657 baseEnd_202657 := by
    simpa [prefixWord, tailWord_202657, baseEnd_202657] using wordTrace_append hprefix tailTrace_202657
  have hstable : (prefixWord ++ tailWord_202657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202657).length < 2 ^ (prefixWord ++ tailWord_202657).sum := by decide
  have hdescent : baseEnd_202657 < baseStart_202657 := by decide
  rcases family_descends (prefixWord ++ tailWord_202657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202730 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_202730 : Nat := 118140960795 + 202730 * 2 ^ 59
def prefixEnd_202730 : Nat := 4983230072969 + 3 ^ 40 * 202730 * 2
def baseEnd_202730 : Nat := 23132874019132678142815

theorem tailTrace_202730 : CollatzResearch.WordTrace tailWord_202730 prefixEnd_202730 23132874019132678142815 := by
  unfold tailWord_202730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848542638887827093147411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4929447037034205581726429 1848542638887827093147411)
  ·
    refine ⟨2772813958331740639721117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1848542638887827093147411 2772813958331740639721117)
    ·
      refine ⟨1039805234374402739895419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2772813958331740639721117 1039805234374402739895419)
      ·
        refine ⟨1559707851561604109843129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039805234374402739895419 1559707851561604109843129)
        ·
          refine ⟨1169780888671203082382347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559707851561604109843129 1169780888671203082382347)
          ·
            refine ⟨1754671333006804623573521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169780888671203082382347 1754671333006804623573521)
            ·
              refine ⟨1316003499755103467680141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754671333006804623573521 1316003499755103467680141)
              ·
                refine ⟨493501312408163800380053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1316003499755103467680141 493501312408163800380053)
                ·
                  refine ⟨23132874019132678142815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 493501312408163800380053 23132874019132678142815)
                  ·
                    rfl

theorem cell22_202730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_202730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202730 prefixEnd_202730 := by exact prefixLift 202730
  have htrace : WordTrace (prefixWord ++ tailWord_202730) baseStart_202730 baseEnd_202730 := by
    simpa [prefixWord, tailWord_202730, baseEnd_202730] using wordTrace_append hprefix tailTrace_202730
  have hstable : (prefixWord ++ tailWord_202730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202730).length < 2 ^ (prefixWord ++ tailWord_202730).sum := by decide
  have hdescent : baseEnd_202730 < baseStart_202730 := by decide
  rcases family_descends (prefixWord ++ tailWord_202730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202745 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_202745 : Nat := 118140960795 + 202745 * 2 ^ 59
def prefixEnd_202745 : Nat := 4983230072969 + 3 ^ 40 * 202745 * 2
def baseEnd_202745 : Nat := 69403756863942995303399

theorem tailTrace_202745 : CollatzResearch.WordTrace tailWord_202745 prefixEnd_202745 69403756863942995303399 := by
  unfold tailWord_202745
  simp only [CollatzResearch.WordTrace]
  refine ⟨7394717650496965934385689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4929811766997977289590459 7394717650496965934385689)
  ·
    refine ⟨5546038237872724450789267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7394717650496965934385689 5546038237872724450789267)
    ·
      refine ⟨8319057356809086676183901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5546038237872724450789267 8319057356809086676183901)
      ·
        refine ⟨3119646508803407503568963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8319057356809086676183901 3119646508803407503568963)
        ·
          refine ⟨4679469763205111255353445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119646508803407503568963 4679469763205111255353445)
          ·
            refine ⟨877400580600958360378771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4679469763205111255353445 877400580600958360378771)
            ·
              refine ⟨1316100870901437540568157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877400580600958360378771 1316100870901437540568157)
              ·
                refine ⟨493537826588039077713059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1316100870901437540568157 493537826588039077713059)
                ·
                  refine ⟨740306739882058616569589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493537826588039077713059 740306739882058616569589)
                  ·
                    refine ⟨69403756863942995303399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 740306739882058616569589 69403756863942995303399)
                    ·
                      rfl

theorem cell22_202745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_202745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202745 prefixEnd_202745 := by exact prefixLift 202745
  have htrace : WordTrace (prefixWord ++ tailWord_202745) baseStart_202745 baseEnd_202745 := by
    simpa [prefixWord, tailWord_202745, baseEnd_202745] using wordTrace_append hprefix tailTrace_202745
  have hstable : (prefixWord ++ tailWord_202745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202745).length < 2 ^ (prefixWord ++ tailWord_202745).sum := by decide
  have hdescent : baseEnd_202745 < baseStart_202745 := by decide
  rcases family_descends (prefixWord ++ tailWord_202745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202760 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_202760 : Nat := 118140960795 + 202760 * 2 ^ 59
def prefixEnd_202760 : Nat := 4983230072969 + 3 ^ 40 * 202760 * 2
def baseEnd_202760 : Nat := 69408891670487956178353

theorem tailTrace_202760 : CollatzResearch.WordTrace tailWord_202760 prefixEnd_202760 69408891670487956178353 := by
  unfold tailWord_202760
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697632372721311748090867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4930176496961748997454489 3697632372721311748090867)
  ·
    refine ⟨5546448559081967622136301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3697632372721311748090867 5546448559081967622136301)
    ·
      refine ⟨2079918209655737858301113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5546448559081967622136301 2079918209655737858301113)
      ·
        refine ⟨1559938657241803393725835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2079918209655737858301113 1559938657241803393725835)
        ·
          refine ⟨2339907985862705090588753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559938657241803393725835 2339907985862705090588753)
          ·
            refine ⟨1754930989397028817941565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2339907985862705090588753 1754930989397028817941565)
            ·
              refine ⟨658099121023885806728087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1754930989397028817941565 658099121023885806728087)
              ·
                refine ⟨987148681535828710092131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658099121023885806728087 987148681535828710092131)
                ·
                  refine ⟨1480723022303743065138197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987148681535828710092131 1480723022303743065138197)
                  ·
                    refine ⟨69408891670487956178353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1480723022303743065138197 69408891670487956178353)
                    ·
                      rfl

theorem cell22_202760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_202760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202760 prefixEnd_202760 := by exact prefixLift 202760
  have htrace : WordTrace (prefixWord ++ tailWord_202760) baseStart_202760 baseEnd_202760 := by
    simpa [prefixWord, tailWord_202760, baseEnd_202760] using wordTrace_append hprefix tailTrace_202760
  have hstable : (prefixWord ++ tailWord_202760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202760).length < 2 ^ (prefixWord ++ tailWord_202760).sum := by decide
  have hdescent : baseEnd_202760 < baseStart_202760 := by decide
  rcases family_descends (prefixWord ++ tailWord_202760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202805 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_202805 : Nat := 118140960795 + 202805 * 2 ^ 59
def prefixEnd_202805 : Nat := 4983230072969 + 3 ^ 40 * 202805 * 2
def baseEnd_202805 : Nat := 69424296090122838803215

theorem tailTrace_202805 : CollatzResearch.WordTrace tailWord_202805 prefixEnd_202805 69424296090122838803215 := by
  unfold tailWord_202805
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396906030279596181569869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4931270686853064121046579 7396906030279596181569869)
  ·
    refine ⟨2773839761354848568088701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7396906030279596181569869 2773839761354848568088701)
    ·
      refine ⟨1040189910508068213033263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2773839761354848568088701 1040189910508068213033263)
      ·
        refine ⟨1560284865762102319549895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040189910508068213033263 1560284865762102319549895)
        ·
          refine ⟨2340427298643153479324843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560284865762102319549895 2340427298643153479324843)
          ·
            refine ⟨3510640947964730218987265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340427298643153479324843 3510640947964730218987265)
            ·
              refine ⟨2632980710973547664240449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3510640947964730218987265 2632980710973547664240449)
              ·
                refine ⟨1974735533230160748180337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632980710973547664240449 1974735533230160748180337)
                ·
                  refine ⟨1481051649922620561135253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974735533230160748180337 1481051649922620561135253)
                  ·
                    refine ⟨69424296090122838803215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1481051649922620561135253 69424296090122838803215)
                    ·
                      rfl

theorem cell22_202805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_202805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202805 prefixEnd_202805 := by exact prefixLift 202805
  have htrace : WordTrace (prefixWord ++ tailWord_202805) baseStart_202805 baseEnd_202805 := by
    simpa [prefixWord, tailWord_202805, baseEnd_202805] using wordTrace_append hprefix tailTrace_202805
  have hstable : (prefixWord ++ tailWord_202805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202805).length < 2 ^ (prefixWord ++ tailWord_202805).sum := by decide
  have hdescent : baseEnd_202805 < baseStart_202805 := by decide
  rcases family_descends (prefixWord ++ tailWord_202805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202807 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 3, 3]
def baseStart_202807 : Nat := 118140960795 + 202807 * 2 ^ 59
def prefixEnd_202807 : Nat := 4983230072969 + 3 ^ 40 * 202807 * 2
def baseEnd_202807 : Nat := 69424980730995500253209

theorem tailTrace_202807 : CollatzResearch.WordTrace tailWord_202807 prefixEnd_202807 69424980730995500253209 := by
  unfold tailWord_202807
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396978976272350523142675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4931319317514900348761783 7396978976272350523142675)
  ·
    refine ⟨11095468464408525784714013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7396978976272350523142675 11095468464408525784714013)
    ·
      refine ⟨4160800674153197169267755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11095468464408525784714013 4160800674153197169267755)
      ·
        refine ⟨6241201011229795753901633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160800674153197169267755 6241201011229795753901633)
        ·
          refine ⟨4680900758422346815426225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6241201011229795753901633 4680900758422346815426225)
          ·
            refine ⟨3510675568816760111569669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4680900758422346815426225 3510675568816760111569669)
            ·
              refine ⟨658251669153142520919313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3510675568816760111569669 658251669153142520919313)
              ·
                refine ⟨493688751864856890689485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658251669153142520919313 493688751864856890689485)
                ·
                  refine ⟨185133281949321334008557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493688751864856890689485 185133281949321334008557)
                  ·
                    refine ⟨69424980730995500253209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185133281949321334008557 69424980730995500253209)
                    ·
                      rfl

theorem cell22_202807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_202807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202807 prefixEnd_202807 := by exact prefixLift 202807
  have htrace : WordTrace (prefixWord ++ tailWord_202807) baseStart_202807 baseEnd_202807 := by
    simpa [prefixWord, tailWord_202807, baseEnd_202807] using wordTrace_append hprefix tailTrace_202807
  have hstable : (prefixWord ++ tailWord_202807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202807).length < 2 ^ (prefixWord ++ tailWord_202807).sum := by decide
  have hdescent : baseEnd_202807 < baseStart_202807 := by decide
  rcases family_descends (prefixWord ++ tailWord_202807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202809 : List Nat := [1, 2, 1, 5, 3, 2, 2, 6]
def baseStart_202809 : Nat := 118140960795 + 202809 * 2 ^ 59
def prefixEnd_202809 : Nat := 4983230072969 + 3 ^ 40 * 202809 * 2
def baseEnd_202809 : Nat := 7713962819096462411467

theorem tailTrace_202809 : CollatzResearch.WordTrace tailWord_202809 prefixEnd_202809 7713962819096462411467 := by
  unfold tailWord_202809
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397051922265104864715481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4931367948176736576476987 7397051922265104864715481)
  ·
    refine ⟨5547788941698828648536611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7397051922265104864715481 5547788941698828648536611)
    ·
      refine ⟨8321683412548242972804917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547788941698828648536611 8321683412548242972804917)
      ·
        refine ⟨780157819926397778700461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8321683412548242972804917 780157819926397778700461)
        ·
          refine ⟨292559182472399167012673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 780157819926397778700461 292559182472399167012673)
          ·
            refine ⟨219419386854299375259505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292559182472399167012673 219419386854299375259505)
            ·
              refine ⟨164564540140724531444629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219419386854299375259505 164564540140724531444629)
              ·
                refine ⟨7713962819096462411467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164564540140724531444629 7713962819096462411467)
                ·
                  rfl

theorem cell22_202809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 6].length) (baseStart_202809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202809 prefixEnd_202809 := by exact prefixLift 202809
  have htrace : WordTrace (prefixWord ++ tailWord_202809) baseStart_202809 baseEnd_202809 := by
    simpa [prefixWord, tailWord_202809, baseEnd_202809] using wordTrace_append hprefix tailTrace_202809
  have hstable : (prefixWord ++ tailWord_202809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202809).length < 2 ^ (prefixWord ++ tailWord_202809).sum := by decide
  have hdescent : baseEnd_202809 < baseStart_202809 := by decide
  rcases family_descends (prefixWord ++ tailWord_202809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202824 : List Nat := [2, 1, 3, 1, 1, 1, 2, 7, 1, 3]
def baseStart_202824 : Nat := 118140960795 + 202824 * 2 ^ 59
def prefixEnd_202824 : Nat := 4983230072969 + 3 ^ 40 * 202824 * 2
def baseEnd_202824 : Nat := 69430800178413122578157

theorem tailTrace_202824 : CollatzResearch.WordTrace tailWord_202824 prefixEnd_202824 69430800178413122578157 := by
  unfold tailWord_202824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3698799508605381213255763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4931732678140508284341017 3698799508605381213255763)
  ·
    refine ⟨5548199262908071819883645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3698799508605381213255763 5548199262908071819883645)
    ·
      refine ⟨2080574723590526932456367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5548199262908071819883645 2080574723590526932456367)
      ·
        refine ⟨3120862085385790398684551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080574723590526932456367 3120862085385790398684551)
        ·
          refine ⟨4681293128078685598026827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120862085385790398684551 4681293128078685598026827)
          ·
            refine ⟨7021939692118028397040241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681293128078685598026827 7021939692118028397040241)
            ·
              refine ⟨5266454769088521297780181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7021939692118028397040241 5266454769088521297780181)
              ·
                refine ⟨123432533650512217916723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5266454769088521297780181 123432533650512217916723)
                ·
                  refine ⟨185148800475768326875085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123432533650512217916723 185148800475768326875085)
                  ·
                    refine ⟨69430800178413122578157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185148800475768326875085 69430800178413122578157)
                    ·
                      rfl

theorem cell22_202824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_202824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202824 prefixEnd_202824 := by exact prefixLift 202824
  have htrace : WordTrace (prefixWord ++ tailWord_202824) baseStart_202824 baseEnd_202824 := by
    simpa [prefixWord, tailWord_202824, baseEnd_202824] using wordTrace_append hprefix tailTrace_202824
  have hstable : (prefixWord ++ tailWord_202824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202824).length < 2 ^ (prefixWord ++ tailWord_202824).sum := by decide
  have hdescent : baseEnd_202824 < baseStart_202824 := by decide
  rcases family_descends (prefixWord ++ tailWord_202824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202841 : List Nat := [1, 2, 1, 2, 2, 1, 7, 2, 1, 3]
def baseStart_202841 : Nat := 118140960795 + 202841 * 2 ^ 59
def prefixEnd_202841 : Nat := 4983230072969 + 3 ^ 40 * 202841 * 2
def baseEnd_202841 : Nat := 69436619625830744903105

theorem tailTrace_202841 : CollatzResearch.WordTrace tailWord_202841 prefixEnd_202841 69436619625830744903105 := by
  unfold tailWord_202841
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398219058149174329880377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4932146038766116219920251 7398219058149174329880377)
  ·
    refine ⟨5548664293611880747410283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7398219058149174329880377 5548664293611880747410283)
    ·
      refine ⟨8322996440417821121115425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5548664293611880747410283 8322996440417821121115425)
      ·
        refine ⟨6242247330313365840836569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8322996440417821121115425 6242247330313365840836569)
        ·
          refine ⟨4681685497735024380627427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6242247330313365840836569 4681685497735024380627427)
          ·
            refine ⟨7022528246602536570941141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681685497735024380627427 7022528246602536570941141)
            ·
              refine ⟨164590505779746950881433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7022528246602536570941141 164590505779746950881433)
              ·
                refine ⟨123442879334810213161075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164590505779746950881433 123442879334810213161075)
                ·
                  refine ⟨185164319002215319741613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123442879334810213161075 185164319002215319741613)
                  ·
                    refine ⟨69436619625830744903105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185164319002215319741613 69436619625830744903105)
                    ·
                      rfl

theorem cell22_202841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 3].length) (baseStart_202841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202841 prefixEnd_202841 := by exact prefixLift 202841
  have htrace : WordTrace (prefixWord ++ tailWord_202841) baseStart_202841 baseEnd_202841 := by
    simpa [prefixWord, tailWord_202841, baseEnd_202841] using wordTrace_append hprefix tailTrace_202841
  have hstable : (prefixWord ++ tailWord_202841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202841).length < 2 ^ (prefixWord ++ tailWord_202841).sum := by decide
  have hdescent : baseEnd_202841 < baseStart_202841 := by decide
  rcases family_descends (prefixWord ++ tailWord_202841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202865 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 8]
def baseStart_202865 : Nat := 118140960795 + 202865 * 2 ^ 59
def prefixEnd_202865 : Nat := 4983230072969 + 3 ^ 40 * 202865 * 2
def baseEnd_202865 : Nat := 23148278438767560767677

theorem tailTrace_202865 : CollatzResearch.WordTrace tailWord_202865 prefixEnd_202865 23148278438767560767677 := by
  unfold tailWord_202865
  simp only [CollatzResearch.WordTrace]
  refine ⟨7399094410062226428754049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4932729606708150952502699 7399094410062226428754049)
  ·
    refine ⟨5549320807546669821565537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7399094410062226428754049 5549320807546669821565537)
    ·
      refine ⟨4161990605660002366174153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5549320807546669821565537 4161990605660002366174153)
      ·
        refine ⟨3121492954245001774630615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4161990605660002366174153 3121492954245001774630615)
        ·
          refine ⟨4682239431367502661945923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121492954245001774630615 4682239431367502661945923)
          ·
            refine ⟨7023359147051253992918885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682239431367502661945923 7023359147051253992918885)
            ·
              refine ⟨1316879840072110123672291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7023359147051253992918885 1316879840072110123672291)
              ·
                refine ⟨1975319760108165185508437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316879840072110123672291 1975319760108165185508437)
                ·
                  refine ⟨23148278438767560767677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1975319760108165185508437 23148278438767560767677)
                  ·
                    rfl

theorem cell22_202865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_202865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202865 prefixEnd_202865 := by exact prefixLift 202865
  have htrace : WordTrace (prefixWord ++ tailWord_202865) baseStart_202865 baseEnd_202865 := by
    simpa [prefixWord, tailWord_202865, baseEnd_202865] using wordTrace_append hprefix tailTrace_202865
  have hstable : (prefixWord ++ tailWord_202865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202865).length < 2 ^ (prefixWord ++ tailWord_202865).sum := by decide
  have hdescent : baseEnd_202865 < baseStart_202865 := by decide
  rcases family_descends (prefixWord ++ tailWord_202865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202914 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_202914 : Nat := 118140960795 + 202914 * 2 ^ 59
def prefixEnd_202914 : Nat := 4983230072969 + 3 ^ 40 * 202914 * 2
def baseEnd_202914 : Nat := 69461609017682887827881

theorem tailTrace_202914 : CollatzResearch.WordTrace tailWord_202914 prefixEnd_202914 69461609017682887827881 := by
  unfold tailWord_202914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850220396721176949321949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4933921057923138531525197 1850220396721176949321949)
  ·
    refine ⟨693832648770441355995731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1850220396721176949321949 693832648770441355995731)
    ·
      refine ⟨1040748973155662033993597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693832648770441355995731 1040748973155662033993597)
      ·
        refine ⟨390280864933373262747599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1040748973155662033993597 390280864933373262747599)
        ·
          refine ⟨585421297400059894121399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390280864933373262747599 585421297400059894121399)
          ·
            refine ⟨878131946100089841182099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585421297400059894121399 878131946100089841182099)
            ·
              refine ⟨1317197919150134761773149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878131946100089841182099 1317197919150134761773149)
              ·
                refine ⟨493949219681300535664931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1317197919150134761773149 493949219681300535664931)
                ·
                  refine ⟨740923829521950803497397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493949219681300535664931 740923829521950803497397)
                  ·
                    refine ⟨69461609017682887827881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 740923829521950803497397 69461609017682887827881)
                    ·
                      rfl

theorem cell22_202914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_202914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202914 prefixEnd_202914 := by exact prefixLift 202914
  have htrace : WordTrace (prefixWord ++ tailWord_202914) baseStart_202914 baseEnd_202914 := by
    simpa [prefixWord, tailWord_202914, baseEnd_202914] using wordTrace_append hprefix tailTrace_202914
  have hstable : (prefixWord ++ tailWord_202914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202914).length < 2 ^ (prefixWord ++ tailWord_202914).sum := by decide
  have hdescent : baseEnd_202914 < baseStart_202914 := by decide
  rcases family_descends (prefixWord ++ tailWord_202914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202929 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_202929 : Nat := 118140960795 + 202929 * 2 ^ 59
def prefixEnd_202929 : Nat := 4983230072969 + 3 ^ 40 * 202929 * 2
def baseEnd_202929 : Nat := 69466743824227848702835

theorem tailTrace_202929 : CollatzResearch.WordTrace tailWord_202929 prefixEnd_202929 69466743824227848702835 := by
  unfold tailWord_202929
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401428681830365359083841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4934285787886910239389227 7401428681830365359083841)
  ·
    refine ⟨5551071511372774019312881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7401428681830365359083841 5551071511372774019312881)
    ·
      refine ⟨4163303633529580514484661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5551071511372774019312881 4163303633529580514484661)
      ·
        refine ⟨390309715643398173232937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4163303633529580514484661 390309715643398173232937)
        ·
          refine ⟨292732286732548629924703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390309715643398173232937 292732286732548629924703)
          ·
            refine ⟨439098430098822944887055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292732286732548629924703 439098430098822944887055)
            ·
              refine ⟨658647645148234417330583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439098430098822944887055 658647645148234417330583)
              ·
                refine ⟨987971467722351625995875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658647645148234417330583 987971467722351625995875)
                ·
                  refine ⟨1481957201583527438993813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987971467722351625995875 1481957201583527438993813)
                  ·
                    refine ⟨69466743824227848702835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1481957201583527438993813 69466743824227848702835)
                    ·
                      rfl

theorem cell22_202929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_202929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202929 prefixEnd_202929 := by exact prefixLift 202929
  have htrace : WordTrace (prefixWord ++ tailWord_202929) baseStart_202929 baseEnd_202929 := by
    simpa [prefixWord, tailWord_202929, baseEnd_202929] using wordTrace_append hprefix tailTrace_202929
  have hstable : (prefixWord ++ tailWord_202929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202929).length < 2 ^ (prefixWord ++ tailWord_202929).sum := by decide
  have hdescent : baseEnd_202929 < baseStart_202929 := by decide
  rcases family_descends (prefixWord ++ tailWord_202929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202933 : List Nat := [1, 3, 3, 4, 1, 1, 2, 3, 4]
def baseStart_202933 : Nat := 118140960795 + 202933 * 2 ^ 59
def prefixEnd_202933 : Nat := 4983230072969 + 3 ^ 40 * 202933 * 2
def baseEnd_202933 : Nat := 23156037701991057200941

theorem tailTrace_202933 : CollatzResearch.WordTrace tailWord_202933 prefixEnd_202933 23156037701991057200941 := by
  unfold tailWord_202933
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401574573815874042229453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4934383049210582694819635 7401574573815874042229453)
  ·
    refine ⟨2775590465180952765836045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7401574573815874042229453 2775590465180952765836045)
    ·
      refine ⟨1040846424442857287188517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2775590465180952765836045 1040846424442857287188517)
      ·
        refine ⟨195158704583035741347847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1040846424442857287188517 195158704583035741347847)
        ·
          refine ⟨292738056874553612021771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195158704583035741347847 292738056874553612021771)
          ·
            refine ⟨439107085311830418032657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292738056874553612021771 439107085311830418032657)
            ·
              refine ⟨329330313983872813524493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439107085311830418032657 329330313983872813524493)
              ·
                refine ⟨123498867743952305071685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329330313983872813524493 123498867743952305071685)
                ·
                  refine ⟨23156037701991057200941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123498867743952305071685 23156037701991057200941)
                  ·
                    rfl

theorem cell22_202933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_202933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202933 prefixEnd_202933 := by exact prefixLift 202933
  have htrace : WordTrace (prefixWord ++ tailWord_202933) baseStart_202933 baseEnd_202933 := by
    simpa [prefixWord, tailWord_202933, baseEnd_202933] using wordTrace_append hprefix tailTrace_202933
  have hstable : (prefixWord ++ tailWord_202933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202933).length < 2 ^ (prefixWord ++ tailWord_202933).sum := by decide
  have hdescent : baseEnd_202933 < baseStart_202933 := by decide
  rcases family_descends (prefixWord ++ tailWord_202933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202948 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_202948 : Nat := 118140960795 + 202948 * 2 ^ 59
def prefixEnd_202948 : Nat := 4983230072969 + 3 ^ 40 * 202948 * 2
def baseEnd_202948 : Nat := 69473247912518132477777

theorem tailTrace_202948 : CollatzResearch.WordTrace tailWord_202948 prefixEnd_202948 69473247912518132477777 := by
  unfold tailWord_202948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701060834380765802012749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4934747779174354402683665 3701060834380765802012749)
  ·
    refine ⟨1387897812892787175754781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3701060834380765802012749 1387897812892787175754781)
    ·
      refine ⟨520461679834795190908043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1387897812892787175754781 520461679834795190908043)
      ·
        refine ⟨780692519752192786362065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520461679834795190908043 780692519752192786362065)
        ·
          refine ⟨585519389814144589771549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780692519752192786362065 585519389814144589771549)
          ·
            refine ⟨219569771180304221164331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585519389814144589771549 219569771180304221164331)
            ·
              refine ⟨329354656770456331746497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219569771180304221164331 329354656770456331746497)
              ·
                refine ⟨247015992577842248809873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329354656770456331746497 247015992577842248809873)
                ·
                  refine ⟨185261994433381686607405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247015992577842248809873 185261994433381686607405)
                  ·
                    refine ⟨69473247912518132477777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185261994433381686607405 69473247912518132477777)
                    ·
                      rfl

theorem cell22_202948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_202948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202948 prefixEnd_202948 := by exact prefixLift 202948
  have htrace : WordTrace (prefixWord ++ tailWord_202948) baseStart_202948 baseEnd_202948 := by
    simpa [prefixWord, tailWord_202948, baseEnd_202948] using wordTrace_append hprefix tailTrace_202948
  have hstable : (prefixWord ++ tailWord_202948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202948).length < 2 ^ (prefixWord ++ tailWord_202948).sum := by decide
  have hdescent : baseEnd_202948 < baseStart_202948 := by decide
  rcases family_descends (prefixWord ++ tailWord_202948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202959 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 3, 3]
def baseStart_202959 : Nat := 118140960795 + 202959 * 2 ^ 59
def prefixEnd_202959 : Nat := 4983230072969 + 3 ^ 40 * 202959 * 2
def baseEnd_202959 : Nat := 69477013437317770452743

theorem tailTrace_202959 : CollatzResearch.WordTrace tailWord_202959 prefixEnd_202959 69477013437317770452743 := by
  unfold tailWord_202959
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402522871721680482675931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4935015247814453655117287 7402522871721680482675931)
  ·
    refine ⟨11103784307582520724013897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7402522871721680482675931 11103784307582520724013897)
    ·
      refine ⟨8327838230686890543010423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11103784307582520724013897 8327838230686890543010423)
      ·
        refine ⟨12491757346030335814515635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8327838230686890543010423 12491757346030335814515635)
        ·
          refine ⟨18737636019045503721773453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12491757346030335814515635 18737636019045503721773453)
          ·
            refine ⟨7026613507142063895665045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18737636019045503721773453 7026613507142063895665045)
            ·
              refine ⟨329372508147284245109299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7026613507142063895665045 329372508147284245109299)
              ·
                refine ⟨494058762220926367663949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329372508147284245109299 494058762220926367663949)
                ·
                  refine ⟨185272035832847387873981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494058762220926367663949 185272035832847387873981)
                  ·
                    refine ⟨69477013437317770452743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185272035832847387873981 69477013437317770452743)
                    ·
                      rfl

theorem cell22_202959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_202959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202959 prefixEnd_202959 := by exact prefixLift 202959
  have htrace : WordTrace (prefixWord ++ tailWord_202959) baseStart_202959 baseEnd_202959 := by
    simpa [prefixWord, tailWord_202959, baseEnd_202959] using wordTrace_append hprefix tailTrace_202959
  have hstable : (prefixWord ++ tailWord_202959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202959).length < 2 ^ (prefixWord ++ tailWord_202959).sum := by decide
  have hdescent : baseEnd_202959 < baseStart_202959 := by decide
  rcases family_descends (prefixWord ++ tailWord_202959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_202978 : List Nat := [3, 3, 4, 1, 1, 1, 1, 8]
def baseStart_202978 : Nat := 118140960795 + 202978 * 2 ^ 59
def prefixEnd_202978 : Nat := 4983230072969 + 3 ^ 40 * 202978 * 2
def baseEnd_202978 : Nat := 7720390836178672691965

theorem tailTrace_202978 : CollatzResearch.WordTrace tailWord_202978 prefixEnd_202978 7720390836178672691965 := by
  unfold tailWord_202978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850803964663211681904397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4935477239101897818411725 1850803964663211681904397)
  ·
    refine ⟨694051486748704380714149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1850803964663211681904397 694051486748704380714149)
    ·
      refine ⟨130134653765382071383903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 694051486748704380714149 130134653765382071383903)
      ·
        refine ⟨195201980648073107075855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130134653765382071383903 195201980648073107075855)
        ·
          refine ⟨292802970972109660613783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195201980648073107075855 292802970972109660613783)
          ·
            refine ⟨439204456458164490920675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292802970972109660613783 439204456458164490920675)
            ·
              refine ⟨658806684687246736381013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439204456458164490920675 658806684687246736381013)
              ·
                refine ⟨7720390836178672691965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 658806684687246736381013 7720390836178672691965)
                ·
                  rfl

theorem cell22_202978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_202978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_202978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_202978 prefixEnd_202978 := by exact prefixLift 202978
  have htrace : WordTrace (prefixWord ++ tailWord_202978) baseStart_202978 baseEnd_202978 := by
    simpa [prefixWord, tailWord_202978, baseEnd_202978] using wordTrace_append hprefix tailTrace_202978
  have hstable : (prefixWord ++ tailWord_202978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_202978).length < 2 ^ (prefixWord ++ tailWord_202978).sum := by decide
  have hdescent : baseEnd_202978 < baseStart_202978 := by decide
  rcases family_descends (prefixWord ++ tailWord_202978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203064 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_203064 : Nat := 118140960795 + 203064 * 2 ^ 59
def prefixEnd_203064 : Nat := 4983230072969 + 3 ^ 40 * 203064 * 2
def baseEnd_203064 : Nat := 69512957083132496577421

theorem tailTrace_203064 : CollatzResearch.WordTrace tailWord_203064 prefixEnd_203064 69512957083132496577421 := by
  unfold tailWord_203064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703176268170641707624123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4937568357560855610165497 3703176268170641707624123)
  ·
    refine ⟨5554764402255962561436185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3703176268170641707624123 5554764402255962561436185)
    ·
      refine ⟨4166073301691971921077139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5554764402255962561436185 4166073301691971921077139)
      ·
        refine ⟨6249109952537957881615709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166073301691971921077139 6249109952537957881615709)
        ·
          refine ⟨2343416232201734205605891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6249109952537957881615709 2343416232201734205605891)
          ·
            refine ⟨3515124348302601308408837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343416232201734205605891 3515124348302601308408837)
            ·
              refine ⟨659085815306737745326657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3515124348302601308408837 659085815306737745326657)
              ·
                refine ⟨494314361480053308994993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659085815306737745326657 494314361480053308994993)
                ·
                  refine ⟨370735771110039981746245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494314361480053308994993 370735771110039981746245)
                  ·
                    refine ⟨69512957083132496577421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 370735771110039981746245 69512957083132496577421)
                    ·
                      rfl

theorem cell22_203064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_203064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203064 prefixEnd_203064 := by exact prefixLift 203064
  have htrace : WordTrace (prefixWord ++ tailWord_203064) baseStart_203064 baseEnd_203064 := by
    simpa [prefixWord, tailWord_203064, baseEnd_203064] using wordTrace_append hprefix tailTrace_203064
  have hstable : (prefixWord ++ tailWord_203064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203064).length < 2 ^ (prefixWord ++ tailWord_203064).sum := by decide
  have hdescent : baseEnd_203064 < baseStart_203064 := by decide
  rcases family_descends (prefixWord ++ tailWord_203064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203066 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_203066 : Nat := 118140960795 + 203066 * 2 ^ 59
def prefixEnd_203066 : Nat := 4983230072969 + 3 ^ 40 * 203066 * 2
def baseEnd_203066 : Nat := 69513641724005158027415

theorem tailTrace_203066 : CollatzResearch.WordTrace tailWord_203066 prefixEnd_203066 69513641724005158027415 := by
  unfold tailWord_203066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851606370583509439205263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4937616988222691837880701 1851606370583509439205263)
  ·
    refine ⟨2777409555875264158807895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1851606370583509439205263 2777409555875264158807895)
    ·
      refine ⟨4166114333812896238211843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2777409555875264158807895 4166114333812896238211843)
      ·
        refine ⟨6249171500719344357317765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166114333812896238211843 6249171500719344357317765)
        ·
          refine ⟨1171719656384877066997081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6249171500719344357317765 1171719656384877066997081)
          ·
            refine ⟨878789742288657800247811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171719656384877066997081 878789742288657800247811)
            ·
              refine ⟨1318184613432986700371717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878789742288657800247811 1318184613432986700371717)
              ·
                refine ⟨247159615018685006319697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1318184613432986700371717 247159615018685006319697)
                ·
                  refine ⟨185369711264013754739773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247159615018685006319697 185369711264013754739773)
                  ·
                    refine ⟨69513641724005158027415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185369711264013754739773 69513641724005158027415)
                    ·
                      rfl

theorem cell22_203066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_203066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203066 prefixEnd_203066 := by exact prefixLift 203066
  have htrace : WordTrace (prefixWord ++ tailWord_203066) baseStart_203066 baseEnd_203066 := by
    simpa [prefixWord, tailWord_203066, baseEnd_203066] using wordTrace_append hprefix tailTrace_203066
  have hstable : (prefixWord ++ tailWord_203066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203066).length < 2 ^ (prefixWord ++ tailWord_203066).sum := by decide
  have hdescent : baseEnd_203066 < baseStart_203066 := by decide
  rcases family_descends (prefixWord ++ tailWord_203066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203077 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_203077 : Nat := 118140960795 + 203077 * 2 ^ 59
def prefixEnd_203077 : Nat := 4983230072969 + 3 ^ 40 * 203077 * 2
def baseEnd_203077 : Nat := 69517407248804796002381

theorem tailTrace_203077 : CollatzResearch.WordTrace tailWord_203077 prefixEnd_203077 69517407248804796002381 := by
  unfold tailWord_203077
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406826685294186635471485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4937884456862791090314323 7406826685294186635471485)
  ·
    refine ⟨2777560006985319988301807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7406826685294186635471485 2777560006985319988301807)
    ·
      refine ⟨4166340010477979982452711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2777560006985319988301807 4166340010477979982452711)
      ·
        refine ⟨6249510015716969973679067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166340010477979982452711 6249510015716969973679067)
        ·
          refine ⟨9374265023575454960518601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6249510015716969973679067 9374265023575454960518601)
          ·
            refine ⟨7030698767681591220388951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9374265023575454960518601 7030698767681591220388951)
            ·
              refine ⟨10546048151522386830583427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030698767681591220388951 10546048151522386830583427)
              ·
                refine ⟨15819072227283580245875141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10546048151522386830583427 15819072227283580245875141)
                ·
                  refine ⟨2966076042615671296101589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15819072227283580245875141 2966076042615671296101589)
                  ·
                    refine ⟨69517407248804796002381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2966076042615671296101589 69517407248804796002381)
                    ·
                      rfl

theorem cell22_203077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_203077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203077 prefixEnd_203077 := by exact prefixLift 203077
  have htrace : WordTrace (prefixWord ++ tailWord_203077) baseStart_203077 baseEnd_203077 := by
    simpa [prefixWord, tailWord_203077, baseEnd_203077] using wordTrace_append hprefix tailTrace_203077
  have hstable : (prefixWord ++ tailWord_203077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203077).length < 2 ^ (prefixWord ++ tailWord_203077).sum := by decide
  have hdescent : baseEnd_203077 < baseStart_203077 := by decide
  rcases family_descends (prefixWord ++ tailWord_203077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203171 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 1, 4]
def baseStart_203171 : Nat := 118140960795 + 203171 * 2 ^ 59
def prefixEnd_203171 : Nat := 4983230072969 + 3 ^ 40 * 203171 * 2
def baseEnd_203171 : Nat := 69549585369819884152093

theorem tailTrace_203171 : CollatzResearch.WordTrace tailWord_203171 prefixEnd_203171 69549585369819884152093 := by
  unfold tailWord_203171
  simp only [CollatzResearch.WordTrace]
  refine ⟨7410255146953640689393367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4940170097969093792928911 7410255146953640689393367)
  ·
    refine ⟨11115382720430461034090051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7410255146953640689393367 11115382720430461034090051)
    ·
      refine ⟨16673074080645691551135077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11115382720430461034090051 16673074080645691551135077)
      ·
        refine ⟨3126201390121067165837827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16673074080645691551135077 3126201390121067165837827)
        ·
          refine ⟨4689302085181600748756741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126201390121067165837827 4689302085181600748756741)
          ·
            refine ⟨879244140971550140391889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4689302085181600748756741 879244140971550140391889)
            ·
              refine ⟨659433105728662605293917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879244140971550140391889 659433105728662605293917)
              ·
                refine ⟨247287414648248476985219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 659433105728662605293917 247287414648248476985219)
                ·
                  refine ⟨370931121972372715477829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247287414648248476985219 370931121972372715477829)
                  ·
                    refine ⟨69549585369819884152093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 370931121972372715477829 69549585369819884152093)
                    ·
                      rfl

theorem cell22_203171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 4].length) (baseStart_203171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203171 prefixEnd_203171 := by exact prefixLift 203171
  have htrace : WordTrace (prefixWord ++ tailWord_203171) baseStart_203171 baseEnd_203171 := by
    simpa [prefixWord, tailWord_203171, baseEnd_203171] using wordTrace_append hprefix tailTrace_203171
  have hstable : (prefixWord ++ tailWord_203171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203171).length < 2 ^ (prefixWord ++ tailWord_203171).sum := by decide
  have hdescent : baseEnd_203171 < baseStart_203171 := by decide
  rcases family_descends (prefixWord ++ tailWord_203171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203235 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 2, 3]
def baseStart_203235 : Nat := 118140960795 + 203235 * 2 ^ 59
def prefixEnd_203235 : Nat := 4983230072969 + 3 ^ 40 * 203235 * 2
def baseEnd_203235 : Nat := 69571493877745050551897

theorem tailTrace_203235 : CollatzResearch.WordTrace tailWord_203235 prefixEnd_203235 69571493877745050551897 := by
  unfold tailWord_203235
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412589418721779619723159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4941726279147853079815439 7412589418721779619723159)
  ·
    refine ⟨11118884128082669429584739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7412589418721779619723159 11118884128082669429584739)
    ·
      refine ⟨16678326192124004144377109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11118884128082669429584739 16678326192124004144377109)
      ·
        refine ⟨781796540255812694267677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16678326192124004144377109 781796540255812694267677)
        ·
          refine ⟨293173702595929760350379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 781796540255812694267677 293173702595929760350379)
          ·
            refine ⟨439760553893894640525569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293173702595929760350379 439760553893894640525569)
            ·
              refine ⟨329820415420420980394177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439760553893894640525569 329820415420420980394177)
              ·
                refine ⟨247365311565315735295633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329820415420420980394177 247365311565315735295633)
                ·
                  refine ⟨185523983673986801471725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247365311565315735295633 185523983673986801471725)
                  ·
                    refine ⟨69571493877745050551897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185523983673986801471725 69571493877745050551897)
                    ·
                      rfl

theorem cell22_203235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 3].length) (baseStart_203235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203235 prefixEnd_203235 := by exact prefixLift 203235
  have htrace : WordTrace (prefixWord ++ tailWord_203235) baseStart_203235 baseEnd_203235 := by
    simpa [prefixWord, tailWord_203235, baseEnd_203235] using wordTrace_append hprefix tailTrace_203235
  have hstable : (prefixWord ++ tailWord_203235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203235).length < 2 ^ (prefixWord ++ tailWord_203235).sum := by decide
  have hdescent : baseEnd_203235 < baseStart_203235 := by decide
  rcases family_descends (prefixWord ++ tailWord_203235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203237 : List Nat := [1, 3, 1, 5, 2, 2, 2, 2, 4]
def baseStart_203237 : Nat := 118140960795 + 203237 * 2 ^ 59
def prefixEnd_203237 : Nat := 4983230072969 + 3 ^ 40 * 203237 * 2
def baseEnd_203237 : Nat := 23190726172872570667297

theorem tailTrace_203237 : CollatzResearch.WordTrace tailWord_203237 prefixEnd_203237 23190726172872570667297 := by
  unfold tailWord_203237
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412662364714533961295965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4941774909809689307530643 7412662364714533961295965)
  ·
    refine ⟨2779748386767950235485987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7412662364714533961295965 2779748386767950235485987)
    ·
      refine ⟨4169622580151925353228981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779748386767950235485987 4169622580151925353228981)
      ·
        refine ⟨390902116889243001865217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4169622580151925353228981 390902116889243001865217)
        ·
          refine ⟨293176587666932251398913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390902116889243001865217 293176587666932251398913)
          ·
            refine ⟨219882440750199188549185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293176587666932251398913 219882440750199188549185)
            ·
              refine ⟨164911830562649391411889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219882440750199188549185 164911830562649391411889)
              ·
                refine ⟨123683872921987043558917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164911830562649391411889 123683872921987043558917)
                ·
                  refine ⟨23190726172872570667297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123683872921987043558917 23190726172872570667297)
                  ·
                    rfl

theorem cell22_203237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_203237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203237 prefixEnd_203237 := by exact prefixLift 203237
  have htrace : WordTrace (prefixWord ++ tailWord_203237) baseStart_203237 baseEnd_203237 := by
    simpa [prefixWord, tailWord_203237, baseEnd_203237] using wordTrace_append hprefix tailTrace_203237
  have hstable : (prefixWord ++ tailWord_203237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203237).length < 2 ^ (prefixWord ++ tailWord_203237).sum := by decide
  have hdescent : baseEnd_203237 < baseStart_203237 := by decide
  rcases family_descends (prefixWord ++ tailWord_203237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203244 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_203244 : Nat := 118140960795 + 203244 * 2 ^ 59
def prefixEnd_203244 : Nat := 4983230072969 + 3 ^ 40 * 203244 * 2
def baseEnd_203244 : Nat := 69574574761672027076869

theorem tailTrace_203244 : CollatzResearch.WordTrace tailWord_203244 prefixEnd_203244 69574574761672027076869 := by
  unfold tailWord_203244
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706458837844587078400393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4941945117126116104533857 3706458837844587078400393)
  ·
    refine ⟨2779844128383440308800295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3706458837844587078400393 2779844128383440308800295)
    ·
      refine ⟨4169766192575160463200443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779844128383440308800295 4169766192575160463200443)
      ·
        refine ⟨6254649288862740694800665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4169766192575160463200443 6254649288862740694800665)
        ·
          refine ⟨4690986966647055521100499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6254649288862740694800665 4690986966647055521100499)
          ·
            refine ⟨7036480449970583281650749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690986966647055521100499 7036480449970583281650749)
            ·
              refine ⟨2638680168738968730619031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7036480449970583281650749 2638680168738968730619031)
              ·
                refine ⟨3958020253108453095928547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638680168738968730619031 3958020253108453095928547)
                ·
                  refine ⟨5937030379662679643892821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958020253108453095928547 5937030379662679643892821)
                  ·
                    refine ⟨69574574761672027076869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5937030379662679643892821 69574574761672027076869)
                    ·
                      rfl

theorem cell22_203244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_203244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203244 prefixEnd_203244 := by exact prefixLift 203244
  have htrace : WordTrace (prefixWord ++ tailWord_203244) baseStart_203244 baseEnd_203244 := by
    simpa [prefixWord, tailWord_203244, baseEnd_203244] using wordTrace_append hprefix tailTrace_203244
  have hstable : (prefixWord ++ tailWord_203244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203244).length < 2 ^ (prefixWord ++ tailWord_203244).sum := by decide
  have hdescent : baseEnd_203244 < baseStart_203244 := by decide
  rcases family_descends (prefixWord ++ tailWord_203244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203293 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 5]
def baseStart_203293 : Nat := 118140960795 + 203293 * 2 ^ 59
def prefixEnd_203293 : Nat := 4983230072969 + 3 ^ 40 * 203293 * 2
def baseEnd_203293 : Nat := 23197116154350744200573

theorem tailTrace_203293 : CollatzResearch.WordTrace tailWord_203293 prefixEnd_203293 23197116154350744200573 := by
  unfold tailWord_203293
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414704852511655525334533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4943136568341103683556355 7414704852511655525334533)
  ·
    refine ⟨1390257159845935411000225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7414704852511655525334533 1390257159845935411000225)
    ·
      refine ⟨1042692869884451558250169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1390257159845935411000225 1042692869884451558250169)
      ·
        refine ⟨782019652413338668687627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1042692869884451558250169 782019652413338668687627)
        ·
          refine ⟨1173029478620008003031441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782019652413338668687627 1173029478620008003031441)
          ·
            refine ⟨879772108965006002273581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173029478620008003031441 879772108965006002273581)
            ·
              refine ⟨329914540861877250852593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879772108965006002273581 329914540861877250852593)
              ·
                refine ⟨247435905646407938139445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329914540861877250852593 247435905646407938139445)
                ·
                  refine ⟨23197116154350744200573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247435905646407938139445 23197116154350744200573)
                  ·
                    rfl

theorem cell22_203293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_203293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203293 prefixEnd_203293 := by exact prefixLift 203293
  have htrace : WordTrace (prefixWord ++ tailWord_203293) baseStart_203293 baseEnd_203293 := by
    simpa [prefixWord, tailWord_203293, baseEnd_203293] using wordTrace_append hprefix tailTrace_203293
  have hstable : (prefixWord ++ tailWord_203293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203293).length < 2 ^ (prefixWord ++ tailWord_203293).sum := by decide
  have hdescent : baseEnd_203293 < baseStart_203293 := by decide
  rcases family_descends (prefixWord ++ tailWord_203293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203321 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 6]
def baseStart_203321 : Nat := 118140960795 + 203321 * 2 ^ 59
def prefixEnd_203321 : Nat := 4983230072969 + 3 ^ 40 * 203321 * 2
def baseEnd_203321 : Nat := 23200311145089830967211

theorem tailTrace_203321 : CollatzResearch.WordTrace tailWord_203321 prefixEnd_203321 23200311145089830967211 := by
  unfold tailWord_203321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7415726096410216307353817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4943817397606810871569211 7415726096410216307353817)
  ·
    refine ⟨5561794572307662230515363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7415726096410216307353817 5561794572307662230515363)
    ·
      refine ⟨8342691858461493345773045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561794572307662230515363 8342691858461493345773045)
      ·
        refine ⟨782127361730765001166223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8342691858461493345773045 782127361730765001166223)
        ·
          refine ⟨1173191042596147501749335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782127361730765001166223 1173191042596147501749335)
          ·
            refine ⟨1759786563894221252624003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173191042596147501749335 1759786563894221252624003)
            ·
              refine ⟨2639679845841331878936005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759786563894221252624003 2639679845841331878936005)
              ·
                refine ⟨494939971095249727300501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2639679845841331878936005 494939971095249727300501)
                ·
                  refine ⟨23200311145089830967211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 494939971095249727300501 23200311145089830967211)
                  ·
                    rfl

theorem cell22_203321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_203321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203321 prefixEnd_203321 := by exact prefixLift 203321
  have htrace : WordTrace (prefixWord ++ tailWord_203321) baseStart_203321 baseEnd_203321 := by
    simpa [prefixWord, tailWord_203321, baseEnd_203321] using wordTrace_append hprefix tailTrace_203321
  have hstable : (prefixWord ++ tailWord_203321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203321).length < 2 ^ (prefixWord ++ tailWord_203321).sum := by decide
  have hdescent : baseEnd_203321 < baseStart_203321 := by decide
  rcases family_descends (prefixWord ++ tailWord_203321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203336 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_203336 : Nat := 118140960795 + 203336 * 2 ^ 59
def prefixEnd_203336 : Nat := 4983230072969 + 3 ^ 40 * 203336 * 2
def baseEnd_203336 : Nat := 69606068241814453776587

theorem tailTrace_203336 : CollatzResearch.WordTrace tailWord_203336 prefixEnd_203336 69606068241814453776587 := by
  unfold tailWord_203336
  simp only [CollatzResearch.WordTrace]
  refine ⟨3708136595677936934574931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4944182127570582579433241 3708136595677936934574931)
  ·
    refine ⟨5562204893516905401862397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3708136595677936934574931 5562204893516905401862397)
    ·
      refine ⟨2085826835068839525698399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5562204893516905401862397 2085826835068839525698399)
      ·
        refine ⟨3128740252603259288547599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085826835068839525698399 3128740252603259288547599)
        ·
          refine ⟨4693110378904888932821399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128740252603259288547599 4693110378904888932821399)
          ·
            refine ⟨7039665568357333399232099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693110378904888932821399 7039665568357333399232099)
            ·
              refine ⟨10559498352536000098848149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039665568357333399232099 10559498352536000098848149)
              ·
                refine ⟨494976485275125004633507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10559498352536000098848149 494976485275125004633507)
                ·
                  refine ⟨742464727912687506950261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494976485275125004633507 742464727912687506950261)
                  ·
                    refine ⟨69606068241814453776587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 742464727912687506950261 69606068241814453776587)
                    ·
                      rfl

theorem cell22_203336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_203336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203336 prefixEnd_203336 := by exact prefixLift 203336
  have htrace : WordTrace (prefixWord ++ tailWord_203336) baseStart_203336 baseEnd_203336 := by
    simpa [prefixWord, tailWord_203336, baseEnd_203336] using wordTrace_append hprefix tailTrace_203336
  have hstable : (prefixWord ++ tailWord_203336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203336).length < 2 ^ (prefixWord ++ tailWord_203336).sum := by decide
  have hdescent : baseEnd_203336 < baseStart_203336 := by decide
  rcases family_descends (prefixWord ++ tailWord_203336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203370 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_203370 : Nat := 118140960795 + 203370 * 2 ^ 59
def prefixEnd_203370 : Nat := 4983230072969 + 3 ^ 40 * 203370 * 2
def baseEnd_203370 : Nat := 69617707136649698426483

theorem tailTrace_203370 : CollatzResearch.WordTrace tailWord_203370 prefixEnd_203370 69617707136649698426483 := by
  unfold tailWord_203370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854378318308174418971891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4945008848821798450591709 1854378318308174418971891)
  ·
    refine ⟨2781567477462261628457837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1854378318308174418971891 2781567477462261628457837)
    ·
      refine ⟨1043087804048348110671689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2781567477462261628457837 1043087804048348110671689)
      ·
        refine ⟨782315853036261083003767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1043087804048348110671689 782315853036261083003767)
        ·
          refine ⟨1173473779554391624505651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782315853036261083003767 1173473779554391624505651)
          ·
            refine ⟨1760210669331587436758477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173473779554391624505651 1760210669331587436758477)
            ·
              refine ⟨660079000999345288784429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1760210669331587436758477 660079000999345288784429)
              ·
                refine ⟨247529625374754483294161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660079000999345288784429 247529625374754483294161)
                ·
                  refine ⟨185647219031065862470621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247529625374754483294161 185647219031065862470621)
                  ·
                    refine ⟨69617707136649698426483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185647219031065862470621 69617707136649698426483)
                    ·
                      rfl

theorem cell22_203370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_203370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203370 prefixEnd_203370 := by exact prefixLift 203370
  have htrace : WordTrace (prefixWord ++ tailWord_203370) baseStart_203370 baseEnd_203370 := by
    simpa [prefixWord, tailWord_203370, baseEnd_203370] using wordTrace_append hprefix tailTrace_203370
  have hstable : (prefixWord ++ tailWord_203370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203370).length < 2 ^ (prefixWord ++ tailWord_203370).sum := by decide
  have hdescent : baseEnd_203370 < baseStart_203370 := by decide
  rcases family_descends (prefixWord ++ tailWord_203370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203428 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 5]
def baseStart_203428 : Nat := 118140960795 + 203428 * 2 ^ 59
def prefixEnd_203428 : Nat := 4983230072969 + 3 ^ 40 * 203428 * 2
def baseEnd_203428 : Nat := 23212520573985626825435

theorem tailTrace_203428 : CollatzResearch.WordTrace tailWord_203428 prefixEnd_203428 23212520573985626825435 := by
  unfold tailWord_203428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709814353511286790749469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4946419138015049054332625 3709814353511286790749469)
  ·
    refine ⟨1391180382566732546531051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3709814353511286790749469 1391180382566732546531051)
    ·
      refine ⟨2086770573850098819796577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391180382566732546531051 2086770573850098819796577)
      ·
        refine ⟨1565077930387574114847433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2086770573850098819796577 1565077930387574114847433)
        ·
          refine ⟨1173808447790680586135575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565077930387574114847433 1173808447790680586135575)
          ·
            refine ⟨1760712671686020879203363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173808447790680586135575 1760712671686020879203363)
            ·
              refine ⟨2641069007529031318805045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760712671686020879203363 2641069007529031318805045)
              ·
                refine ⟨247600219455846686137973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2641069007529031318805045 247600219455846686137973)
                ·
                  refine ⟨23212520573985626825435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247600219455846686137973 23212520573985626825435)
                  ·
                    rfl

theorem cell22_203428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_203428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203428 prefixEnd_203428 := by exact prefixLift 203428
  have htrace : WordTrace (prefixWord ++ tailWord_203428) baseStart_203428 baseEnd_203428 := by
    simpa [prefixWord, tailWord_203428, baseEnd_203428] using wordTrace_append hprefix tailTrace_203428
  have hstable : (prefixWord ++ tailWord_203428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203428).length < 2 ^ (prefixWord ++ tailWord_203428).sum := by decide
  have hdescent : baseEnd_203428 < baseStart_203428 := by decide
  rcases family_descends (prefixWord ++ tailWord_203428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203471 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 9]
def baseStart_203471 : Nat := 118140960795 + 203471 * 2 ^ 59
def prefixEnd_203471 : Nat := 4983230072969 + 3 ^ 40 * 203471 * 2
def baseEnd_203471 : Nat := 69652281500719101651173

theorem tailTrace_203471 : CollatzResearch.WordTrace tailWord_203471 prefixEnd_203471 69652281500719101651173 := by
  unfold tailWord_203471
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421197045866791925314267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4947464697244527950209511 7421197045866791925314267)
  ·
    refine ⟨11131795568800187887971401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7421197045866791925314267 11131795568800187887971401)
    ·
      refine ⟨8348846676600140915978551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11131795568800187887971401 8348846676600140915978551)
      ·
        refine ⟨12523270014900211373967827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8348846676600140915978551 12523270014900211373967827)
        ·
          refine ⟨18784905022350317060951741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12523270014900211373967827 18784905022350317060951741)
          ·
            refine ⟨7044339383381368897856903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18784905022350317060951741 7044339383381368897856903)
            ·
              refine ⟨10566509075072053346785355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7044339383381368897856903 10566509075072053346785355)
              ·
                refine ⟨15849763612608080020178033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10566509075072053346785355 15849763612608080020178033)
                ·
                  refine ⟨11887322709456060015133525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15849763612608080020178033 11887322709456060015133525)
                  ·
                    refine ⟨69652281500719101651173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 11887322709456060015133525 69652281500719101651173)
                    ·
                      rfl

theorem cell22_203471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_203471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203471 prefixEnd_203471 := by exact prefixLift 203471
  have htrace : WordTrace (prefixWord ++ tailWord_203471) baseStart_203471 baseEnd_203471 := by
    simpa [prefixWord, tailWord_203471, baseEnd_203471] using wordTrace_append hprefix tailTrace_203471
  have hstable : (prefixWord ++ tailWord_203471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203471).length < 2 ^ (prefixWord ++ tailWord_203471).sum := by decide
  have hdescent : baseEnd_203471 < baseStart_203471 := by decide
  rcases family_descends (prefixWord ++ tailWord_203471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203473 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 6]
def baseStart_203473 : Nat := 118140960795 + 203473 * 2 ^ 59
def prefixEnd_203473 : Nat := 4983230072969 + 3 ^ 40 * 203473 * 2
def baseEnd_203473 : Nat := 23217655380530587700389

theorem tailTrace_203473 : CollatzResearch.WordTrace tailWord_203473 prefixEnd_203473 23217655380530587700389 := by
  unfold tailWord_203473
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421269991859546266887073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4947513327906364177924715 7421269991859546266887073)
  ·
    refine ⟨5565952493894659700165305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7421269991859546266887073 5565952493894659700165305)
    ·
      refine ⟨4174464370420994775123979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5565952493894659700165305 4174464370420994775123979)
      ·
        refine ⟨6261696555631492162685969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174464370420994775123979 6261696555631492162685969)
        ·
          refine ⟨4696272416723619122014477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6261696555631492162685969 4696272416723619122014477)
          ·
            refine ⟨1761102156271357170755429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4696272416723619122014477 1761102156271357170755429)
            ·
              refine ⟨330206654300879469516643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1761102156271357170755429 330206654300879469516643)
              ·
                refine ⟨495309981451319204274965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330206654300879469516643 495309981451319204274965)
                ·
                  refine ⟨23217655380530587700389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 495309981451319204274965 23217655380530587700389)
                  ·
                    rfl

theorem cell22_203473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_203473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203473 prefixEnd_203473 := by exact prefixLift 203473
  have htrace : WordTrace (prefixWord ++ tailWord_203473) baseStart_203473 baseEnd_203473 := by
    simpa [prefixWord, tailWord_203473, baseEnd_203473] using wordTrace_append hprefix tailTrace_203473
  have hstable : (prefixWord ++ tailWord_203473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203473).length < 2 ^ (prefixWord ++ tailWord_203473).sum := by decide
  have hdescent : baseEnd_203473 < baseStart_203473 := by decide
  rcases family_descends (prefixWord ++ tailWord_203473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203503 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 1, 6]
def baseStart_203503 : Nat := 118140960795 + 203503 * 2 ^ 59
def prefixEnd_203503 : Nat := 4983230072969 + 3 ^ 40 * 203503 * 2
def baseEnd_203503 : Nat := 69663235754681684851075

theorem tailTrace_203503 : CollatzResearch.WordTrace tailWord_203503 prefixEnd_203503 69663235754681684851075 := by
  unfold tailWord_203503
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422364181750861390479163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4948242787833907593652775 7422364181750861390479163)
  ·
    refine ⟨11133546272626292085718745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7422364181750861390479163 11133546272626292085718745)
    ·
      refine ⟨8350159704469719064289059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11133546272626292085718745 8350159704469719064289059)
      ·
        refine ⟨12525239556704578596433589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8350159704469719064289059 12525239556704578596433589)
        ·
          refine ⟨1174241208441054243415649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12525239556704578596433589 1174241208441054243415649)
          ·
            refine ⟨880680906330790682561737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174241208441054243415649 880680906330790682561737)
            ·
              refine ⟨660510679748093011921303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880680906330790682561737 660510679748093011921303)
              ·
                refine ⟨990766019622139517881955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660510679748093011921303 990766019622139517881955)
                ·
                  refine ⟨1486149029433209276822933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990766019622139517881955 1486149029433209276822933)
                  ·
                    refine ⟨69663235754681684851075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1486149029433209276822933 69663235754681684851075)
                    ·
                      rfl

theorem cell22_203503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_203503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203503 prefixEnd_203503 := by exact prefixLift 203503
  have htrace : WordTrace (prefixWord ++ tailWord_203503) baseStart_203503 baseEnd_203503 := by
    simpa [prefixWord, tailWord_203503, baseEnd_203503] using wordTrace_append hprefix tailTrace_203503
  have hstable : (prefixWord ++ tailWord_203503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203503).length < 2 ^ (prefixWord ++ tailWord_203503).sum := by decide
  have hdescent : baseEnd_203503 < baseStart_203503 := by decide
  rcases family_descends (prefixWord ++ tailWord_203503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203522 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_203522 : Nat := 118140960795 + 203522 * 2 ^ 59
def prefixEnd_203522 : Nat := 4983230072969 + 3 ^ 40 * 203522 * 2
def baseEnd_203522 : Nat := 69669739842971968626017

theorem tailTrace_203522 : CollatzResearch.WordTrace tailWord_203522 prefixEnd_203522 69669739842971968626017 := by
  unfold tailWord_203522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855764292170506908855205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4948704779121351756947213 1855764292170506908855205)
  ·
    refine ⟨347955804781970045410351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1855764292170506908855205 347955804781970045410351)
    ·
      refine ⟨521933707172955068115527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347955804781970045410351 521933707172955068115527)
      ·
        refine ⟨782900560759432602173291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521933707172955068115527 782900560759432602173291)
        ·
          refine ⟨1174350841139148903259937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782900560759432602173291 1174350841139148903259937)
          ·
            refine ⟨880763130854361677444953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174350841139148903259937 880763130854361677444953)
            ·
              refine ⟨660572348140771258083715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880763130854361677444953 660572348140771258083715)
              ·
                refine ⟨990858522211156887125573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660572348140771258083715 990858522211156887125573)
                ·
                  refine ⟨185785972914591916336045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990858522211156887125573 185785972914591916336045)
                  ·
                    refine ⟨69669739842971968626017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185785972914591916336045 69669739842971968626017)
                    ·
                      rfl

theorem cell22_203522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_203522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203522 prefixEnd_203522 := by exact prefixLift 203522
  have htrace : WordTrace (prefixWord ++ tailWord_203522) baseStart_203522 baseEnd_203522 := by
    simpa [prefixWord, tailWord_203522, baseEnd_203522] using wordTrace_append hprefix tailTrace_203522
  have hstable : (prefixWord ++ tailWord_203522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203522).length < 2 ^ (prefixWord ++ tailWord_203522).sum := by decide
  have hdescent : baseEnd_203522 < baseStart_203522 := by decide
  rcases family_descends (prefixWord ++ tailWord_203522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203610 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_203610 : Nat := 118140960795 + 203610 * 2 ^ 59
def prefixEnd_203610 : Nat := 4983230072969 + 3 ^ 40 * 203610 * 2
def baseEnd_203610 : Nat := 69699864041369072425747

theorem tailTrace_203610 : CollatzResearch.WordTrace tailWord_203610 prefixEnd_203610 69699864041369072425747 := by
  unfold tailWord_203610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856566698090804666156071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4950844528242145776416189 1856566698090804666156071)
  ·
    refine ⟨2784850047136206999234107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1856566698090804666156071 2784850047136206999234107)
    ·
      refine ⟨4177275070704310498851161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2784850047136206999234107 4177275070704310498851161)
      ·
        refine ⟨3132956303028232874138371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4177275070704310498851161 3132956303028232874138371)
        ·
          refine ⟨4699434454542349311207557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132956303028232874138371 4699434454542349311207557)
          ·
            refine ⟨881143960226690495851417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4699434454542349311207557 881143960226690495851417)
            ·
              refine ⟨660857970170017871888563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881143960226690495851417 660857970170017871888563)
              ·
                refine ⟨991286955255026807832845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660857970170017871888563 991286955255026807832845)
                ·
                  refine ⟨371732608220635052937317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991286955255026807832845 371732608220635052937317)
                  ·
                    refine ⟨69699864041369072425747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 371732608220635052937317 69699864041369072425747)
                    ·
                      rfl

theorem cell22_203610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_203610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203610 prefixEnd_203610 := by exact prefixLift 203610
  have htrace : WordTrace (prefixWord ++ tailWord_203610) baseStart_203610 baseEnd_203610 := by
    simpa [prefixWord, tailWord_203610, baseEnd_203610] using wordTrace_append hprefix tailTrace_203610
  have hstable : (prefixWord ++ tailWord_203610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203610).length < 2 ^ (prefixWord ++ tailWord_203610).sum := by decide
  have hdescent : baseEnd_203610 < baseStart_203610 := by decide
  rcases family_descends (prefixWord ++ tailWord_203610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203627 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 1, 4]
def baseStart_203627 : Nat := 118140960795 + 203627 * 2 ^ 59
def prefixEnd_203627 : Nat := 4983230072969 + 3 ^ 40 * 203627 * 2
def baseEnd_203627 : Nat := 69705683488786694750695

theorem tailTrace_203627 : CollatzResearch.WordTrace tailWord_203627 prefixEnd_203627 69705683488786694750695 := by
  unfold tailWord_203627
  simp only [CollatzResearch.WordTrace]
  refine ⟨7426886833301630567993135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4951257888867753711995423 7426886833301630567993135)
  ·
    refine ⟨11140330249952445851989703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7426886833301630567993135 11140330249952445851989703)
    ·
      refine ⟨16710495374928668777984555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11140330249952445851989703 16710495374928668777984555)
      ·
        refine ⟨25065743062393003166976833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16710495374928668777984555 25065743062393003166976833)
        ·
          refine ⟨18799307296794752375232625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25065743062393003166976833 18799307296794752375232625)
          ·
            refine ⟨14099480472596064281424469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18799307296794752375232625 14099480472596064281424469)
            ·
              refine ⟨165228286788235128297943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 14099480472596064281424469 165228286788235128297943)
              ·
                refine ⟨247842430182352692446915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165228286788235128297943 247842430182352692446915)
                ·
                  refine ⟨371763645273529038670373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247842430182352692446915 371763645273529038670373)
                  ·
                    refine ⟨69705683488786694750695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 371763645273529038670373 69705683488786694750695)
                    ·
                      rfl

theorem cell22_203627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 4].length) (baseStart_203627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203627 prefixEnd_203627 := by exact prefixLift 203627
  have htrace : WordTrace (prefixWord ++ tailWord_203627) baseStart_203627 baseEnd_203627 := by
    simpa [prefixWord, tailWord_203627, baseEnd_203627] using wordTrace_append hprefix tailTrace_203627
  have hstable : (prefixWord ++ tailWord_203627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203627).length < 2 ^ (prefixWord ++ tailWord_203627).sum := by decide
  have hdescent : baseEnd_203627 < baseStart_203627 := by decide
  rcases family_descends (prefixWord ++ tailWord_203627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203655 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 1, 6]
def baseStart_203655 : Nat := 118140960795 + 203655 * 2 ^ 59
def prefixEnd_203655 : Nat := 4983230072969 + 3 ^ 40 * 203655 * 2
def baseEnd_203655 : Nat := 69715268461003955050609

theorem tailTrace_203655 : CollatzResearch.WordTrace tailWord_203655 prefixEnd_203655 69715268461003955050609 := by
  unfold tailWord_203655
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427908077200191350012419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4951938718133460900008279 7427908077200191350012419)
  ·
    refine ⟨11141862115800287025018629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7427908077200191350012419 11141862115800287025018629)
    ·
      refine ⟨2089099146712553817190993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11141862115800287025018629 2089099146712553817190993)
      ·
        refine ⟨1566824360034415362893245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2089099146712553817190993 1566824360034415362893245)
        ·
          refine ⟨587559135012905761084967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1566824360034415362893245 587559135012905761084967)
          ·
            refine ⟨881338702519358641627451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587559135012905761084967 881338702519358641627451)
            ·
              refine ⟨1322008053779037962441177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881338702519358641627451 1322008053779037962441177)
              ·
                refine ⟨991506040334278471830883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322008053779037962441177 991506040334278471830883)
                ·
                  refine ⟨1487259060501417707746325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991506040334278471830883 1487259060501417707746325)
                  ·
                    refine ⟨69715268461003955050609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1487259060501417707746325 69715268461003955050609)
                    ·
                      rfl

theorem cell22_203655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_203655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203655 prefixEnd_203655 := by exact prefixLift 203655
  have htrace : WordTrace (prefixWord ++ tailWord_203655) baseStart_203655 baseEnd_203655 := by
    simpa [prefixWord, tailWord_203655, baseEnd_203655] using wordTrace_append hprefix tailTrace_203655
  have hstable : (prefixWord ++ tailWord_203655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203655).length < 2 ^ (prefixWord ++ tailWord_203655).sum := by decide
  have hdescent : baseEnd_203655 < baseStart_203655 := by decide
  rcases family_descends (prefixWord ++ tailWord_203655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203657 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 1, 5]
def baseStart_203657 : Nat := 118140960795 + 203657 * 2 ^ 59
def prefixEnd_203657 : Nat := 4983230072969 + 3 ^ 40 * 203657 * 2
def baseEnd_203657 : Nat := 69715953101876616500603

theorem tailTrace_203657 : CollatzResearch.WordTrace tailWord_203657 prefixEnd_203657 69715953101876616500603 := by
  unfold tailWord_203657
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427981023192945691585225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4951987348795297127723483 7427981023192945691585225)
  ·
    refine ⟨5570985767394709268688919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7427981023192945691585225 5570985767394709268688919)
    ·
      refine ⟨8356478651092063903033379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5570985767394709268688919 8356478651092063903033379)
      ·
        refine ⟨12534717976638095854550069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8356478651092063903033379 12534717976638095854550069)
        ·
          refine ⟨1175129810309821486364069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12534717976638095854550069 1175129810309821486364069)
          ·
            refine ⟨220336839433091528693263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1175129810309821486364069 220336839433091528693263)
            ·
              refine ⟨330505259149637293039895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220336839433091528693263 330505259149637293039895)
              ·
                refine ⟨495757888724455939559843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330505259149637293039895 495757888724455939559843)
                ·
                  refine ⟨743636833086683909339765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495757888724455939559843 743636833086683909339765)
                  ·
                    refine ⟨69715953101876616500603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 743636833086683909339765 69715953101876616500603)
                    ·
                      rfl

theorem cell22_203657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_203657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203657 prefixEnd_203657 := by exact prefixLift 203657
  have htrace : WordTrace (prefixWord ++ tailWord_203657) baseStart_203657 baseEnd_203657 := by
    simpa [prefixWord, tailWord_203657, baseEnd_203657] using wordTrace_append hprefix tailTrace_203657
  have hstable : (prefixWord ++ tailWord_203657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203657).length < 2 ^ (prefixWord ++ tailWord_203657).sum := by decide
  have hdescent : baseEnd_203657 < baseStart_203657 := by decide
  rcases family_descends (prefixWord ++ tailWord_203657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203676 : List Nat := [2, 2, 3, 3, 2, 2, 1, 3, 4]
def baseStart_203676 : Nat := 118140960795 + 203676 * 2 ^ 59
def prefixEnd_203676 : Nat := 4983230072969 + 3 ^ 40 * 203676 * 2
def baseEnd_203676 : Nat := 23240819063388966758515

theorem tailTrace_203676 : CollatzResearch.WordTrace tailWord_203676 prefixEnd_203676 23240819063388966758515 := by
  unfold tailWord_203676
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714337005062055968263441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4952449340082741291017921 3714337005062055968263441)
  ·
    refine ⟨2785752753796541976197581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3714337005062055968263441 2785752753796541976197581)
    ·
      refine ⟨1044657282673703241074093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2785752753796541976197581 1044657282673703241074093)
      ·
        refine ⟨391746481002638715402785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1044657282673703241074093 391746481002638715402785)
        ·
          refine ⟨293809860751979036552089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391746481002638715402785 293809860751979036552089)
          ·
            refine ⟨220357395563984277414067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293809860751979036552089 220357395563984277414067)
            ·
              refine ⟨330536093345976416121101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220357395563984277414067 330536093345976416121101)
              ·
                refine ⟨123951035004741156045413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330536093345976416121101 123951035004741156045413)
                ·
                  refine ⟨23240819063388966758515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123951035004741156045413 23240819063388966758515)
                  ·
                    rfl

theorem cell22_203676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_203676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203676 prefixEnd_203676 := by exact prefixLift 203676
  have htrace : WordTrace (prefixWord ++ tailWord_203676) baseStart_203676 baseEnd_203676 := by
    simpa [prefixWord, tailWord_203676, baseEnd_203676] using wordTrace_append hprefix tailTrace_203676
  have hstable : (prefixWord ++ tailWord_203676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203676).length < 2 ^ (prefixWord ++ tailWord_203676).sum := by decide
  have hdescent : baseEnd_203676 < baseStart_203676 := by decide
  rcases family_descends (prefixWord ++ tailWord_203676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203687 : List Nat := [1, 1, 6, 1, 3, 2, 8]
def baseStart_203687 : Nat := 118140960795 + 203687 * 2 ^ 59
def prefixEnd_203687 : Nat := 4983230072969 + 3 ^ 40 * 203687 * 2
def baseEnd_203687 : Nat := 2582452693146908824093

theorem tailTrace_203687 : CollatzResearch.WordTrace tailWord_203687 prefixEnd_203687 2582452693146908824093 := by
  unfold tailWord_203687
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429075213084260815177315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4952716808722840543451543 7429075213084260815177315)
  ·
    refine ⟨11143612819626391222765973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7429075213084260815177315 11143612819626391222765973)
    ·
      refine ⟨522356850919987088567155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11143612819626391222765973 522356850919987088567155)
      ·
        refine ⟨783535276379980632850733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522356850919987088567155 783535276379980632850733)
        ·
          refine ⟨293825728642492737319025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783535276379980632850733 293825728642492737319025)
          ·
            refine ⟨220369296481869552989269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293825728642492737319025 220369296481869552989269)
            ·
              refine ⟨2582452693146908824093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 220369296481869552989269 2582452693146908824093)
              ·
                rfl

theorem cell22_203687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 8].length) (baseStart_203687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203687 prefixEnd_203687 := by exact prefixLift 203687
  have htrace : WordTrace (prefixWord ++ tailWord_203687) baseStart_203687 baseEnd_203687 := by
    simpa [prefixWord, tailWord_203687, baseEnd_203687] using wordTrace_append hprefix tailTrace_203687
  have hstable : (prefixWord ++ tailWord_203687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203687).length < 2 ^ (prefixWord ++ tailWord_203687).sum := by decide
  have hdescent : baseEnd_203687 < baseStart_203687 := by decide
  rcases family_descends (prefixWord ++ tailWord_203687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203693 : List Nat := [1, 5, 2, 3, 1, 1, 3, 2, 4]
def baseStart_203693 : Nat := 118140960795 + 203693 * 2 ^ 59
def prefixEnd_203693 : Nat := 4983230072969 + 3 ^ 40 * 203693 * 2
def baseEnd_203693 : Nat := 23242758879194840866831

theorem tailTrace_203693 : CollatzResearch.WordTrace tailWord_203693 prefixEnd_203693 23242758879194840866831 := by
  unfold tailWord_203693
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429294051062523839895733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4952862700708349226597155 7429294051062523839895733)
  ·
    refine ⟨696496317287111609990225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7429294051062523839895733 696496317287111609990225)
    ·
      refine ⟨522372237965333707492669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 696496317287111609990225 522372237965333707492669)
      ·
        refine ⟨195889589237000140309751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 522372237965333707492669 195889589237000140309751)
        ·
          refine ⟨293834383855500210464627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195889589237000140309751 293834383855500210464627)
          ·
            refine ⟨440751575783250315696941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293834383855500210464627 440751575783250315696941)
            ·
              refine ⟨165281840918718868386353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440751575783250315696941 165281840918718868386353)
              ·
                refine ⟨123961380689039151289765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165281840918718868386353 123961380689039151289765)
                ·
                  refine ⟨23242758879194840866831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123961380689039151289765 23242758879194840866831)
                  ·
                    rfl

theorem cell22_203693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_203693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203693 prefixEnd_203693 := by exact prefixLift 203693
  have htrace : WordTrace (prefixWord ++ tailWord_203693) baseStart_203693 baseEnd_203693 := by
    simpa [prefixWord, tailWord_203693, baseEnd_203693] using wordTrace_append hprefix tailTrace_203693
  have hstable : (prefixWord ++ tailWord_203693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203693).length < 2 ^ (prefixWord ++ tailWord_203693).sum := by decide
  have hdescent : baseEnd_203693 < baseStart_203693 := by decide
  rcases family_descends (prefixWord ++ tailWord_203693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203715 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 5]
def baseStart_203715 : Nat := 118140960795 + 203715 * 2 ^ 59
def prefixEnd_203715 : Nat := 4983230072969 + 3 ^ 40 * 203715 * 2
def baseEnd_203715 : Nat := 23245269229061266183475

theorem tailTrace_203715 : CollatzResearch.WordTrace tailWord_203715 prefixEnd_203715 23245269229061266183475 := by
  unfold tailWord_203715
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430096456982821597196599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4953397637988547731464399 7430096456982821597196599)
  ·
    refine ⟨11145144685474232395794899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7430096456982821597196599 11145144685474232395794899)
    ·
      refine ⟨16717717028211348593692349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11145144685474232395794899 16717717028211348593692349)
      ·
        refine ⟨6269143885579255722634631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16717717028211348593692349 6269143885579255722634631)
        ·
          refine ⟨9403715828368883583951947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6269143885579255722634631 9403715828368883583951947)
          ·
            refine ⟨14105573742553325375927921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9403715828368883583951947 14105573742553325375927921)
            ·
              refine ⟨10579180306914994031945941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14105573742553325375927921 10579180306914994031945941)
              ·
                refine ⟨247949538443320172623733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10579180306914994031945941 247949538443320172623733)
                ·
                  refine ⟨23245269229061266183475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247949538443320172623733 23245269229061266183475)
                  ·
                    rfl

theorem cell22_203715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 5].length) (baseStart_203715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203715 prefixEnd_203715 := by exact prefixLift 203715
  have htrace : WordTrace (prefixWord ++ tailWord_203715) baseStart_203715 baseEnd_203715 := by
    simpa [prefixWord, tailWord_203715, baseEnd_203715] using wordTrace_append hprefix tailTrace_203715
  have hstable : (prefixWord ++ tailWord_203715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203715).length < 2 ^ (prefixWord ++ tailWord_203715).sum := by decide
  have hdescent : baseEnd_203715 < baseStart_203715 := by decide
  rcases family_descends (prefixWord ++ tailWord_203715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203760 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 6]
def baseStart_203760 : Nat := 118140960795 + 203760 * 2 ^ 59
def prefixEnd_203760 : Nat := 4983230072969 + 3 ^ 40 * 203760 * 2
def baseEnd_203760 : Nat := 23250404035606227058429

theorem tailTrace_203760 : CollatzResearch.WordTrace tailWord_203760 prefixEnd_203760 23250404035606227058429 := by
  unfold tailWord_203760
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715868870909897141292367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4954491827879862855056489 3715868870909897141292367)
  ·
    refine ⟨5573803306364845711938551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3715868870909897141292367 5573803306364845711938551)
    ·
      refine ⟨8360704959547268567907827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5573803306364845711938551 8360704959547268567907827)
      ·
        refine ⟨12541057439320902851861741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360704959547268567907827 12541057439320902851861741)
        ·
          refine ⟨4702896539745338569448153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12541057439320902851861741 4702896539745338569448153)
          ·
            refine ⟨3527172404809003927086115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4702896539745338569448153 3527172404809003927086115)
            ·
              refine ⟨5290758607213505890629173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527172404809003927086115 5290758607213505890629173)
              ·
                refine ⟨496008619426266177246485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5290758607213505890629173 496008619426266177246485)
                ·
                  refine ⟨23250404035606227058429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 496008619426266177246485 23250404035606227058429)
                  ·
                    rfl

theorem cell22_203760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_203760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203760 prefixEnd_203760 := by exact prefixLift 203760
  have htrace : WordTrace (prefixWord ++ tailWord_203760) baseStart_203760 baseEnd_203760 := by
    simpa [prefixWord, tailWord_203760, baseEnd_203760] using wordTrace_append hprefix tailTrace_203760
  have hstable : (prefixWord ++ tailWord_203760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203760).length < 2 ^ (prefixWord ++ tailWord_203760).sum := by decide
  have hdescent : baseEnd_203760 < baseStart_203760 := by decide
  rcases family_descends (prefixWord ++ tailWord_203760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203777 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 6]
def baseStart_203777 : Nat := 118140960795 + 203777 * 2 ^ 59
def prefixEnd_203777 : Nat := 4983230072969 + 3 ^ 40 * 203777 * 2
def baseEnd_203777 : Nat := 23252343851412101166745

theorem tailTrace_203777 : CollatzResearch.WordTrace tailWord_203777 prefixEnd_203777 23252343851412101166745 := by
  unfold tailWord_203777
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432357782758206185953585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4954905188505470790635723 7432357782758206185953585)
  ·
    refine ⟨5574268337068654639465189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7432357782758206185953585 5574268337068654639465189)
    ·
      refine ⟨1045175313200372744899723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5574268337068654639465189 1045175313200372744899723)
      ·
        refine ⟨1567762969800559117349585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045175313200372744899723 1567762969800559117349585)
        ·
          refine ⟨1175822227350419338012189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1567762969800559117349585 1175822227350419338012189)
          ·
            refine ⟨440933335256407251754571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1175822227350419338012189 440933335256407251754571)
            ·
              refine ⟨661400002884610877631857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440933335256407251754571 661400002884610877631857)
              ·
                refine ⟨496050002163458158223893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661400002884610877631857 496050002163458158223893)
                ·
                  refine ⟨23252343851412101166745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 496050002163458158223893 23252343851412101166745)
                  ·
                    rfl

theorem cell22_203777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_203777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203777 prefixEnd_203777 := by exact prefixLift 203777
  have htrace : WordTrace (prefixWord ++ tailWord_203777) baseStart_203777 baseEnd_203777 := by
    simpa [prefixWord, tailWord_203777, baseEnd_203777] using wordTrace_append hprefix tailTrace_203777
  have hstable : (prefixWord ++ tailWord_203777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203777).length < 2 ^ (prefixWord ++ tailWord_203777).sum := by decide
  have hdescent : baseEnd_203777 < baseStart_203777 := by decide
  rcases family_descends (prefixWord ++ tailWord_203777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203809 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 4, 3]
def baseStart_203809 : Nat := 118140960795 + 203809 * 2 ^ 59
def prefixEnd_203809 : Nat := 4983230072969 + 3 ^ 40 * 203809 * 2
def baseEnd_203809 : Nat := 69767985808198886700137

theorem tailTrace_203809 : CollatzResearch.WordTrace tailWord_203809 prefixEnd_203809 69767985808198886700137 := by
  unfold tailWord_203809
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433524918642275651118481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4955683279094850434078987 7433524918642275651118481)
  ·
    refine ⟨5575143688981706738338861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7433524918642275651118481 5575143688981706738338861)
    ·
      refine ⟨2090678883368140026877073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5575143688981706738338861 2090678883368140026877073)
      ·
        refine ⟨1568009162526105020157805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2090678883368140026877073 1568009162526105020157805)
        ·
          refine ⟨588003435947289382559177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1568009162526105020157805 588003435947289382559177)
          ·
            refine ⟨441002576960467036919383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588003435947289382559177 441002576960467036919383)
            ·
              refine ⟨661503865440700555379075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441002576960467036919383 661503865440700555379075)
              ·
                refine ⟨992255798161050833068613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661503865440700555379075 992255798161050833068613)
                ·
                  refine ⟨186047962155197031200365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992255798161050833068613 186047962155197031200365)
                  ·
                    refine ⟨69767985808198886700137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186047962155197031200365 69767985808198886700137)
                    ·
                      rfl

theorem cell22_203809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_203809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203809 prefixEnd_203809 := by exact prefixLift 203809
  have htrace : WordTrace (prefixWord ++ tailWord_203809) baseStart_203809 baseEnd_203809 := by
    simpa [prefixWord, tailWord_203809, baseEnd_203809] using wordTrace_append hprefix tailTrace_203809
  have hstable : (prefixWord ++ tailWord_203809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203809).length < 2 ^ (prefixWord ++ tailWord_203809).sum := by decide
  have hdescent : baseEnd_203809 < baseStart_203809 := by decide
  rcases family_descends (prefixWord ++ tailWord_203809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203822 : List Nat := [4, 1, 3, 1, 1, 1, 2, 9]
def baseStart_203822 : Nat := 118140960795 + 203822 * 2 ^ 59
def prefixEnd_203822 : Nat := 4983230072969 + 3 ^ 40 * 203822 * 2
def baseEnd_203822 : Nat := 7752492885985687347233

theorem tailTrace_203822 : CollatzResearch.WordTrace tailWord_203822 prefixEnd_203822 7752492885985687347233 := by
  unfold tailWord_203822
  simp only [CollatzResearch.WordTrace]
  refine ⟨929249883449397358917715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4955999378396785914227813 929249883449397358917715)
  ·
    refine ⟨1393874825174096038376573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 929249883449397358917715 1393874825174096038376573)
    ·
      refine ⟨522703059440286014391215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1393874825174096038376573 522703059440286014391215)
      ·
        refine ⟨784054589160429021586823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522703059440286014391215 784054589160429021586823)
        ·
          refine ⟨1176081883740643532380235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784054589160429021586823 1176081883740643532380235)
          ·
            refine ⟨1764122825610965298570353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176081883740643532380235 1764122825610965298570353)
            ·
              refine ⟨1323092119208223973927765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764122825610965298570353 1323092119208223973927765)
              ·
                refine ⟨7752492885985687347233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1323092119208223973927765 7752492885985687347233)
                ·
                  rfl

theorem cell22_203822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_203822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203822 prefixEnd_203822 := by exact prefixLift 203822
  have htrace : WordTrace (prefixWord ++ tailWord_203822) baseStart_203822 baseEnd_203822 := by
    simpa [prefixWord, tailWord_203822, baseEnd_203822] using wordTrace_append hprefix tailTrace_203822
  have hstable : (prefixWord ++ tailWord_203822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203822).length < 2 ^ (prefixWord ++ tailWord_203822).sum := by decide
  have hdescent : baseEnd_203822 < baseStart_203822 := by decide
  rcases family_descends (prefixWord ++ tailWord_203822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203826 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_203826 : Nat := 118140960795 + 203826 * 2 ^ 59
def prefixEnd_203826 : Nat := 4983230072969 + 3 ^ 40 * 203826 * 2
def baseEnd_203826 : Nat := 69773805255616509025085

theorem tailTrace_203826 : CollatzResearch.WordTrace tailWord_203826 prefixEnd_203826 69773805255616509025085 := by
  unfold tailWord_203826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858536239895171888621833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4956096639720458369658221 1858536239895171888621833)
  ·
    refine ⟨1393902179921378916466375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1858536239895171888621833 1393902179921378916466375)
    ·
      refine ⟨2090853269882068374699563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393902179921378916466375 2090853269882068374699563)
      ·
        refine ⟨3136279904823102562049345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090853269882068374699563 3136279904823102562049345)
        ·
          refine ⟨2352209928617326921537009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136279904823102562049345 2352209928617326921537009)
          ·
            refine ⟨1764157446462995191152757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352209928617326921537009 1764157446462995191152757)
            ·
              refine ⟨165389760605905799170571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1764157446462995191152757 165389760605905799170571)
              ·
                refine ⟨248084640908858698755857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165389760605905799170571 248084640908858698755857)
                ·
                  refine ⟨186063480681644024066893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248084640908858698755857 186063480681644024066893)
                  ·
                    refine ⟨69773805255616509025085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186063480681644024066893 69773805255616509025085)
                    ·
                      rfl

theorem cell22_203826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_203826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203826 prefixEnd_203826 := by exact prefixLift 203826
  have htrace : WordTrace (prefixWord ++ tailWord_203826) baseStart_203826 baseEnd_203826 := by
    simpa [prefixWord, tailWord_203826, baseEnd_203826] using wordTrace_append hprefix tailTrace_203826
  have hstable : (prefixWord ++ tailWord_203826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203826).length < 2 ^ (prefixWord ++ tailWord_203826).sum := by decide
  have hdescent : baseEnd_203826 < baseStart_203826 := by decide
  rcases family_descends (prefixWord ++ tailWord_203826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203946 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_203946 : Nat := 118140960795 + 203946 * 2 ^ 59
def prefixEnd_203946 : Nat := 4983230072969 + 3 ^ 40 * 203946 * 2
def baseEnd_203946 : Nat := 23271627902658732008239

theorem tailTrace_203946 : CollatzResearch.WordTrace tailWord_203946 prefixEnd_203946 23271627902658732008239 := by
  unfold tailWord_203946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859630429786487012213923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4959014479430632032570461 1859630429786487012213923)
  ·
    refine ⟨2789445644679730518320885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859630429786487012213923 2789445644679730518320885)
    ·
      refine ⟨261510529188724736092583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2789445644679730518320885 261510529188724736092583)
      ·
        refine ⟨392265793783087104138875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261510529188724736092583 392265793783087104138875)
        ·
          refine ⟨588398690674630656208313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392265793783087104138875 588398690674630656208313)
          ·
            refine ⟨441299018005972992156235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588398690674630656208313 441299018005972992156235)
            ·
              refine ⟨661948527008959488234353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441299018005972992156235 661948527008959488234353)
              ·
                refine ⟨496461395256719616175765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661948527008959488234353 496461395256719616175765)
                ·
                  refine ⟨23271627902658732008239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 496461395256719616175765 23271627902658732008239)
                  ·
                    rfl

theorem cell22_203946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_203946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203946 prefixEnd_203946 := by exact prefixLift 203946
  have htrace : WordTrace (prefixWord ++ tailWord_203946) baseStart_203946 baseEnd_203946 := by
    simpa [prefixWord, tailWord_203946, baseEnd_203946] using wordTrace_append hprefix tailTrace_203946
  have hstable : (prefixWord ++ tailWord_203946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203946).length < 2 ^ (prefixWord ++ tailWord_203946).sum := by decide
  have hdescent : baseEnd_203946 < baseStart_203946 := by decide
  rcases family_descends (prefixWord ++ tailWord_203946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_203978 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_203978 : Nat := 118140960795 + 203978 * 2 ^ 59
def prefixEnd_203978 : Nat := 4983230072969 + 3 ^ 40 * 203978 * 2
def baseEnd_203978 : Nat := 69825837961938779224619

theorem tailTrace_203978 : CollatzResearch.WordTrace tailWord_203978 prefixEnd_203978 69825837961938779224619 := by
  unfold tailWord_203978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859922213757504378505147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4959792570020011676013725 1859922213757504378505147)
  ·
    refine ⟨2789883320636256567757721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859922213757504378505147 2789883320636256567757721)
    ·
      refine ⟨2092412490477192425818291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2789883320636256567757721 2092412490477192425818291)
      ·
        refine ⟨3138618735715788638727437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092412490477192425818291 3138618735715788638727437)
        ·
          refine ⟨1176982025893420739522789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3138618735715788638727437 1176982025893420739522789)
          ·
            refine ⟨220684129855016388660523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1176982025893420739522789 220684129855016388660523)
            ·
              refine ⟨331026194782524582990785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220684129855016388660523 331026194782524582990785)
              ·
                refine ⟨248269646086893437243089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331026194782524582990785 248269646086893437243089)
                ·
                  refine ⟨186202234565170077932317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248269646086893437243089 186202234565170077932317)
                  ·
                    refine ⟨69825837961938779224619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186202234565170077932317 69825837961938779224619)
                    ·
                      rfl

theorem cell22_203978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_203978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_203978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_203978 prefixEnd_203978 := by exact prefixLift 203978
  have htrace : WordTrace (prefixWord ++ tailWord_203978) baseStart_203978 baseEnd_203978 := by
    simpa [prefixWord, tailWord_203978, baseEnd_203978] using wordTrace_append hprefix tailTrace_203978
  have hstable : (prefixWord ++ tailWord_203978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_203978).length < 2 ^ (prefixWord ++ tailWord_203978).sum := by decide
  have hdescent : baseEnd_203978 < baseStart_203978 := by decide
  rcases family_descends (prefixWord ++ tailWord_203978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204040 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 3, 3]
def baseStart_204040 : Nat := 118140960795 + 204040 * 2 ^ 59
def prefixEnd_204040 : Nat := 4983230072969 + 3 ^ 40 * 204040 * 2
def baseEnd_204040 : Nat := 69847061828991284174429

theorem tailTrace_204040 : CollatzResearch.WordTrace tailWord_204040 prefixEnd_204040 69847061828991284174429 := by
  unfold tailWord_204040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720975090402701051388787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4961300120536934735185049 3720975090402701051388787)
  ·
    refine ⟨5581462635604051577083181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3720975090402701051388787 5581462635604051577083181)
    ·
      refine ⟨2093048488351519341406193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5581462635604051577083181 2093048488351519341406193)
      ·
        refine ⟨1569786366263639506054645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093048488351519341406193 1569786366263639506054645)
        ·
          refine ⟨147167471837216203692623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1569786366263639506054645 147167471837216203692623)
          ·
            refine ⟨220751207755824305538935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147167471837216203692623 220751207755824305538935)
            ·
              refine ⟨331126811633736458308403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220751207755824305538935 331126811633736458308403)
              ·
                refine ⟨496690217450604687462605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331126811633736458308403 496690217450604687462605)
                ·
                  refine ⟨186258831543976757798477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496690217450604687462605 186258831543976757798477)
                  ·
                    refine ⟨69847061828991284174429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186258831543976757798477 69847061828991284174429)
                    ·
                      rfl

theorem cell22_204040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_204040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204040 prefixEnd_204040 := by exact prefixLift 204040
  have htrace : WordTrace (prefixWord ++ tailWord_204040) baseStart_204040 baseEnd_204040 := by
    simpa [prefixWord, tailWord_204040, baseEnd_204040] using wordTrace_append hprefix tailTrace_204040
  have hstable : (prefixWord ++ tailWord_204040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204040).length < 2 ^ (prefixWord ++ tailWord_204040).sum := by decide
  have hdescent : baseEnd_204040 < baseStart_204040 := by decide
  rcases family_descends (prefixWord ++ tailWord_204040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204049 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_204049 : Nat := 118140960795 + 204049 * 2 ^ 59
def prefixEnd_204049 : Nat := 4983230072969 + 3 ^ 40 * 204049 * 2
def baseEnd_204049 : Nat := 69850142712918260699401

theorem tailTrace_204049 : CollatzResearch.WordTrace tailWord_204049 prefixEnd_204049 69850142712918260699401 := by
  unfold tailWord_204049
  simp only [CollatzResearch.WordTrace]
  refine ⟨7442278437772796639855201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4961518958515197759903467 7442278437772796639855201)
  ·
    refine ⟨5581708828329597479891401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7442278437772796639855201 5581708828329597479891401)
    ·
      refine ⟨4186281621247198109918551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5581708828329597479891401 4186281621247198109918551)
      ·
        refine ⟨6279422431870797164877827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186281621247198109918551 6279422431870797164877827)
        ·
          refine ⟨9419133647806195747316741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279422431870797164877827 9419133647806195747316741)
          ·
            refine ⟨1766087558963661702621889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9419133647806195747316741 1766087558963661702621889)
            ·
              refine ⟨1324565669222746276966417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766087558963661702621889 1324565669222746276966417)
              ·
                refine ⟨993424251917059707724813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324565669222746276966417 993424251917059707724813)
                ·
                  refine ⟨372534094468897390396805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993424251917059707724813 372534094468897390396805)
                  ·
                    refine ⟨69850142712918260699401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372534094468897390396805 69850142712918260699401)
                    ·
                      rfl

theorem cell22_204049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_204049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204049 prefixEnd_204049 := by exact prefixLift 204049
  have htrace : WordTrace (prefixWord ++ tailWord_204049) baseStart_204049 baseEnd_204049 := by
    simpa [prefixWord, tailWord_204049, baseEnd_204049] using wordTrace_append hprefix tailTrace_204049
  have hstable : (prefixWord ++ tailWord_204049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204049).length < 2 ^ (prefixWord ++ tailWord_204049).sum := by decide
  have hdescent : baseEnd_204049 < baseStart_204049 := by decide
  rcases family_descends (prefixWord ++ tailWord_204049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204083 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 1, 4]
def baseStart_204083 : Nat := 118140960795 + 204083 * 2 ^ 59
def prefixEnd_204083 : Nat := 4983230072969 + 3 ^ 40 * 204083 * 2
def baseEnd_204083 : Nat := 69861781607753505349297

theorem tailTrace_204083 : CollatzResearch.WordTrace tailWord_204083 prefixEnd_204083 69861781607753505349297 := by
  unfold tailWord_204083
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443518519649620446592903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4962345679766413631061935 7443518519649620446592903)
  ·
    refine ⟨11165277779474430669889355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7443518519649620446592903 11165277779474430669889355)
    ·
      refine ⟨16747916669211646004834033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11165277779474430669889355 16747916669211646004834033)
      ·
        refine ⟨12560937501908734503625525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16747916669211646004834033 12560937501908734503625525)
        ·
          refine ⟨1177587890803943859714893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12560937501908734503625525 1177587890803943859714893)
          ·
            refine ⟨441595459051478947393085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1177587890803943859714893 441595459051478947393085)
            ·
              refine ⟨165598297144304605272407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441595459051478947393085 165598297144304605272407)
              ·
                refine ⟨248397445716456907908611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165598297144304605272407 248397445716456907908611)
                ·
                  refine ⟨372596168574685361862917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248397445716456907908611 372596168574685361862917)
                  ·
                    refine ⟨69861781607753505349297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372596168574685361862917 69861781607753505349297)
                    ·
                      rfl

theorem cell22_204083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 4].length) (baseStart_204083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204083 prefixEnd_204083 := by exact prefixLift 204083
  have htrace : WordTrace (prefixWord ++ tailWord_204083) baseStart_204083 baseEnd_204083 := by
    simpa [prefixWord, tailWord_204083, baseEnd_204083] using wordTrace_append hprefix tailTrace_204083
  have hstable : (prefixWord ++ tailWord_204083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204083).length < 2 ^ (prefixWord ++ tailWord_204083).sum := by decide
  have hdescent : baseEnd_204083 < baseStart_204083 := by decide
  rcases family_descends (prefixWord ++ tailWord_204083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204128 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 2, 4]
def baseStart_204128 : Nat := 118140960795 + 204128 * 2 ^ 59
def prefixEnd_204128 : Nat := 4983230072969 + 3 ^ 40 * 204128 * 2
def baseEnd_204128 : Nat := 69877186027388387974159

theorem tailTrace_204128 : CollatzResearch.WordTrace tailWord_204128 prefixEnd_204128 69877186027388387974159 := by
  unfold tailWord_204128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722579902243296565990519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4963439869657728754654025 3722579902243296565990519)
  ·
    refine ⟨5583869853364944848985779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3722579902243296565990519 5583869853364944848985779)
    ·
      refine ⟨8375804780047417273478669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5583869853364944848985779 8375804780047417273478669)
      ·
        refine ⟨3140926792517781477554501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8375804780047417273478669 3140926792517781477554501)
        ·
          refine ⟨588923773597084027041469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3140926792517781477554501 588923773597084027041469)
          ·
            refine ⟨220846415098906510140551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 588923773597084027041469 220846415098906510140551)
            ·
              refine ⟨331269622648359765210827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220846415098906510140551 331269622648359765210827)
              ·
                refine ⟨496904433972539647816241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331269622648359765210827 496904433972539647816241)
                ·
                  refine ⟨372678325479404735862181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496904433972539647816241 372678325479404735862181)
                  ·
                    refine ⟨69877186027388387974159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372678325479404735862181 69877186027388387974159)
                    ·
                      rfl

theorem cell22_204128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_204128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204128 prefixEnd_204128 := by exact prefixLift 204128
  have htrace : WordTrace (prefixWord ++ tailWord_204128) baseStart_204128 baseEnd_204128 := by
    simpa [prefixWord, tailWord_204128, baseEnd_204128] using wordTrace_append hprefix tailTrace_204128
  have hstable : (prefixWord ++ tailWord_204128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204128).length < 2 ^ (prefixWord ++ tailWord_204128).sum := by decide
  have hdescent : baseEnd_204128 < baseStart_204128 := by decide
  rcases family_descends (prefixWord ++ tailWord_204128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204154 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_204154 : Nat := 118140960795 + 204154 * 2 ^ 59
def prefixEnd_204154 : Nat := 4983230072969 + 3 ^ 40 * 204154 * 2
def baseEnd_204154 : Nat := 23295362119577662274693

theorem tailTrace_204154 : CollatzResearch.WordTrace tailWord_204154 prefixEnd_204154 23295362119577662274693 := by
  unfold tailWord_204154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861527025598099893106879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4964072068261599714951677 1861527025598099893106879)
  ·
    refine ⟨2792290538397149839660319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1861527025598099893106879 2792290538397149839660319)
    ·
      refine ⟨4188435807595724759490479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2792290538397149839660319 4188435807595724759490479)
      ·
        refine ⟨6282653711393587139235719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4188435807595724759490479 6282653711393587139235719)
        ·
          refine ⟨9423980567090380708853579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6282653711393587139235719 9423980567090380708853579)
          ·
            refine ⟨14135970850635571063280369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9423980567090380708853579 14135970850635571063280369)
            ·
              refine ⟨10601978137976678297460277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14135970850635571063280369 10601978137976678297460277)
              ·
                refine ⟨993935450435313590386901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10601978137976678297460277 993935450435313590386901)
                ·
                  refine ⟨23295362119577662274693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 993935450435313590386901 23295362119577662274693)
                  ·
                    rfl

theorem cell22_204154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_204154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204154 prefixEnd_204154 := by exact prefixLift 204154
  have htrace : WordTrace (prefixWord ++ tailWord_204154) baseStart_204154 baseEnd_204154 := by
    simpa [prefixWord, tailWord_204154, baseEnd_204154] using wordTrace_append hprefix tailTrace_204154
  have hstable : (prefixWord ++ tailWord_204154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204154).length < 2 ^ (prefixWord ++ tailWord_204154).sum := by decide
  have hdescent : baseEnd_204154 < baseStart_204154 := by decide
  rcases family_descends (prefixWord ++ tailWord_204154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204216 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 6]
def baseStart_204216 : Nat := 118140960795 + 204216 * 2 ^ 59
def prefixEnd_204216 : Nat := 4983230072969 + 3 ^ 40 * 204216 * 2
def baseEnd_204216 : Nat := 23302436741928497257963

theorem tailTrace_204216 : CollatzResearch.WordTrace tailWord_204216 prefixEnd_204216 23302436741928497257963 := by
  unfold tailWord_204216
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724184714083892080592251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4965579618778522774123001 3724184714083892080592251)
  ·
    refine ⟨5586277071125838120888377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3724184714083892080592251 5586277071125838120888377)
    ·
      refine ⟨4189707803344378590666283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5586277071125838120888377 4189707803344378590666283)
      ·
        refine ⟨6284561705016567885999425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189707803344378590666283 6284561705016567885999425)
        ·
          refine ⟨4713421278762425914499569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6284561705016567885999425 4713421278762425914499569)
          ·
            refine ⟨3535065959071819435874677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4713421278762425914499569 3535065959071819435874677)
            ·
              refine ⟨331412433662983072113251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3535065959071819435874677 331412433662983072113251)
              ·
                refine ⟨497118650494474608169877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331412433662983072113251 497118650494474608169877)
                ·
                  refine ⟨23302436741928497257963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 497118650494474608169877 23302436741928497257963)
                  ·
                    rfl

theorem cell22_204216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_204216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204216 prefixEnd_204216 := by exact prefixLift 204216
  have htrace : WordTrace (prefixWord ++ tailWord_204216) baseStart_204216 baseEnd_204216 := by
    simpa [prefixWord, tailWord_204216, baseEnd_204216] using wordTrace_append hprefix tailTrace_204216
  have hstable : (prefixWord ++ tailWord_204216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204216).length < 2 ^ (prefixWord ++ tailWord_204216).sum := by decide
  have hdescent : baseEnd_204216 < baseStart_204216 := by decide
  rcases family_descends (prefixWord ++ tailWord_204216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204231 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 1, 5]
def baseStart_204231 : Nat := 118140960795 + 204231 * 2 ^ 59
def prefixEnd_204231 : Nat := 4983230072969 + 3 ^ 40 * 204231 * 2
def baseEnd_204231 : Nat := 69912445032330452648843

theorem tailTrace_204231 : CollatzResearch.WordTrace tailWord_204231 prefixEnd_204231 69912445032330452648843 := by
  unfold tailWord_204231
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448916523113441722980547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4965944348742294481987031 7448916523113441722980547)
  ·
    refine ⟨11173374784670162584470821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7448916523113441722980547 11173374784670162584470821)
    ·
      refine ⟨2095007772125655484588279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11173374784670162584470821 2095007772125655484588279)
      ·
        refine ⟨3142511658188483226882419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095007772125655484588279 3142511658188483226882419)
        ·
          refine ⟨4713767487282724840323629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142511658188483226882419 4713767487282724840323629)
          ·
            refine ⟨1767662807731021815121361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4713767487282724840323629 1767662807731021815121361)
            ·
              refine ⟨1325747105798266361341021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767662807731021815121361 1325747105798266361341021)
              ·
                refine ⟨497155164674349885502883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1325747105798266361341021 497155164674349885502883)
                ·
                  refine ⟨745732747011524828254325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497155164674349885502883 745732747011524828254325)
                  ·
                    refine ⟨69912445032330452648843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 745732747011524828254325 69912445032330452648843)
                    ·
                      rfl

theorem cell22_204231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_204231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204231 prefixEnd_204231 := by exact prefixLift 204231
  have htrace : WordTrace (prefixWord ++ tailWord_204231) baseStart_204231 baseEnd_204231 := by
    simpa [prefixWord, tailWord_204231, baseEnd_204231] using wordTrace_append hprefix tailTrace_204231
  have hstable : (prefixWord ++ tailWord_204231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204231).length < 2 ^ (prefixWord ++ tailWord_204231).sum := by decide
  have hdescent : baseEnd_204231 < baseStart_204231 := by decide
  rcases family_descends (prefixWord ++ tailWord_204231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204261 : List Nat := [1, 3, 1, 5, 1, 11]
def baseStart_204261 : Nat := 118140960795 + 204261 * 2 ^ 59
def prefixEnd_204261 : Nat := 4983230072969 + 3 ^ 40 * 204261 * 2
def baseEnd_204261 : Nat := 863243390684202153071

theorem tailTrace_204261 : CollatzResearch.WordTrace tailWord_204261 prefixEnd_204261 863243390684202153071 := by
  unfold tailWord_204261
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450010713004756846572637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4966673808669837897715091 7450010713004756846572637)
  ·
    refine ⟨2793754017376783817464739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7450010713004756846572637 2793754017376783817464739)
    ·
      refine ⟨4190631026065175726197109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2793754017376783817464739 4190631026065175726197109)
      ·
        refine ⟨392871658693610224330979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4190631026065175726197109 392871658693610224330979)
        ·
          refine ⟨589307488040415336496469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392871658693610224330979 589307488040415336496469)
          ·
            refine ⟨863243390684202153071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 589307488040415336496469 863243390684202153071)
            ·
              rfl

theorem cell22_204261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 11].length) (baseStart_204261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204261 prefixEnd_204261 := by exact prefixLift 204261
  have htrace : WordTrace (prefixWord ++ tailWord_204261) baseStart_204261 baseEnd_204261 := by
    simpa [prefixWord, tailWord_204261, baseEnd_204261] using wordTrace_append hprefix tailTrace_204261
  have hstable : (prefixWord ++ tailWord_204261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204261).length < 2 ^ (prefixWord ++ tailWord_204261).sum := by decide
  have hdescent : baseEnd_204261 < baseStart_204261 := by decide
  rcases family_descends (prefixWord ++ tailWord_204261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204263 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 2, 4]
def baseStart_204263 : Nat := 118140960795 + 204263 * 2 ^ 59
def prefixEnd_204263 : Nat := 4983230072969 + 3 ^ 40 * 204263 * 2
def baseEnd_204263 : Nat := 69923399286293035848745

theorem tailTrace_204263 : CollatzResearch.WordTrace tailWord_204263 prefixEnd_204263 69923399286293035848745 := by
  unfold tailWord_204263
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450083658997511188145443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4966722439331674125430295 7450083658997511188145443)
  ·
    refine ⟨11175125488496266782218165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7450083658997511188145443 11175125488496266782218165)
    ·
      refine ⟨1047668014546525010832953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11175125488496266782218165 1047668014546525010832953)
      ·
        refine ⟨785751010909893758124715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1047668014546525010832953 785751010909893758124715)
        ·
          refine ⟨1178626516364840637187073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785751010909893758124715 1178626516364840637187073)
          ·
            refine ⟨883969887273630477890305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178626516364840637187073 883969887273630477890305)
            ·
              refine ⟨662977415455222858417729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883969887273630477890305 662977415455222858417729)
              ·
                refine ⟨497233061591417143813297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662977415455222858417729 497233061591417143813297)
                ·
                  refine ⟨372924796193562857859973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497233061591417143813297 372924796193562857859973)
                  ·
                    refine ⟨69923399286293035848745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372924796193562857859973 69923399286293035848745)
                    ·
                      rfl

theorem cell22_204263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_204263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204263 prefixEnd_204263 := by exact prefixLift 204263
  have htrace : WordTrace (prefixWord ++ tailWord_204263) baseStart_204263 baseEnd_204263 := by
    simpa [prefixWord, tailWord_204263, baseEnd_204263] using wordTrace_append hprefix tailTrace_204263
  have hstable : (prefixWord ++ tailWord_204263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204263).length < 2 ^ (prefixWord ++ tailWord_204263).sum := by decide
  have hdescent : baseEnd_204263 < baseStart_204263 := by decide
  rcases family_descends (prefixWord ++ tailWord_204263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204278 : List Nat := [5, 1, 1, 1, 2, 2, 3, 7]
def baseStart_204278 : Nat := 118140960795 + 204278 * 2 ^ 59
def prefixEnd_204278 : Nat := 4983230072969 + 3 ^ 40 * 204278 * 2
def baseEnd_204278 : Nat := 7769837121426444080411

theorem tailTrace_204278 : CollatzResearch.WordTrace tailWord_204278 prefixEnd_204278 7769837121426444080411 := by
  unfold tailWord_204278
  simp only [CollatzResearch.WordTrace]
  refine ⟨465664422121448046871343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4967087169295445833294325 465664422121448046871343)
  ·
    refine ⟨698496633182172070307015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 465664422121448046871343 698496633182172070307015)
    ·
      refine ⟨1047744949773258105460523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698496633182172070307015 1047744949773258105460523)
      ·
        refine ⟨1571617424659887158190785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047744949773258105460523 1571617424659887158190785)
        ·
          refine ⟨1178713068494915368643089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571617424659887158190785 1178713068494915368643089)
          ·
            refine ⟨884034801371186526482317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178713068494915368643089 884034801371186526482317)
            ·
              refine ⟨331513050514194947430869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884034801371186526482317 331513050514194947430869)
              ·
                refine ⟨7769837121426444080411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 331513050514194947430869 7769837121426444080411)
                ·
                  rfl

theorem cell22_204278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_204278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204278 prefixEnd_204278 := by exact prefixLift 204278
  have htrace : WordTrace (prefixWord ++ tailWord_204278) baseStart_204278 baseEnd_204278 := by
    simpa [prefixWord, tailWord_204278, baseEnd_204278] using wordTrace_append hprefix tailTrace_204278
  have hstable : (prefixWord ++ tailWord_204278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204278).length < 2 ^ (prefixWord ++ tailWord_204278).sum := by decide
  have hdescent : baseEnd_204278 < baseStart_204278 := by decide
  rcases family_descends (prefixWord ++ tailWord_204278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204323 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 7]
def baseStart_204323 : Nat := 118140960795 + 204323 * 2 ^ 59
def prefixEnd_204323 : Nat := 4983230072969 + 3 ^ 40 * 204323 * 2
def baseEnd_204323 : Nat := 23314646170824293116187

theorem tailTrace_204323 : CollatzResearch.WordTrace tailWord_204323 prefixEnd_204323 23314646170824293116187 := by
  unfold tailWord_204323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452272038780141435329623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4968181359186760956886415 7452272038780141435329623)
  ·
    refine ⟨11178408058170212152994435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452272038780141435329623 11178408058170212152994435)
    ·
      refine ⟨16767612087255318229491653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11178408058170212152994435 16767612087255318229491653)
      ·
        refine ⟨3143927266360372168029685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16767612087255318229491653 3143927266360372168029685)
        ·
          refine ⟨294743181221284890752783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3143927266360372168029685 294743181221284890752783)
          ·
            refine ⟨442114771831927336129175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294743181221284890752783 442114771831927336129175)
            ·
              refine ⟨663172157747891004193763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442114771831927336129175 663172157747891004193763)
              ·
                refine ⟨994758236621836506290645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663172157747891004193763 994758236621836506290645)
                ·
                  refine ⟨23314646170824293116187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 994758236621836506290645 23314646170824293116187)
                  ·
                    rfl

theorem cell22_204323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 7].length) (baseStart_204323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204323 prefixEnd_204323 := by exact prefixLift 204323
  have htrace : WordTrace (prefixWord ++ tailWord_204323) baseStart_204323 baseEnd_204323 := by
    simpa [prefixWord, tailWord_204323, baseEnd_204323] using wordTrace_append hprefix tailTrace_204323
  have hstable : (prefixWord ++ tailWord_204323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204323).length < 2 ^ (prefixWord ++ tailWord_204323).sum := by decide
  have hdescent : baseEnd_204323 < baseStart_204323 := by decide
  rcases family_descends (prefixWord ++ tailWord_204323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204370 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_204370 : Nat := 118140960795 + 204370 * 2 ^ 59
def prefixEnd_204370 : Nat := 4983230072969 + 3 ^ 40 * 204370 * 2
def baseEnd_204370 : Nat := 69960027572980423423417

theorem tailTrace_204370 : CollatzResearch.WordTrace tailWord_204370 prefixEnd_204370 69960027572980423423417 := by
  unfold tailWord_204370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863496567402467115572641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4969324179739912308193709 1863496567402467115572641)
  ·
    refine ⟨1397622425551850336679481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1863496567402467115572641 1397622425551850336679481)
    ·
      refine ⟨1048216819163887752509611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397622425551850336679481 1048216819163887752509611)
      ·
        refine ⟨1572325228745831628764417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048216819163887752509611 1572325228745831628764417)
        ·
          refine ⟨1179243921559373721573313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572325228745831628764417 1179243921559373721573313)
          ·
            refine ⟨884432941169530291179985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179243921559373721573313 884432941169530291179985)
            ·
              refine ⟨663324705877147718384989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884432941169530291179985 663324705877147718384989)
              ·
                refine ⟨248746764703930394394371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663324705877147718384989 248746764703930394394371)
                ·
                  refine ⟨373120147055895591591557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248746764703930394394371 373120147055895591591557)
                  ·
                    refine ⟨69960027572980423423417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373120147055895591591557 69960027572980423423417)
                    ·
                      rfl

theorem cell22_204370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_204370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204370 prefixEnd_204370 := by exact prefixLift 204370
  have htrace : WordTrace (prefixWord ++ tailWord_204370) baseStart_204370 baseEnd_204370 := by
    simpa [prefixWord, tailWord_204370, baseEnd_204370] using wordTrace_append hprefix tailTrace_204370
  have hstable : (prefixWord ++ tailWord_204370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204370).length < 2 ^ (prefixWord ++ tailWord_204370).sum := by decide
  have hdescent : baseEnd_204370 < baseStart_204370 := by decide
  rcases family_descends (prefixWord ++ tailWord_204370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204413 : List Nat := [1, 4, 1, 1, 4, 1, 2, 8]
def baseStart_204413 : Nat := 118140960795 + 204413 * 2 ^ 59
def prefixEnd_204413 : Nat := 4983230072969 + 3 ^ 40 * 204413 * 2
def baseEnd_204413 : Nat := 7774971927971404955365

theorem tailTrace_204413 : CollatzResearch.WordTrace tailWord_204413 prefixEnd_204413 7774971927971404955365 := by
  unfold tailWord_204413
  simp only [CollatzResearch.WordTrace]
  refine ⟨7455554608454086806105893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4970369738969391204070595 7455554608454086806105893)
  ·
    refine ⟨1397916489085141276144855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7455554608454086806105893 1397916489085141276144855)
    ·
      refine ⟨2096874733627711914217283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397916489085141276144855 2096874733627711914217283)
      ·
        refine ⟨3145312100441567871325925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096874733627711914217283 3145312100441567871325925)
        ·
          refine ⟨589746018832793975873611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3145312100441567871325925 589746018832793975873611)
          ·
            refine ⟨884619028249190963810417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589746018832793975873611 884619028249190963810417)
            ·
              refine ⟨663464271186893222857813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884619028249190963810417 663464271186893222857813)
              ·
                refine ⟨7774971927971404955365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 663464271186893222857813 7774971927971404955365)
                ·
                  rfl

theorem cell22_204413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 8].length) (baseStart_204413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204413 prefixEnd_204413 := by exact prefixLift 204413
  have htrace : WordTrace (prefixWord ++ tailWord_204413) baseStart_204413 baseEnd_204413 := by
    simpa [prefixWord, tailWord_204413, baseEnd_204413] using wordTrace_append hprefix tailTrace_204413
  have hstable : (prefixWord ++ tailWord_204413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204413).length < 2 ^ (prefixWord ++ tailWord_204413).sum := by decide
  have hdescent : baseEnd_204413 < baseStart_204413 := by decide
  rcases family_descends (prefixWord ++ tailWord_204413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204434 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_204434 : Nat := 118140960795 + 204434 * 2 ^ 59
def prefixEnd_204434 : Nat := 4983230072969 + 3 ^ 40 * 204434 * 2
def baseEnd_204434 : Nat := 69981936080905589823221

theorem tailTrace_204434 : CollatzResearch.WordTrace tailWord_204434 prefixEnd_204434 69981936080905589823221 := by
  unfold tailWord_204434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864080135344501848155089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4970880360918671595080237 1864080135344501848155089)
  ·
    refine ⟨1398060101508376386116317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1864080135344501848155089 1398060101508376386116317)
    ·
      refine ⟨524272538065641144793619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1398060101508376386116317 524272538065641144793619)
      ·
        refine ⟨786408807098461717190429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524272538065641144793619 786408807098461717190429)
        ·
          refine ⟨294903302661923143946411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 786408807098461717190429 294903302661923143946411)
          ·
            refine ⟨442354953992884715919617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294903302661923143946411 442354953992884715919617)
            ·
              refine ⟨331766215494663536939713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442354953992884715919617 331766215494663536939713)
              ·
                refine ⟨248824661620997652704785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331766215494663536939713 248824661620997652704785)
                ·
                  refine ⟨186618496215748239528589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248824661620997652704785 186618496215748239528589)
                  ·
                    refine ⟨69981936080905589823221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186618496215748239528589 69981936080905589823221)
                    ·
                      rfl

theorem cell22_204434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_204434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204434 prefixEnd_204434 := by exact prefixLift 204434
  have htrace : WordTrace (prefixWord ++ tailWord_204434) baseStart_204434 baseEnd_204434 := by
    simpa [prefixWord, tailWord_204434, baseEnd_204434] using wordTrace_append hprefix tailTrace_204434
  have hstable : (prefixWord ++ tailWord_204434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204434).length < 2 ^ (prefixWord ++ tailWord_204434).sum := by decide
  have hdescent : baseEnd_204434 < baseStart_204434 := by decide
  rcases family_descends (prefixWord ++ tailWord_204434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204436 : List Nat := [2, 4, 2, 2, 2, 2, 2, 2, 4]
def baseStart_204436 : Nat := 118140960795 + 204436 * 2 ^ 59
def prefixEnd_204436 : Nat := 4983230072969 + 3 ^ 40 * 204436 * 2
def baseEnd_204436 : Nat := 23327540240592750424405

theorem tailTrace_204436 : CollatzResearch.WordTrace tailWord_204436 prefixEnd_204436 23327540240592750424405 := by
  unfold tailWord_204436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728196743685380867096581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4970928991580507822795441 3728196743685380867096581)
  ·
    refine ⟨699036889441008912580609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3728196743685380867096581 699036889441008912580609)
    ·
      refine ⟨524277667080756684435457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 699036889441008912580609 524277667080756684435457)
      ·
        refine ⟨393208250310567513326593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524277667080756684435457 393208250310567513326593)
        ·
          refine ⟨294906187732925634994945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393208250310567513326593 294906187732925634994945)
          ·
            refine ⟨221179640799694226246209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294906187732925634994945 221179640799694226246209)
            ·
              refine ⟨165884730599770669684657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221179640799694226246209 165884730599770669684657)
              ·
                refine ⟨124413547949828002263493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165884730599770669684657 124413547949828002263493)
                ·
                  refine ⟨23327540240592750424405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124413547949828002263493 23327540240592750424405)
                  ·
                    rfl

theorem cell22_204436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_204436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204436 prefixEnd_204436 := by exact prefixLift 204436
  have htrace : WordTrace (prefixWord ++ tailWord_204436) baseStart_204436 baseEnd_204436 := by
    simpa [prefixWord, tailWord_204436, baseEnd_204436] using wordTrace_append hprefix tailTrace_204436
  have hstable : (prefixWord ++ tailWord_204436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204436).length < 2 ^ (prefixWord ++ tailWord_204436).sum := by decide
  have hdescent : baseEnd_204436 < baseStart_204436 := by decide
  rcases family_descends (prefixWord ++ tailWord_204436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_204445 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_204445 : Nat := 118140960795 + 204445 * 2 ^ 59
def prefixEnd_204445 : Nat := 4983230072969 + 3 ^ 40 * 204445 * 2
def baseEnd_204445 : Nat := 69985701605705227798187

theorem tailTrace_204445 : CollatzResearch.WordTrace tailWord_204445 prefixEnd_204445 69985701605705227798187 := by
  unfold tailWord_204445
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456721744338156271270789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4971147829558770847513859 7456721744338156271270789)
  ·
    refine ⟨1398135327063404300863273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7456721744338156271270789 1398135327063404300863273)
    ·
      refine ⟨1048601495297553225647455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1398135327063404300863273 1048601495297553225647455)
      ·
        refine ⟨1572902242946329838471183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048601495297553225647455 1572902242946329838471183)
        ·
          refine ⟨2359353364419494757706775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572902242946329838471183 2359353364419494757706775)
          ·
            refine ⟨3539030046629242136560163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359353364419494757706775 3539030046629242136560163)
            ·
              refine ⟨5308545069943863204840245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539030046629242136560163 5308545069943863204840245)
              ·
                refine ⟨497676100307237175453773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5308545069943863204840245 497676100307237175453773)
                ·
                  refine ⟨186628537615213940795165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497676100307237175453773 186628537615213940795165)
                  ·
                    refine ⟨69985701605705227798187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186628537615213940795165 69985701605705227798187)
                    ·
                      rfl

theorem cell22_204445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_204445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_204445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_204445 prefixEnd_204445 := by exact prefixLift 204445
  have htrace : WordTrace (prefixWord ++ tailWord_204445) baseStart_204445 baseEnd_204445 := by
    simpa [prefixWord, tailWord_204445, baseEnd_204445] using wordTrace_append hprefix tailTrace_204445
  have hstable : (prefixWord ++ tailWord_204445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_204445).length < 2 ^ (prefixWord ++ tailWord_204445).sum := by decide
  have hdescent : baseEnd_204445 < baseStart_204445 := by decide
  rcases family_descends (prefixWord ++ tailWord_204445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
