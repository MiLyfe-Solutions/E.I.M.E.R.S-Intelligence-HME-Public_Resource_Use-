import V185TrunkScan21Chunk088

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1080235 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 8]
def baseStart_1080235 : Nat := 118140960795 + 1080235 * 2 ^ 59
def prefixEnd_1080235 : Nat := 4983230072969 + 3 ^ 40 * 1080235 * 2
def baseEnd_1080235 : Nat := 246524344359860581908709

theorem tailTrace_1080235 : CollatzResearch.WordTrace tailWord_1080235 prefixEnd_1080235 246524344359860581908709 := by
  unfold tailWord_1080235
  simp only [CollatzResearch.WordTrace]
  refine ⟨39399407241500559295154159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26266271494333706196769439 39399407241500559295154159)
  ·
    refine ⟨59099110862250838942731239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39399407241500559295154159 59099110862250838942731239)
    ·
      refine ⟨88648666293376258414096859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59099110862250838942731239 88648666293376258414096859)
      ·
        refine ⟨132972999440064387621145289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88648666293376258414096859 132972999440064387621145289)
        ·
          refine ⟨99729749580048290715858967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132972999440064387621145289 99729749580048290715858967)
          ·
            refine ⟨149594624370072436073788451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99729749580048290715858967 149594624370072436073788451)
            ·
              refine ⟨224391936555108654110682677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149594624370072436073788451 224391936555108654110682677)
              ·
                refine ⟨21036744052041436322876501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224391936555108654110682677 21036744052041436322876501)
                ·
                  refine ⟨246524344359860581908709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21036744052041436322876501 246524344359860581908709)
                  ·
                    rfl

theorem cell21_1080235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_1080235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080235 prefixEnd_1080235 := by exact prefixLift 1080235
  have htrace : WordTrace (prefixWord ++ tailWord_1080235) baseStart_1080235 baseEnd_1080235 := by
    simpa [prefixWord, tailWord_1080235, baseEnd_1080235] using wordTrace_append hprefix tailTrace_1080235
  have hstable : (prefixWord ++ tailWord_1080235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080235).length < 2 ^ (prefixWord ++ tailWord_1080235).sum := by decide
  have hdescent : baseEnd_1080235 < baseStart_1080235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080266 : List Nat := [3, 1, 2, 1, 2, 1, 1, 10]
def baseStart_1080266 : Nat := 118140960795 + 1080266 * 2 ^ 59
def prefixEnd_1080266 : Nat := 4983230072969 + 3 ^ 40 * 1080266 * 2
def baseEnd_1080266 : Nat := 82177139660737138963993

theorem tailTrace_1080266 : CollatzResearch.WordTrace tailWord_1080266 prefixEnd_1080266 82177139660737138963993 := by
  unfold tailWord_1080266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9850134476097062897383163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26267025269592167726355101 9850134476097062897383163)
  ·
    refine ⟨14775201714145594346074745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9850134476097062897383163 14775201714145594346074745)
    ·
      refine ⟨11081401285609195759556059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14775201714145594346074745 11081401285609195759556059)
      ·
        refine ⟨16622101928413793639334089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11081401285609195759556059 16622101928413793639334089)
        ·
          refine ⟨12466576446310345229500567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16622101928413793639334089 12466576446310345229500567)
          ·
            refine ⟨18699864669465517844250851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12466576446310345229500567 18699864669465517844250851)
            ·
              refine ⟨28049797004198276766376277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18699864669465517844250851 28049797004198276766376277)
              ·
                refine ⟨82177139660737138963993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28049797004198276766376277 82177139660737138963993)
                ·
                  rfl

theorem cell21_1080266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_1080266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080266 prefixEnd_1080266 := by exact prefixLift 1080266
  have htrace : WordTrace (prefixWord ++ tailWord_1080266) baseStart_1080266 baseEnd_1080266 := by
    simpa [prefixWord, tailWord_1080266, baseEnd_1080266] using wordTrace_append hprefix tailTrace_1080266
  have hstable : (prefixWord ++ tailWord_1080266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080266).length < 2 ^ (prefixWord ++ tailWord_1080266).sum := by decide
  have hdescent : baseEnd_1080266 < baseStart_1080266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080314 : List Nat := [3, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_1080314 : Nat := 118140960795 + 1080314 * 2 ^ 59
def prefixEnd_1080314 : Nat := 4983230072969 + 3 ^ 40 * 1080314 * 2
def baseEnd_1080314 : Nat := 246542373236174000091881

theorem tailTrace_1080314 : CollatzResearch.WordTrace tailWord_1080314 prefixEnd_1080314 246542373236174000091881 := by
  unfold tailWord_1080314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9850572152053588946819999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26268192405476237191519997 9850572152053588946819999)
  ·
    refine ⟨14775858228080383420229999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9850572152053588946819999 14775858228080383420229999)
    ·
      refine ⟨22163787342120575130344999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14775858228080383420229999 22163787342120575130344999)
      ·
        refine ⟨33245681013180862695517499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22163787342120575130344999 33245681013180862695517499)
        ·
          refine ⟨49868521519771294043276249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33245681013180862695517499 49868521519771294043276249)
          ·
            refine ⟨37401391139828470532457187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49868521519771294043276249 37401391139828470532457187)
            ·
              refine ⟨56102086709742705798685781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37401391139828470532457187 56102086709742705798685781)
              ·
                refine ⟨657446328629797333578349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 56102086709742705798685781 657446328629797333578349)
                ·
                  refine ⟨246542373236174000091881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657446328629797333578349 246542373236174000091881)
                  ·
                    rfl

theorem cell21_1080314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_1080314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080314 prefixEnd_1080314 := by exact prefixLift 1080314
  have htrace : WordTrace (prefixWord ++ tailWord_1080314) baseStart_1080314 baseEnd_1080314 := by
    simpa [prefixWord, tailWord_1080314, baseEnd_1080314] using wordTrace_append hprefix tailTrace_1080314
  have hstable : (prefixWord ++ tailWord_1080314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080314).length < 2 ^ (prefixWord ++ tailWord_1080314).sum := by decide
  have hdescent : baseEnd_1080314 < baseStart_1080314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080359 : List Nat := [1, 1, 7, 1, 1, 10]
def baseStart_1080359 : Nat := 118140960795 + 1080359 * 2 ^ 59
def prefixEnd_1080359 : Nat := 4983230072969 + 3 ^ 40 * 1080359 * 2
def baseEnd_1080359 : Nat := 9131579364787552660807

theorem tailTrace_1080359 : CollatzResearch.WordTrace tailWord_1080359 prefixEnd_1080359 9131579364787552660807 := by
  unfold tailWord_1080359
  simp only [CollatzResearch.WordTrace]
  refine ⟨39403929893051328472668131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26269286595367552315112087 39403929893051328472668131)
  ·
    refine ⟨59105894839576992709002197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39403929893051328472668131 59105894839576992709002197)
    ·
      refine ⟨1385294410302585766617239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 59105894839576992709002197 1385294410302585766617239)
      ·
        refine ⟨2077941615453878649925859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385294410302585766617239 2077941615453878649925859)
        ·
          refine ⟨3116912423180817974888789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077941615453878649925859 3116912423180817974888789)
          ·
            refine ⟨9131579364787552660807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3116912423180817974888789 9131579364787552660807)
            ·
              rfl

theorem cell21_1080359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 10].length) (baseStart_1080359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080359 prefixEnd_1080359 := by exact prefixLift 1080359
  have htrace : WordTrace (prefixWord ++ tailWord_1080359) baseStart_1080359 baseEnd_1080359 := by
    simpa [prefixWord, tailWord_1080359, baseEnd_1080359] using wordTrace_append hprefix tailTrace_1080359
  have hstable : (prefixWord ++ tailWord_1080359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080359).length < 2 ^ (prefixWord ++ tailWord_1080359).sum := by decide
  have hdescent : baseEnd_1080359 < baseStart_1080359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080362 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_1080362 : Nat := 118140960795 + 1080362 * 2 ^ 59
def prefixEnd_1080362 : Nat := 4983230072969 + 3 ^ 40 * 1080362 * 2
def baseEnd_1080362 : Nat := 246553327490136583291783

theorem tailTrace_1080362 : CollatzResearch.WordTrace tailWord_1080362 prefixEnd_1080362 246553327490136583291783 := by
  unfold tailWord_1080362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851009828010114996256835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26269359541360306656684893 9851009828010114996256835)
  ·
    refine ⟨14776514742015172494385253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9851009828010114996256835 14776514742015172494385253)
    ·
      refine ⟨2770596514127844842697235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14776514742015172494385253 2770596514127844842697235)
      ·
        refine ⟨4155894771191767264045853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2770596514127844842697235 4155894771191767264045853)
        ·
          refine ⟨1558460539196912724017195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4155894771191767264045853 1558460539196912724017195)
          ·
            refine ⟨2337690808795369086025793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558460539196912724017195 2337690808795369086025793)
            ·
              refine ⟨1753268106596526814519345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337690808795369086025793 1753268106596526814519345)
              ·
                refine ⟨1314951079947395110889509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753268106596526814519345 1314951079947395110889509)
                ·
                  refine ⟨246553327490136583291783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1314951079947395110889509 246553327490136583291783)
                  ·
                    rfl

theorem cell21_1080362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_1080362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080362 prefixEnd_1080362 := by exact prefixLift 1080362
  have htrace : WordTrace (prefixWord ++ tailWord_1080362) baseStart_1080362 baseEnd_1080362 := by
    simpa [prefixWord, tailWord_1080362, baseEnd_1080362] using wordTrace_append hprefix tailTrace_1080362
  have hstable : (prefixWord ++ tailWord_1080362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080362).length < 2 ^ (prefixWord ++ tailWord_1080362).sum := by decide
  have hdescent : baseEnd_1080362 < baseStart_1080362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080373 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1080373 : Nat := 118140960795 + 1080373 * 2 ^ 59
def prefixEnd_1080373 : Nat := 4983230072969 + 3 ^ 40 * 1080373 * 2
def baseEnd_1080373 : Nat := 246555837840003008608427

theorem tailTrace_1080373 : CollatzResearch.WordTrace tailWord_1080373 prefixEnd_1080373 246555837840003008608427 := by
  unfold tailWord_1080373
  simp only [CollatzResearch.WordTrace]
  refine ⟨39404440515000608863677773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26269627010000405909118515 39404440515000608863677773)
  ·
    refine ⟨14776665193125228323879165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39404440515000608863677773 14776665193125228323879165)
    ·
      refine ⟨5541249447421960621454687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14776665193125228323879165 5541249447421960621454687)
      ·
        refine ⟨8311874171132940932182031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5541249447421960621454687 8311874171132940932182031)
        ·
          refine ⟨12467811256699411398273047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8311874171132940932182031 12467811256699411398273047)
          ·
            refine ⟨18701716885049117097409571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12467811256699411398273047 18701716885049117097409571)
            ·
              refine ⟨28052575327573675646114357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18701716885049117097409571 28052575327573675646114357)
              ·
                refine ⟨2629928936960032091823221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28052575327573675646114357 2629928936960032091823221)
                ·
                  refine ⟨246555837840003008608427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2629928936960032091823221 246555837840003008608427)
                  ·
                    rfl

theorem cell21_1080373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1080373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080373 prefixEnd_1080373 := by exact prefixLift 1080373
  have htrace : WordTrace (prefixWord ++ tailWord_1080373) baseStart_1080373 baseEnd_1080373 := by
    simpa [prefixWord, tailWord_1080373, baseEnd_1080373] using wordTrace_append hprefix tailTrace_1080373
  have hstable : (prefixWord ++ tailWord_1080373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080373).length < 2 ^ (prefixWord ++ tailWord_1080373).sum := by decide
  have hdescent : baseEnd_1080373 < baseStart_1080373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080438 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1080438 : Nat := 118140960795 + 1080438 * 2 ^ 59
def prefixEnd_1080438 : Nat := 4983230072969 + 3 ^ 40 * 1080438 * 2
def baseEnd_1080438 : Nat := 246570671725577340024961

theorem tailTrace_1080438 : CollatzResearch.WordTrace tailWord_1080438 prefixEnd_1080438 246570671725577340024961 := by
  unfold tailWord_1080438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462925703735320310299623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26271207506510083309862645 2462925703735320310299623)
  ·
    refine ⟨3694388555602980465449435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2462925703735320310299623 3694388555602980465449435)
    ·
      refine ⟨5541582833404470698174153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694388555602980465449435 5541582833404470698174153)
      ·
        refine ⟨4156187125053353023630615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5541582833404470698174153 4156187125053353023630615)
        ·
          refine ⟨6234280687580029535445923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156187125053353023630615 6234280687580029535445923)
          ·
            refine ⟨9351421031370044303168885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6234280687580029535445923 9351421031370044303168885)
            ·
              refine ⟨876695721690941653422083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9351421031370044303168885 876695721690941653422083)
              ·
                refine ⟨1315043582536412480133125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876695721690941653422083 1315043582536412480133125)
                ·
                  refine ⟨246570671725577340024961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315043582536412480133125 246570671725577340024961)
                  ·
                    rfl

theorem cell21_1080438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1080438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080438 prefixEnd_1080438 := by exact prefixLift 1080438
  have htrace : WordTrace (prefixWord ++ tailWord_1080438) baseStart_1080438 baseEnd_1080438 := by
    simpa [prefixWord, tailWord_1080438, baseEnd_1080438] using wordTrace_append hprefix tailTrace_1080438
  have hstable : (prefixWord ++ tailWord_1080438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080438).length < 2 ^ (prefixWord ++ tailWord_1080438).sum := by decide
  have hdescent : baseEnd_1080438 < baseStart_1080438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080452 : List Nat := [2, 3, 2, 1, 2, 4, 2, 5]
def baseStart_1080452 : Nat := 118140960795 + 1080452 * 2 ^ 59
def prefixEnd_1080452 : Nat := 4983230072969 + 3 ^ 40 * 1080452 * 2
def baseEnd_1080452 : Nat := 82191288905438808930533

theorem tailTrace_1080452 : CollatzResearch.WordTrace tailWord_1080452 prefixEnd_1080452 82191288905438808930533 := by
  unfold tailWord_1080452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19703660940857202677901805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26271547921142936903869073 19703660940857202677901805)
  ·
    refine ⟨7388872852821451004213177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19703660940857202677901805 7388872852821451004213177)
    ·
      refine ⟨5541654639616088253159883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7388872852821451004213177 5541654639616088253159883)
      ·
        refine ⟨8312481959424132379739825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5541654639616088253159883 8312481959424132379739825)
        ·
          refine ⟨6234361469568099284804869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8312481959424132379739825 6234361469568099284804869)
          ·
            refine ⟨1168942775544018615900913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6234361469568099284804869 1168942775544018615900913)
            ·
              refine ⟨876707081658013961925685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168942775544018615900913 876707081658013961925685)
              ·
                refine ⟨82191288905438808930533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876707081658013961925685 82191288905438808930533)
                ·
                  rfl

theorem cell21_1080452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_1080452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080452 prefixEnd_1080452 := by exact prefixLift 1080452
  have htrace : WordTrace (prefixWord ++ tailWord_1080452) baseStart_1080452 baseEnd_1080452 := by
    simpa [prefixWord, tailWord_1080452, baseEnd_1080452] using wordTrace_append hprefix tailTrace_1080452
  have hstable : (prefixWord ++ tailWord_1080452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080452).length < 2 ^ (prefixWord ++ tailWord_1080452).sum := by decide
  have hdescent : baseEnd_1080452 < baseStart_1080452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080480 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_1080480 : Nat := 118140960795 + 1080480 * 2 ^ 59
def prefixEnd_1080480 : Nat := 4983230072969 + 3 ^ 40 * 1080480 * 2
def baseEnd_1080480 : Nat := 246580256697794600324875

theorem tailTrace_1080480 : CollatzResearch.WordTrace tailWord_1080480 prefixEnd_1080480 246580256697794600324875 := by
  unfold tailWord_1080480
  simp only [CollatzResearch.WordTrace]
  refine ⟨19704171562806483068911447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26272228750408644091881929 19704171562806483068911447)
  ·
    refine ⟨29556257344209724603367171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19704171562806483068911447 29556257344209724603367171)
    ·
      refine ⟨44334386016314586905050757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29556257344209724603367171 44334386016314586905050757)
      ·
        refine ⟨8312697378058985044697017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44334386016314586905050757 8312697378058985044697017)
        ·
          refine ⟨6234523033544238783522763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8312697378058985044697017 6234523033544238783522763)
          ·
            refine ⟨9351784550316358175284145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6234523033544238783522763 9351784550316358175284145)
            ·
              refine ⟨7013838412737268631463109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9351784550316358175284145 7013838412737268631463109)
              ·
                refine ⟨1315094702388237868399333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7013838412737268631463109 1315094702388237868399333)
                ·
                  refine ⟨246580256697794600324875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315094702388237868399333 246580256697794600324875)
                  ·
                    rfl

theorem cell21_1080480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_1080480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080480 prefixEnd_1080480 := by exact prefixLift 1080480
  have htrace : WordTrace (prefixWord ++ tailWord_1080480) baseStart_1080480 baseEnd_1080480 := by
    simpa [prefixWord, tailWord_1080480, baseEnd_1080480] using wordTrace_append hprefix tailTrace_1080480
  have hstable : (prefixWord ++ tailWord_1080480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080480).length < 2 ^ (prefixWord ++ tailWord_1080480).sum := by decide
  have hdescent : baseEnd_1080480 < baseStart_1080480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080497 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 4]
def baseStart_1080497 : Nat := 118140960795 + 1080497 * 2 ^ 59
def prefixEnd_1080497 : Nat := 4983230072969 + 3 ^ 40 * 1080497 * 2
def baseEnd_1080497 : Nat := 246584136329406348541507

theorem tailTrace_1080497 : CollatzResearch.WordTrace tailWord_1080497 prefixEnd_1080497 246584136329406348541507 := by
  unfold tailWord_1080497
  simp only [CollatzResearch.WordTrace]
  refine ⟨39408963166551378041191745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26272642111034252027461163 39408963166551378041191745)
  ·
    refine ⟨29556722374913533530893809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39408963166551378041191745 29556722374913533530893809)
    ·
      refine ⟨22167541781185150148170357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29556722374913533530893809 22167541781185150148170357)
      ·
        refine ⟨2078207041986107826390971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22167541781185150148170357 2078207041986107826390971)
        ·
          refine ⟨3117310562979161739586457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078207041986107826390971 3117310562979161739586457)
          ·
            refine ⟨2337982922234371304689843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3117310562979161739586457 2337982922234371304689843)
            ·
              refine ⟨3506974383351556957034765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337982922234371304689843 3506974383351556957034765)
              ·
                refine ⟨1315115393756833858888037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3506974383351556957034765 1315115393756833858888037)
                ·
                  refine ⟨246584136329406348541507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315115393756833858888037 246584136329406348541507)
                  ·
                    rfl

theorem cell21_1080497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_1080497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080497 prefixEnd_1080497 := by exact prefixLift 1080497
  have htrace : WordTrace (prefixWord ++ tailWord_1080497) baseStart_1080497 baseEnd_1080497 := by
    simpa [prefixWord, tailWord_1080497, baseEnd_1080497] using wordTrace_append hprefix tailTrace_1080497
  have hstable : (prefixWord ++ tailWord_1080497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080497).length < 2 ^ (prefixWord ++ tailWord_1080497).sum := by decide
  have hdescent : baseEnd_1080497 < baseStart_1080497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080534 : List Nat := [5, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1080534 : Nat := 118140960795 + 1080534 * 2 ^ 59
def prefixEnd_1080534 : Nat := 4983230072969 + 3 ^ 40 * 1080534 * 2
def baseEnd_1080534 : Nat := 246592580233502506424765

theorem tailTrace_1080534 : CollatzResearch.WordTrace tailWord_1080534 prefixEnd_1080534 246592580233502506424765 := by
  unfold tailWord_1080534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463144541713583335018041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26273541778278222240192437 2463144541713583335018041)
  ·
    refine ⟨1847358406285187501263531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2463144541713583335018041 1847358406285187501263531)
    ·
      refine ⟨2771037609427781251895297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1847358406285187501263531 2771037609427781251895297)
      ·
        refine ⟨2078278207070835938921473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2771037609427781251895297 2078278207070835938921473)
        ·
          refine ⟨1558708655303126954191105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2078278207070835938921473 1558708655303126954191105)
          ·
            refine ⟨1169031491477345215643329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558708655303126954191105 1169031491477345215643329)
            ·
              refine ⟨876773618608008911732497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169031491477345215643329 876773618608008911732497)
              ·
                refine ⟨657580213956006683799373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876773618608008911732497 657580213956006683799373)
                ·
                  refine ⟨246592580233502506424765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657580213956006683799373 246592580233502506424765)
                  ·
                    rfl

theorem cell21_1080534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1080534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080534 prefixEnd_1080534 := by exact prefixLift 1080534
  have htrace : WordTrace (prefixWord ++ tailWord_1080534) baseStart_1080534 baseEnd_1080534 := by
    simpa [prefixWord, tailWord_1080534, baseEnd_1080534] using wordTrace_append hprefix tailTrace_1080534
  have hstable : (prefixWord ++ tailWord_1080534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080534).length < 2 ^ (prefixWord ++ tailWord_1080534).sum := by decide
  have hdescent : baseEnd_1080534 < baseStart_1080534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080556 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1080556 : Nat := 118140960795 + 1080556 * 2 ^ 59
def prefixEnd_1080556 : Nat := 4983230072969 + 3 ^ 40 * 1080556 * 2
def baseEnd_1080556 : Nat := 246597600933235357058053

theorem tailTrace_1080556 : CollatzResearch.WordTrace tailWord_1080556 prefixEnd_1080556 246597600933235357058053 := by
  unfold tailWord_1080556
  simp only [CollatzResearch.WordTrace]
  refine ⟨19705557536668815558794761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26274076715558420745059681 19705557536668815558794761)
  ·
    refine ⟨14779168152501611669096071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19705557536668815558794761 14779168152501611669096071)
    ·
      refine ⟨22168752228752417503644107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14779168152501611669096071 22168752228752417503644107)
      ·
        refine ⟨33253128343128626255466161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22168752228752417503644107 33253128343128626255466161)
        ·
          refine ⟨24939846257346469691599621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33253128343128626255466161 24939846257346469691599621)
          ·
            refine ⟨4676221173252463067174929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24939846257346469691599621 4676221173252463067174929)
            ·
              refine ⟨3507165879939347300381197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4676221173252463067174929 3507165879939347300381197)
              ·
                refine ⟨1315187204977255237642949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3507165879939347300381197 1315187204977255237642949)
                ·
                  refine ⟨246597600933235357058053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315187204977255237642949 246597600933235357058053)
                  ·
                    rfl

theorem cell21_1080556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1080556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080556 prefixEnd_1080556 := by exact prefixLift 1080556
  have htrace : WordTrace (prefixWord ++ tailWord_1080556) baseStart_1080556 baseEnd_1080556 := by
    simpa [prefixWord, tailWord_1080556, baseEnd_1080556] using wordTrace_append hprefix tailTrace_1080556
  have hstable : (prefixWord ++ tailWord_1080556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080556).length < 2 ^ (prefixWord ++ tailWord_1080556).sum := by decide
  have hdescent : baseEnd_1080556 < baseStart_1080556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080618 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_1080618 : Nat := 118140960795 + 1080618 * 2 ^ 59
def prefixEnd_1080618 : Nat := 4983230072969 + 3 ^ 40 * 1080618 * 2
def baseEnd_1080618 : Nat := 246611750177937027024593

theorem tailTrace_1080618 : CollatzResearch.WordTrace tailWord_1080618 prefixEnd_1080618 246611750177937027024593 := by
  unfold tailWord_1080618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9853344099778253926586627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26275584266075343804231005 9853344099778253926586627)
  ·
    refine ⟨14780016149667380889879941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9853344099778253926586627 14780016149667380889879941)
    ·
      refine ⟨2771253028062633916852489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14780016149667380889879941 2771253028062633916852489)
      ·
        refine ⟨2078439771046975437639367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2771253028062633916852489 2078439771046975437639367)
        ·
          refine ⟨3117659656570463156459051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078439771046975437639367 3117659656570463156459051)
          ·
            refine ⟨4676489484855694734688577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117659656570463156459051 4676489484855694734688577)
            ·
              refine ⟨3507367113641771051016433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4676489484855694734688577 3507367113641771051016433)
              ·
                refine ⟨2630525335231328288262325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507367113641771051016433 2630525335231328288262325)
                ·
                  refine ⟨246611750177937027024593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2630525335231328288262325 246611750177937027024593)
                  ·
                    rfl

theorem cell21_1080618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_1080618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080618 prefixEnd_1080618 := by exact prefixLift 1080618
  have htrace : WordTrace (prefixWord ++ tailWord_1080618) baseStart_1080618 baseEnd_1080618 := by
    simpa [prefixWord, tailWord_1080618, baseEnd_1080618] using wordTrace_append hprefix tailTrace_1080618
  have hstable : (prefixWord ++ tailWord_1080618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080618).length < 2 ^ (prefixWord ++ tailWord_1080618).sum := by decide
  have hdescent : baseEnd_1080618 < baseStart_1080618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080621 : List Nat := [1, 5, 3, 1, 1, 3, 2, 5]
def baseStart_1080621 : Nat := 118140960795 + 1080621 * 2 ^ 59
def prefixEnd_1080621 : Nat := 4983230072969 + 3 ^ 40 * 1080621 * 2
def baseEnd_1080621 : Nat := 82204144939603229491529

theorem tailTrace_1080621 : CollatzResearch.WordTrace tailWord_1080621 prefixEnd_1080621 82204144939603229491529 := by
  unfold tailWord_1080621
  simp only [CollatzResearch.WordTrace]
  refine ⟨39413485818102147218705717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26275657212068098145803811 39413485818102147218705717)
  ·
    refine ⟨3695014295447076301753661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39413485818102147218705717 3695014295447076301753661)
    ·
      refine ⟨1385630360792653613157623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3695014295447076301753661 1385630360792653613157623)
      ·
        refine ⟨2078445541188980419736435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385630360792653613157623 2078445541188980419736435)
        ·
          refine ⟨3117668311783470629604653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078445541188980419736435 3117668311783470629604653)
          ·
            refine ⟨1169125616918801486101745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3117668311783470629604653 1169125616918801486101745)
            ·
              refine ⟨876844212689101114576309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169125616918801486101745 876844212689101114576309)
              ·
                refine ⟨82204144939603229491529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876844212689101114576309 82204144939603229491529)
                ·
                  rfl

theorem cell21_1080621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 5].length) (baseStart_1080621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080621 prefixEnd_1080621 := by exact prefixLift 1080621
  have htrace : WordTrace (prefixWord ++ tailWord_1080621) baseStart_1080621 baseEnd_1080621 := by
    simpa [prefixWord, tailWord_1080621, baseEnd_1080621] using wordTrace_append hprefix tailTrace_1080621
  have hstable : (prefixWord ++ tailWord_1080621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080621).length < 2 ^ (prefixWord ++ tailWord_1080621).sum := by decide
  have hdescent : baseEnd_1080621 < baseStart_1080621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080708 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1080708 : Nat := 118140960795 + 1080708 * 2 ^ 59
def prefixEnd_1080708 : Nat := 4983230072969 + 3 ^ 40 * 1080708 * 2
def baseEnd_1080708 : Nat := 246632289404116870524409

theorem tailTrace_1080708 : CollatzResearch.WordTrace tailWord_1080708 prefixEnd_1080708 246632289404116870524409 := by
  unfold tailWord_1080708
  simp only [CollatzResearch.WordTrace]
  refine ⟨19708329484393480538561389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26277772645857974051415185 19708329484393480538561389)
  ·
    refine ⟨7390623556647555201960521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19708329484393480538561389 7390623556647555201960521)
    ·
      refine ⟨5542967667485666401470391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7390623556647555201960521 5542967667485666401470391)
      ·
        refine ⟨8314451501228499602205587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5542967667485666401470391 8314451501228499602205587)
        ·
          refine ⟨12471677251842749403308381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8314451501228499602205587 12471677251842749403308381)
          ·
            refine ⟨4676878969441031026240643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12471677251842749403308381 4676878969441031026240643)
            ·
              refine ⟨7015318454161546539360965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676878969441031026240643 7015318454161546539360965)
              ·
                refine ⟨1315372210155289976130181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7015318454161546539360965 1315372210155289976130181)
                ·
                  refine ⟨246632289404116870524409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315372210155289976130181 246632289404116870524409)
                  ·
                    rfl

theorem cell21_1080708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1080708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080708 prefixEnd_1080708 := by exact prefixLift 1080708
  have htrace : WordTrace (prefixWord ++ tailWord_1080708) baseStart_1080708 baseEnd_1080708 := by
    simpa [prefixWord, tailWord_1080708, baseEnd_1080708] using wordTrace_append hprefix tailTrace_1080708
  have hstable : (prefixWord ++ tailWord_1080708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080708).length < 2 ^ (prefixWord ++ tailWord_1080708).sum := by decide
  have hdescent : baseEnd_1080708 < baseStart_1080708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080711 : List Nat := [1, 1, 4, 2, 2, 2, 4, 2, 3]
def baseStart_1080711 : Nat := 118140960795 + 1080711 * 2 ^ 59
def prefixEnd_1080711 : Nat := 4983230072969 + 3 ^ 40 * 1080711 * 2
def baseEnd_1080711 : Nat := 246632974044989531974403

theorem tailTrace_1080711 : CollatzResearch.WordTrace tailWord_1080711 prefixEnd_1080711 246632974044989531974403 := by
  unfold tailWord_1080711
  simp only [CollatzResearch.WordTrace]
  refine ⟨39416768387776092589481987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26277845591850728392987991 39416768387776092589481987)
  ·
    refine ⟨59125152581664138884222981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39416768387776092589481987 59125152581664138884222981)
    ·
      refine ⟨11085966109062026040791809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59125152581664138884222981 11085966109062026040791809)
      ·
        refine ⟨8314474581796519530593857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11085966109062026040791809 8314474581796519530593857)
        ·
          refine ⟨6235855936347389647945393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8314474581796519530593857 6235855936347389647945393)
          ·
            refine ⟨4676891952260542235959045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6235855936347389647945393 4676891952260542235959045)
            ·
              refine ⟨876917241048851669242321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4676891952260542235959045 876917241048851669242321)
              ·
                refine ⟨657687930786638751931741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876917241048851669242321 657687930786638751931741)
                ·
                  refine ⟨246632974044989531974403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657687930786638751931741 246632974044989531974403)
                  ·
                    rfl

theorem cell21_1080711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 3].length) (baseStart_1080711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080711 prefixEnd_1080711 := by exact prefixLift 1080711
  have htrace : WordTrace (prefixWord ++ tailWord_1080711) baseStart_1080711 baseEnd_1080711 := by
    simpa [prefixWord, tailWord_1080711, baseEnd_1080711] using wordTrace_append hprefix tailTrace_1080711
  have hstable : (prefixWord ++ tailWord_1080711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080711).length < 2 ^ (prefixWord ++ tailWord_1080711).sum := by decide
  have hdescent : baseEnd_1080711 < baseStart_1080711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080829 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1080829 : Nat := 118140960795 + 1080829 * 2 ^ 59
def prefixEnd_1080829 : Nat := 4983230072969 + 3 ^ 40 * 1080829 * 2
def baseEnd_1080829 : Nat := 246659903252647549007495

theorem tailTrace_1080829 : CollatzResearch.WordTrace tailWord_1080829 prefixEnd_1080829 246659903252647549007495 := by
  unfold tailWord_1080829
  simp only [CollatzResearch.WordTrace]
  refine ⟨39421072201348598742277541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26280714800899065828185027 39421072201348598742277541)
  ·
    refine ⟨7391451037752862264177039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39421072201348598742277541 7391451037752862264177039)
    ·
      refine ⟨11087176556629293396265559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7391451037752862264177039 11087176556629293396265559)
      ·
        refine ⟨16630764834943940094398339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11087176556629293396265559 16630764834943940094398339)
        ·
          refine ⟨24946147252415910141597509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16630764834943940094398339 24946147252415910141597509)
          ·
            refine ⟨4677402609827983151549533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24946147252415910141597509 4677402609827983151549533)
            ·
              refine ⟨1754025978685493681831075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4677402609827983151549533 1754025978685493681831075)
              ·
                refine ⟨2631038968028240522746613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754025978685493681831075 2631038968028240522746613)
                ·
                  refine ⟨246659903252647549007495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2631038968028240522746613 246659903252647549007495)
                  ·
                    rfl

theorem cell21_1080829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1080829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080829 prefixEnd_1080829 := by exact prefixLift 1080829
  have htrace : WordTrace (prefixWord ++ tailWord_1080829) baseStart_1080829 baseEnd_1080829 := by
    simpa [prefixWord, tailWord_1080829, baseEnd_1080829] using wordTrace_append hprefix tailTrace_1080829
  have hstable : (prefixWord ++ tailWord_1080829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080829).length < 2 ^ (prefixWord ++ tailWord_1080829).sum := by decide
  have hdescent : baseEnd_1080829 < baseStart_1080829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080936 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_1080936 : Nat := 118140960795 + 1080936 * 2 ^ 59
def prefixEnd_1080936 : Nat := 4983230072969 + 3 ^ 40 * 1080936 * 2
def baseEnd_1080936 : Nat := 246684322110439140723943

theorem tailTrace_1080936 : CollatzResearch.WordTrace tailWord_1080936 prefixEnd_1080936 246684322110439140723943 := by
  unfold tailWord_1080936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19712487405980478008211331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26283316541307304010948441 19712487405980478008211331)
  ·
    refine ⟨29568731108970717012316997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19712487405980478008211331 29568731108970717012316997)
    ·
      refine ⟨5544137082932009439809437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29568731108970717012316997 5544137082932009439809437)
      ·
        refine ⟨2079051406099503539928539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5544137082932009439809437 2079051406099503539928539)
        ·
          refine ⟨3118577109149255309892809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079051406099503539928539 3118577109149255309892809)
          ·
            refine ⟨2338932831861941482419607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3118577109149255309892809 2338932831861941482419607)
            ·
              refine ⟨3508399247792912223629411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338932831861941482419607 3508399247792912223629411)
              ·
                refine ⟨5262598871689368335444117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508399247792912223629411 5262598871689368335444117)
                ·
                  refine ⟨246684322110439140723943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5262598871689368335444117 246684322110439140723943)
                  ·
                    rfl

theorem cell21_1080936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_1080936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080936 prefixEnd_1080936 := by exact prefixLift 1080936
  have htrace : WordTrace (prefixWord ++ tailWord_1080936) baseStart_1080936 baseEnd_1080936 := by
    simpa [prefixWord, tailWord_1080936, baseEnd_1080936] using wordTrace_append hprefix tailTrace_1080936
  have hstable : (prefixWord ++ tailWord_1080936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080936).length < 2 ^ (prefixWord ++ tailWord_1080936).sum := by decide
  have hdescent : baseEnd_1080936 < baseStart_1080936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080967 : List Nat := [1, 1, 4, 2, 1, 5, 2, 5]
def baseStart_1080967 : Nat := 118140960795 + 1080967 * 2 ^ 59
def prefixEnd_1080967 : Nat := 4983230072969 + 3 ^ 40 * 1080967 * 2
def baseEnd_1080967 : Nat := 82230465577596658569071

theorem tailTrace_1080967 : CollatzResearch.WordTrace tailWord_1080967 prefixEnd_1080967 82230465577596658569071 := by
  unfold tailWord_1080967
  simp only [CollatzResearch.WordTrace]
  refine ⟨39426105474848648310801155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26284070316565765540534103 39426105474848648310801155)
  ·
    refine ⟨59139158212272972466201733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39426105474848648310801155 59139158212272972466201733)
    ·
      refine ⟨11088592164801182337412825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59139158212272972466201733 11088592164801182337412825)
      ·
        refine ⟨8316444123600886753059619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11088592164801182337412825 8316444123600886753059619)
        ·
          refine ⟨12474666185401330129589429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8316444123600886753059619 12474666185401330129589429)
          ·
            refine ⟨1169499954881374699649009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12474666185401330129589429 1169499954881374699649009)
            ·
              refine ⟨877124966161031024736757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169499954881374699649009 877124966161031024736757)
              ·
                refine ⟨82230465577596658569071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877124966161031024736757 82230465577596658569071)
                ·
                  rfl

theorem cell21_1080967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 5].length) (baseStart_1080967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080967 prefixEnd_1080967 := by exact prefixLift 1080967
  have htrace : WordTrace (prefixWord ++ tailWord_1080967) baseStart_1080967 baseEnd_1080967 := by
    simpa [prefixWord, tailWord_1080967, baseEnd_1080967] using wordTrace_append hprefix tailTrace_1080967
  have hstable : (prefixWord ++ tailWord_1080967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080967).length < 2 ^ (prefixWord ++ tailWord_1080967).sum := by decide
  have hdescent : baseEnd_1080967 < baseStart_1080967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080995 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 4]
def baseStart_1080995 : Nat := 118140960795 + 1080995 * 2 ^ 59
def prefixEnd_1080995 : Nat := 4983230072969 + 3 ^ 40 * 1080995 * 2
def baseEnd_1080995 : Nat := 246697786714268149240489

theorem tailTrace_1080995 : CollatzResearch.WordTrace tailWord_1080995 prefixEnd_1080995 246697786714268149240489 := by
  unfold tailWord_1080995
  simp only [CollatzResearch.WordTrace]
  refine ⟨39427126718747209092820439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26284751145831472728546959 39427126718747209092820439)
  ·
    refine ⟨59140690078120813639230659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39427126718747209092820439 59140690078120813639230659)
    ·
      refine ⟨88711035117181220458845989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59140690078120813639230659 88711035117181220458845989)
      ·
        refine ⟨16633319084471478836033623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88711035117181220458845989 16633319084471478836033623)
        ·
          refine ⟨24949978626707218254050435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16633319084471478836033623 24949978626707218254050435)
          ·
            refine ⟨37424967940060827381075653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24949978626707218254050435 37424967940060827381075653)
            ·
              refine ⟨7017181488761405133951685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37424967940060827381075653 7017181488761405133951685)
              ·
                refine ⟨1315721529142763462615941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7017181488761405133951685 1315721529142763462615941)
                ·
                  refine ⟨246697786714268149240489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315721529142763462615941 246697786714268149240489)
                  ·
                    rfl

theorem cell21_1080995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_1080995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080995 prefixEnd_1080995 := by exact prefixLift 1080995
  have htrace : WordTrace (prefixWord ++ tailWord_1080995) baseStart_1080995 baseEnd_1080995 := by
    simpa [prefixWord, tailWord_1080995, baseEnd_1080995] using wordTrace_append hprefix tailTrace_1080995
  have hstable : (prefixWord ++ tailWord_1080995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080995).length < 2 ^ (prefixWord ++ tailWord_1080995).sum := by decide
  have hdescent : baseEnd_1080995 < baseStart_1080995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081071 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 4]
def baseStart_1081071 : Nat := 118140960795 + 1081071 * 2 ^ 59
def prefixEnd_1081071 : Nat := 4983230072969 + 3 ^ 40 * 1081071 * 2
def baseEnd_1081071 : Nat := 246715130949708905973667

theorem tailTrace_1081071 : CollatzResearch.WordTrace tailWord_1081071 prefixEnd_1081071 246715130949708905973667 := by
  unfold tailWord_1081071
  simp only [CollatzResearch.WordTrace]
  refine ⟨39429898666471874072587067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26286599110981249381724711 39429898666471874072587067)
  ·
    refine ⟨59144847999707811108880601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39429898666471874072587067 59144847999707811108880601)
    ·
      refine ⟨44358635999780858331660451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59144847999707811108880601 44358635999780858331660451)
      ·
        refine ⟨66537953999671287497490677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44358635999780858331660451 66537953999671287497490677)
        ·
          refine ⟨6237933187469183202889751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66537953999671287497490677 6237933187469183202889751)
          ·
            refine ⟨9356899781203774804334627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6237933187469183202889751 9356899781203774804334627)
            ·
              refine ⟨14035349671805662206501941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9356899781203774804334627 14035349671805662206501941)
              ·
                refine ⟨1315814031731780831859557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14035349671805662206501941 1315814031731780831859557)
                ·
                  refine ⟨246715130949708905973667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315814031731780831859557 246715130949708905973667)
                  ·
                    rfl

theorem cell21_1081071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_1081071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081071 prefixEnd_1081071 := by exact prefixLift 1081071
  have htrace : WordTrace (prefixWord ++ tailWord_1081071) baseStart_1081071 baseEnd_1081071 := by
    simpa [prefixWord, tailWord_1081071, baseEnd_1081071] using wordTrace_append hprefix tailTrace_1081071
  have hstable : (prefixWord ++ tailWord_1081071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081071).length < 2 ^ (prefixWord ++ tailWord_1081071).sum := by decide
  have hdescent : baseEnd_1081071 < baseStart_1081071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081094 : List Nat := [6, 2, 2, 1, 1, 1, 8]
def baseStart_1081094 : Nat := 118140960795 + 1081094 * 2 ^ 59
def prefixEnd_1081094 : Nat := 4983230072969 + 3 ^ 40 * 1081094 * 2
def baseEnd_1081094 : Nat := 27413375540340664121143

theorem tailTrace_1081094 : CollatzResearch.WordTrace tailWord_1081094 prefixEnd_1081094 27413375540340664121143 := by
  unfold tailWord_1081094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232210548293392156271073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26287158363592366000449557 1232210548293392156271073)
  ·
    refine ⟨924157911220044117203305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1232210548293392156271073 924157911220044117203305)
    ·
      refine ⟨693118433415033087902479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 924157911220044117203305 693118433415033087902479)
      ·
        refine ⟨1039677650122549631853719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693118433415033087902479 1039677650122549631853719)
        ·
          refine ⟨1559516475183824447780579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039677650122549631853719 1559516475183824447780579)
          ·
            refine ⟨2339274712775736671670869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559516475183824447780579 2339274712775736671670869)
            ·
              refine ⟨27413375540340664121143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2339274712775736671670869 27413375540340664121143)
              ·
                rfl

theorem cell21_1081094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 8].length) (baseStart_1081094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081094 prefixEnd_1081094 := by exact prefixLift 1081094
  have htrace : WordTrace (prefixWord ++ tailWord_1081094) baseStart_1081094 baseEnd_1081094 := by
    simpa [prefixWord, tailWord_1081094, baseEnd_1081094] using wordTrace_append hprefix tailTrace_1081094
  have hstable : (prefixWord ++ tailWord_1081094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081094).length < 2 ^ (prefixWord ++ tailWord_1081094).sum := by decide
  have hdescent : baseEnd_1081094 < baseStart_1081094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081108 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1081108 : Nat := 118140960795 + 1081108 * 2 ^ 59
def prefixEnd_1081108 : Nat := 4983230072969 + 3 ^ 40 * 1081108 * 2
def baseEnd_1081108 : Nat := 246723574853805063856925

theorem tailTrace_1081108 : CollatzResearch.WordTrace tailWord_1081108 prefixEnd_1081108 246723574853805063856925 := by
  unfold tailWord_1081108
  simp only [CollatzResearch.WordTrace]
  refine ⟨19715624083668914695841989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26287498778225219594455985 19715624083668914695841989)
  ·
    refine ⟨3696679515687921505470373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19715624083668914695841989 3696679515687921505470373)
    ·
      refine ⟨693127409191485282275695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3696679515687921505470373 693127409191485282275695)
      ·
        refine ⟨1039691113787227923413543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693127409191485282275695 1039691113787227923413543)
        ·
          refine ⟨1559536670680841885120315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039691113787227923413543 1559536670680841885120315)
          ·
            refine ⟨2339305006021262827680473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559536670680841885120315 2339305006021262827680473)
            ·
              refine ⟨1754478754515947120760355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2339305006021262827680473 1754478754515947120760355)
              ·
                refine ⟨2631718131773920681140533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754478754515947120760355 2631718131773920681140533)
                ·
                  refine ⟨246723574853805063856925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2631718131773920681140533 246723574853805063856925)
                  ·
                    rfl

theorem cell21_1081108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1081108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081108 prefixEnd_1081108 := by exact prefixLift 1081108
  have htrace : WordTrace (prefixWord ++ tailWord_1081108) baseStart_1081108 baseEnd_1081108 := by
    simpa [prefixWord, tailWord_1081108, baseEnd_1081108] using wordTrace_append hprefix tailTrace_1081108
  have hstable : (prefixWord ++ tailWord_1081108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081108).length < 2 ^ (prefixWord ++ tailWord_1081108).sum := by decide
  have hdescent : baseEnd_1081108 < baseStart_1081108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081192 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_1081192 : Nat := 118140960795 + 1081192 * 2 ^ 59
def prefixEnd_1081192 : Nat := 4983230072969 + 3 ^ 40 * 1081192 * 2
def baseEnd_1081192 : Nat := 246742744798239584456753

theorem tailTrace_1081192 : CollatzResearch.WordTrace tailWord_1081192 prefixEnd_1081192 246742744798239584456753 := by
  unfold tailWord_1081192
  simp only [CollatzResearch.WordTrace]
  refine ⟨19717155949516755868870915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26289541266022341158494553 19717155949516755868870915)
  ·
    refine ⟨29575733924275133803306373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19717155949516755868870915 29575733924275133803306373)
    ·
      refine ⟨5545450110801587588119945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29575733924275133803306373 5545450110801587588119945)
      ·
        refine ⟨4159087583101190691089959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5545450110801587588119945 4159087583101190691089959)
        ·
          refine ⟨6238631374651786036634939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159087583101190691089959 6238631374651786036634939)
          ·
            refine ⟨9357947061977679054952409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238631374651786036634939 9357947061977679054952409)
            ·
              refine ⟨7018460296483259291214307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9357947061977679054952409 7018460296483259291214307)
              ·
                refine ⟨10527690444724888936821461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7018460296483259291214307 10527690444724888936821461)
                ·
                  refine ⟨246742744798239584456753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10527690444724888936821461 246742744798239584456753)
                  ·
                    rfl

theorem cell21_1081192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_1081192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081192 prefixEnd_1081192 := by exact prefixLift 1081192
  have htrace : WordTrace (prefixWord ++ tailWord_1081192) baseStart_1081192 baseEnd_1081192 := by
    simpa [prefixWord, tailWord_1081192, baseEnd_1081192] using wordTrace_append hprefix tailTrace_1081192
  have hstable : (prefixWord ++ tailWord_1081192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081192).length < 2 ^ (prefixWord ++ tailWord_1081192).sum := by decide
  have hdescent : baseEnd_1081192 < baseStart_1081192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081209 : List Nat := [1, 2, 1, 3, 2, 2, 2, 5, 3]
def baseStart_1081209 : Nat := 118140960795 + 1081209 * 2 ^ 59
def prefixEnd_1081209 : Nat := 4983230072969 + 3 ^ 40 * 1081209 * 2
def baseEnd_1081209 : Nat := 246746624429851332673385

theorem tailTrace_1081209 : CollatzResearch.WordTrace tailWord_1081209 prefixEnd_1081209 246746624429851332673385 := by
  unfold tailWord_1081209
  simp only [CollatzResearch.WordTrace]
  refine ⟨39434931939971923641110681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26289954626647949094073787 39434931939971923641110681)
  ·
    refine ⟨29576198954978942730833011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39434931939971923641110681 29576198954978942730833011)
    ·
      refine ⟨44364298432468414096249517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29576198954978942730833011 44364298432468414096249517)
      ·
        refine ⟨16636611912175655286093569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44364298432468414096249517 16636611912175655286093569)
        ·
          refine ⟨12477458934131741464570177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16636611912175655286093569 12477458934131741464570177)
          ·
            refine ⟨9358094200598806098427633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12477458934131741464570177 9358094200598806098427633)
            ·
              refine ⟨7018570650449104573820725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9358094200598806098427633 7018570650449104573820725)
              ·
                refine ⟨657990998479603553795693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7018570650449104573820725 657990998479603553795693)
                ·
                  refine ⟨246746624429851332673385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657990998479603553795693 246746624429851332673385)
                  ·
                    rfl

theorem cell21_1081209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_1081209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081209 prefixEnd_1081209 := by exact prefixLift 1081209
  have htrace : WordTrace (prefixWord ++ tailWord_1081209) baseStart_1081209 baseEnd_1081209 := by
    simpa [prefixWord, tailWord_1081209, baseEnd_1081209] using wordTrace_append hprefix tailTrace_1081209
  have hstable : (prefixWord ++ tailWord_1081209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081209).length < 2 ^ (prefixWord ++ tailWord_1081209).sum := by decide
  have hdescent : baseEnd_1081209 < baseStart_1081209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081319 : List Nat := [1, 1, 5, 2, 3, 2, 1, 3, 3]
def baseStart_1081319 : Nat := 118140960795 + 1081319 * 2 ^ 59
def prefixEnd_1081319 : Nat := 4983230072969 + 3 ^ 40 * 1081319 * 2
def baseEnd_1081319 : Nat := 246771727928515585839827

theorem tailTrace_1081319 : CollatzResearch.WordTrace tailWord_1081319 prefixEnd_1081319 246771727928515585839827 := by
  unfold tailWord_1081319
  simp only [CollatzResearch.WordTrace]
  refine ⟨39438943969573412427615011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26292629313048941618410007 39438943969573412427615011)
  ·
    refine ⟨59158415954360118641422517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39438943969573412427615011 59158415954360118641422517)
    ·
      refine ⟨5546101495721261122633361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59158415954360118641422517 5546101495721261122633361)
      ·
        refine ⟨4159576121790945841975021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5546101495721261122633361 4159576121790945841975021)
        ·
          refine ⟨1559841045671604690740633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4159576121790945841975021 1559841045671604690740633)
          ·
            refine ⟨1169880784253703518055475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1559841045671604690740633 1169880784253703518055475)
            ·
              refine ⟨1754821176380555277083213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169880784253703518055475 1754821176380555277083213)
              ·
                refine ⟨658057941142708228906205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1754821176380555277083213 658057941142708228906205)
                ·
                  refine ⟨246771727928515585839827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658057941142708228906205 246771727928515585839827)
                  ·
                    rfl

theorem cell21_1081319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 3].length) (baseStart_1081319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081319 prefixEnd_1081319 := by exact prefixLift 1081319
  have htrace : WordTrace (prefixWord ++ tailWord_1081319) baseStart_1081319 baseEnd_1081319 := by
    simpa [prefixWord, tailWord_1081319, baseEnd_1081319] using wordTrace_append hprefix tailTrace_1081319
  have hstable : (prefixWord ++ tailWord_1081319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081319).length < 2 ^ (prefixWord ++ tailWord_1081319).sum := by decide
  have hdescent : baseEnd_1081319 < baseStart_1081319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081434 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1081434 : Nat := 118140960795 + 1081434 * 2 ^ 59
def prefixEnd_1081434 : Nat := 4983230072969 + 3 ^ 40 * 1081434 * 2
def baseEnd_1081434 : Nat := 246797972495300941422925

theorem tailTrace_1081434 : CollatzResearch.WordTrace tailWord_1081434 prefixEnd_1081434 246797972495300941422925 := by
  unfold tailWord_1081434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860784591039196767012839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26295425576104524712034237 9860784591039196767012839)
  ·
    refine ⟨14791176886558795150519259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9860784591039196767012839 14791176886558795150519259)
    ·
      refine ⟨22186765329838192725778889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14791176886558795150519259 22186765329838192725778889)
      ·
        refine ⟨16640073997378644544334167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22186765329838192725778889 16640073997378644544334167)
        ·
          refine ⟨24960110996067966816501251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16640073997378644544334167 24960110996067966816501251)
          ·
            refine ⟨37440166494101950224751877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24960110996067966816501251 37440166494101950224751877)
            ·
              refine ⟨7020031217644115667140977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37440166494101950224751877 7020031217644115667140977)
              ·
                refine ⟨5265023413233086750355733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7020031217644115667140977 5265023413233086750355733)
                ·
                  refine ⟨246797972495300941422925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5265023413233086750355733 246797972495300941422925)
                  ·
                    rfl

theorem cell21_1081434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1081434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081434 prefixEnd_1081434 := by exact prefixLift 1081434
  have htrace : WordTrace (prefixWord ++ tailWord_1081434) baseStart_1081434 baseEnd_1081434 := by
    simpa [prefixWord, tailWord_1081434, baseEnd_1081434] using wordTrace_append hprefix tailTrace_1081434
  have hstable : (prefixWord ++ tailWord_1081434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081434).length < 2 ^ (prefixWord ++ tailWord_1081434).sum := by decide
  have hdescent : baseEnd_1081434 < baseStart_1081434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081468 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_1081468 : Nat := 118140960795 + 1081468 * 2 ^ 59
def prefixEnd_1081468 : Nat := 4983230072969 + 3 ^ 40 * 1081468 * 2
def baseEnd_1081468 : Nat := 246805731758524437856189

theorem tailTrace_1081468 : CollatzResearch.WordTrace tailWord_1081468 prefixEnd_1081468 246805731758524437856189 := by
  unfold tailWord_1081468
  simp only [CollatzResearch.WordTrace]
  refine ⟨19722189223016805437394529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26296252297355740583192705 19722189223016805437394529)
  ·
    refine ⟨14791641917262604078045897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19722189223016805437394529 14791641917262604078045897)
    ·
      refine ⟨11093731437946953058534423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14791641917262604078045897 11093731437946953058534423)
      ·
        refine ⟨16640597156920429587801635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11093731437946953058534423 16640597156920429587801635)
        ·
          refine ⟨24960895735380644381702453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16640597156920429587801635 24960895735380644381702453)
          ·
            refine ⟨2340083975191935410784605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24960895735380644381702453 2340083975191935410784605)
            ·
              refine ⟨877531490696975779044227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2340083975191935410784605 877531490696975779044227)
              ·
                refine ⟨1316297236045463668566341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877531490696975779044227 1316297236045463668566341)
                ·
                  refine ⟨246805731758524437856189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1316297236045463668566341 246805731758524437856189)
                  ·
                    rfl

theorem cell21_1081468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_1081468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081468 prefixEnd_1081468 := by exact prefixLift 1081468
  have htrace : WordTrace (prefixWord ++ tailWord_1081468) baseStart_1081468 baseEnd_1081468 := by
    simpa [prefixWord, tailWord_1081468, baseEnd_1081468] using wordTrace_append hprefix tailTrace_1081468
  have hstable : (prefixWord ++ tailWord_1081468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081468).length < 2 ^ (prefixWord ++ tailWord_1081468).sum := by decide
  have hdescent : baseEnd_1081468 < baseStart_1081468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081482 : List Nat := [3, 1, 2, 3, 1, 2, 4, 5]
def baseStart_1081482 : Nat := 118140960795 + 1081482 * 2 ^ 59
def prefixEnd_1081482 : Nat := 4983230072969 + 3 ^ 40 * 1081482 * 2
def baseEnd_1081482 : Nat := 82269642249754508207609

theorem tailTrace_1081482 : CollatzResearch.WordTrace tailWord_1081482 prefixEnd_1081482 82269642249754508207609 := by
  unfold tailWord_1081482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861222266995722816449675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26296592711988594177199133 9861222266995722816449675)
  ·
    refine ⟨14791833400493584224674513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9861222266995722816449675 14791833400493584224674513)
    ·
      refine ⟨11093875050370188168505885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14791833400493584224674513 11093875050370188168505885)
      ·
        refine ⟨4160203143888820563189707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11093875050370188168505885 4160203143888820563189707)
        ·
          refine ⟨6240304715833230844784561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4160203143888820563189707 6240304715833230844784561)
          ·
            refine ⟨4680228536874923133588421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6240304715833230844784561 4680228536874923133588421)
            ·
              refine ⟨877542850664048087547829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4680228536874923133588421 877542850664048087547829)
              ·
                refine ⟨82269642249754508207609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877542850664048087547829 82269642249754508207609)
                ·
                  rfl

theorem cell21_1081482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_1081482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081482 prefixEnd_1081482 := by exact prefixLift 1081482
  have htrace : WordTrace (prefixWord ++ tailWord_1081482) baseStart_1081482 baseEnd_1081482 := by
    simpa [prefixWord, tailWord_1081482, baseEnd_1081482] using wordTrace_append hprefix tailTrace_1081482
  have hstable : (prefixWord ++ tailWord_1081482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081482).length < 2 ^ (prefixWord ++ tailWord_1081482).sum := by decide
  have hdescent : baseEnd_1081482 < baseStart_1081482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081527 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 4]
def baseStart_1081527 : Nat := 118140960795 + 1081527 * 2 ^ 59
def prefixEnd_1081527 : Nat := 4983230072969 + 3 ^ 40 * 1081527 * 2
def baseEnd_1081527 : Nat := 246819196362353446372735

theorem tailTrace_1081527 : CollatzResearch.WordTrace tailWord_1081527 prefixEnd_1081527 246819196362353446372735 := by
  unfold tailWord_1081527
  simp only [CollatzResearch.WordTrace]
  refine ⟨39446530352819863951186835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26297686901879909300791223 39446530352819863951186835)
  ·
    refine ⟨59169795529229795926780253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39446530352819863951186835 59169795529229795926780253)
    ·
      refine ⟨22188673323461173472542595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59169795529229795926780253 22188673323461173472542595)
      ·
        refine ⟨33283009985191760208813893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22188673323461173472542595 33283009985191760208813893)
        ·
          refine ⟨6240564372223455039152605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33283009985191760208813893 6240564372223455039152605)
          ·
            refine ⟨2340211639583795639682227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6240564372223455039152605 2340211639583795639682227)
            ·
              refine ⟨3510317459375693459523341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340211639583795639682227 3510317459375693459523341)
              ·
                refine ⟨1316369047265885047321253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3510317459375693459523341 1316369047265885047321253)
                ·
                  refine ⟨246819196362353446372735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1316369047265885047321253 246819196362353446372735)
                  ·
                    rfl

theorem cell21_1081527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_1081527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081527 prefixEnd_1081527 := by exact prefixLift 1081527
  have htrace : WordTrace (prefixWord ++ tailWord_1081527) baseStart_1081527 baseEnd_1081527 := by
    simpa [prefixWord, tailWord_1081527, baseEnd_1081527] using wordTrace_append hprefix tailTrace_1081527
  have hstable : (prefixWord ++ tailWord_1081527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081527).length < 2 ^ (prefixWord ++ tailWord_1081527).sum := by decide
  have hdescent : baseEnd_1081527 < baseStart_1081527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081558 : List Nat := [5, 2, 1, 2, 1, 10]
def baseStart_1081558 : Nat := 118140960795 + 1081558 * 2 ^ 59
def prefixEnd_1081558 : Nat := 4983230072969 + 3 ^ 40 * 1081558 * 2
def baseEnd_1081558 : Nat := 9141713740174232642815

theorem tailTrace_1081558 : CollatzResearch.WordTrace tailWord_1081558 prefixEnd_1081558 9141713740174232642815 := by
  unfold tailWord_1081558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465478813481722265347833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26298440677138370830376885 2465478813481722265347833)
  ·
    refine ⟨1849109110111291699010875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2465478813481722265347833 1849109110111291699010875)
    ·
      refine ⟨2773663665166937548516313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1849109110111291699010875 2773663665166937548516313)
      ·
        refine ⟨2080247748875203161387235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773663665166937548516313 2080247748875203161387235)
        ·
          refine ⟨3120371623312804742080853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080247748875203161387235 3120371623312804742080853)
          ·
            refine ⟨9141713740174232642815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3120371623312804742080853 9141713740174232642815)
            ·
              rfl

theorem cell21_1081558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 10].length) (baseStart_1081558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081558 prefixEnd_1081558 := by exact prefixLift 1081558
  have htrace : WordTrace (prefixWord ++ tailWord_1081558) baseStart_1081558 baseEnd_1081558 := by
    simpa [prefixWord, tailWord_1081558, baseEnd_1081558] using wordTrace_append hprefix tailTrace_1081558
  have hstable : (prefixWord ++ tailWord_1081558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081558).length < 2 ^ (prefixWord ++ tailWord_1081558).sum := by decide
  have hdescent : baseEnd_1081558 < baseStart_1081558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081600 : List Nat := [2, 1, 1, 2, 1, 1, 4, 9]
def baseStart_1081600 : Nat := 118140960795 + 1081600 * 2 ^ 59
def prefixEnd_1081600 : Nat := 4983230072969 + 3 ^ 40 * 1081600 * 2
def baseEnd_1081600 : Nat := 82278618652307180551973

theorem tailTrace_1081600 : CollatzResearch.WordTrace tailWord_1081600 prefixEnd_1081600 82278618652307180551973 := by
  unfold tailWord_1081600
  simp only [CollatzResearch.WordTrace]
  refine ⟨19724596440777698709297127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26299461921036931612396169 19724596440777698709297127)
  ·
    refine ⟨29586894661166548063945691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19724596440777698709297127 29586894661166548063945691)
    ·
      refine ⟨44380341991749822095918537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29586894661166548063945691 44380341991749822095918537)
      ·
        refine ⟨33285256493812366571938903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44380341991749822095918537 33285256493812366571938903)
        ·
          refine ⟨49927884740718549857908355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33285256493812366571938903 49927884740718549857908355)
          ·
            refine ⟨74891827111077824786862533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49927884740718549857908355 74891827111077824786862533)
            ·
              refine ⟨14042217583327092147536725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74891827111077824786862533 14042217583327092147536725)
              ·
                refine ⟨82278618652307180551973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14042217583327092147536725 82278618652307180551973)
                ·
                  rfl

theorem cell21_1081600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_1081600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081600 prefixEnd_1081600 := by exact prefixLift 1081600
  have htrace : WordTrace (prefixWord ++ tailWord_1081600) baseStart_1081600 baseEnd_1081600 := by
    simpa [prefixWord, tailWord_1081600, baseEnd_1081600] using wordTrace_append hprefix tailTrace_1081600
  have hstable : (prefixWord ++ tailWord_1081600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081600).length < 2 ^ (prefixWord ++ tailWord_1081600).sum := by decide
  have hdescent : baseEnd_1081600 < baseStart_1081600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081800 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_1081800 : Nat := 118140960795 + 1081800 * 2 ^ 59
def prefixEnd_1081800 : Nat := 4983230072969 + 3 ^ 40 * 1081800 * 2
def baseEnd_1081800 : Nat := 246881498681765638322177

theorem tailTrace_1081800 : CollatzResearch.WordTrace tailWord_1081800 prefixEnd_1081800 246881498681765638322177 := by
  unfold tailWord_1081800
  simp only [CollatzResearch.WordTrace]
  refine ⟨19728243740415415787937427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26304324987220554383916569 19728243740415415787937427)
  ·
    refine ⟨29592365610623123681906141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19728243740415415787937427 29592365610623123681906141)
    ·
      refine ⟨11097137103983671380714803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29592365610623123681906141 11097137103983671380714803)
      ·
        refine ⟨16645705655975507071072205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11097137103983671380714803 16645705655975507071072205)
        ·
          refine ⟨6242139620990815151652077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16645705655975507071072205 6242139620990815151652077)
          ·
            refine ⟨2340802357871555681869529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6242139620990815151652077 2340802357871555681869529)
            ·
              refine ⟨1755601768403666761402147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340802357871555681869529 1755601768403666761402147)
              ·
                refine ⟨2633402652605500142103221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755601768403666761402147 2633402652605500142103221)
                ·
                  refine ⟨246881498681765638322177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2633402652605500142103221 246881498681765638322177)
                  ·
                    rfl

theorem cell21_1081800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_1081800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081800 prefixEnd_1081800 := by exact prefixLift 1081800
  have htrace : WordTrace (prefixWord ++ tailWord_1081800) baseStart_1081800 baseEnd_1081800 := by
    simpa [prefixWord, tailWord_1081800, baseEnd_1081800] using wordTrace_append hprefix tailTrace_1081800
  have hstable : (prefixWord ++ tailWord_1081800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081800).length < 2 ^ (prefixWord ++ tailWord_1081800).sum := by decide
  have hdescent : baseEnd_1081800 < baseStart_1081800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081834 : List Nat := [3, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_1081834 : Nat := 118140960795 + 1081834 * 2 ^ 59
def prefixEnd_1081834 : Nat := 4983230072969 + 3 ^ 40 * 1081834 * 2
def baseEnd_1081834 : Nat := 246889257944989134755441

theorem tailTrace_1081834 : CollatzResearch.WordTrace tailWord_1081834 prefixEnd_1081834 246889257944989134755441 := by
  unfold tailWord_1081834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9864431890676913845653139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26305151708471770255075037 9864431890676913845653139)
  ·
    refine ⟨14796647836015370768479709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9864431890676913845653139 14796647836015370768479709)
    ·
      refine ⟨5548742938505764038179891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14796647836015370768479709 5548742938505764038179891)
      ·
        refine ⟨8323114407758646057269837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5548742938505764038179891 8323114407758646057269837)
        ·
          refine ⟨3121167902909492271476189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8323114407758646057269837 3121167902909492271476189)
          ·
            refine ⟨1170437963591059601803571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3121167902909492271476189 1170437963591059601803571)
            ·
              refine ⟨1755656945386589402705357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170437963591059601803571 1755656945386589402705357)
              ·
                refine ⟨658371354519971026014509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755656945386589402705357 658371354519971026014509)
                ·
                  refine ⟨246889257944989134755441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658371354519971026014509 246889257944989134755441)
                  ·
                    rfl

theorem cell21_1081834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_1081834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081834 prefixEnd_1081834 := by exact prefixLift 1081834
  have htrace : WordTrace (prefixWord ++ tailWord_1081834) baseStart_1081834 baseEnd_1081834 := by
    simpa [prefixWord, tailWord_1081834, baseEnd_1081834] using wordTrace_append hprefix tailTrace_1081834
  have hstable : (prefixWord ++ tailWord_1081834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081834).length < 2 ^ (prefixWord ++ tailWord_1081834).sum := by decide
  have hdescent : baseEnd_1081834 < baseStart_1081834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081873 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 8]
def baseStart_1081873 : Nat := 118140960795 + 1081873 * 2 ^ 59
def prefixEnd_1081873 : Nat := 4983230072969 + 3 ^ 40 * 1081873 * 2
def baseEnd_1081873 : Nat := 246898158276333733605361

theorem tailTrace_1081873 : CollatzResearch.WordTrace tailWord_1081873 prefixEnd_1081873 246898158276333733605361 := by
  unfold tailWord_1081873
  simp only [CollatzResearch.WordTrace]
  refine ⟨39459150009566365043282273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26306100006377576695521515 39459150009566365043282273)
  ·
    refine ⟨29594362507174773782461705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39459150009566365043282273 29594362507174773782461705)
    ·
      refine ⟨22195771880381080336846279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29594362507174773782461705 22195771880381080336846279)
      ·
        refine ⟨33293657820571620505269419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22195771880381080336846279 33293657820571620505269419)
        ·
          refine ⟨49940486730857430757904129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33293657820571620505269419 49940486730857430757904129)
          ·
            refine ⟨37455365048143073068428097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49940486730857430757904129 37455365048143073068428097)
            ·
              refine ⟨28091523786107304801321073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37455365048143073068428097 28091523786107304801321073)
              ·
                refine ⟨21068642839580478600990805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28091523786107304801321073 21068642839580478600990805)
                ·
                  refine ⟨246898158276333733605361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21068642839580478600990805 246898158276333733605361)
                  ·
                    rfl

theorem cell21_1081873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_1081873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081873 prefixEnd_1081873 := by exact prefixLift 1081873
  have htrace : WordTrace (prefixWord ++ tailWord_1081873) baseStart_1081873 baseEnd_1081873 := by
    simpa [prefixWord, tailWord_1081873, baseEnd_1081873] using wordTrace_append hprefix tailTrace_1081873
  have hstable : (prefixWord ++ tailWord_1081873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081873).length < 2 ^ (prefixWord ++ tailWord_1081873).sum := by decide
  have hdescent : baseEnd_1081873 < baseStart_1081873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081910 : List Nat := [5, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1081910 : Nat := 118140960795 + 1081910 * 2 ^ 59
def prefixEnd_1081910 : Nat := 4983230072969 + 3 ^ 40 * 1081910 * 2
def baseEnd_1081910 : Nat := 246906602180429891488619

theorem tailTrace_1081910 : CollatzResearch.WordTrace tailWord_1081910 prefixEnd_1081910 246906602180429891488619 := by
  unfold tailWord_1081910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466281219402020022648699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26306999673621546908252789 2466281219402020022648699)
  ·
    refine ⟨3699421829103030033973049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2466281219402020022648699 3699421829103030033973049)
    ·
      refine ⟨2774566371827272525479787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3699421829103030033973049 2774566371827272525479787)
      ·
        refine ⟨4161849557740908788219681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774566371827272525479787 4161849557740908788219681)
        ·
          refine ⟨3121387168305681591164761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4161849557740908788219681 3121387168305681591164761)
          ·
            refine ⟨2341040376229261193373571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3121387168305681591164761 2341040376229261193373571)
            ·
              refine ⟨3511560564343891790060357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341040376229261193373571 3511560564343891790060357)
              ·
                refine ⟨658417605814479710636317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3511560564343891790060357 658417605814479710636317)
                ·
                  refine ⟨246906602180429891488619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658417605814479710636317 246906602180429891488619)
                  ·
                    rfl

theorem cell21_1081910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1081910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081910 prefixEnd_1081910 := by exact prefixLift 1081910
  have htrace : WordTrace (prefixWord ++ tailWord_1081910) baseStart_1081910 baseEnd_1081910 := by
    simpa [prefixWord, tailWord_1081910, baseEnd_1081910] using wordTrace_append hprefix tailTrace_1081910
  have hstable : (prefixWord ++ tailWord_1081910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081910).length < 2 ^ (prefixWord ++ tailWord_1081910).sum := by decide
  have hdescent : baseEnd_1081910 < baseStart_1081910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081921 : List Nat := [1, 2, 5, 1, 1, 2, 3, 6]
def baseStart_1081921 : Nat := 118140960795 + 1081921 * 2 ^ 59
def prefixEnd_1081921 : Nat := 4983230072969 + 3 ^ 40 * 1081921 * 2
def baseEnd_1081921 : Nat := 82303037510098772268421

theorem tailTrace_1081921 : CollatzResearch.WordTrace tailWord_1081921 prefixEnd_1081921 82303037510098772268421 := by
  unfold tailWord_1081921
  simp only [CollatzResearch.WordTrace]
  refine ⟨39460900713392469241029617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26307267142261646160686411 39460900713392469241029617)
  ·
    refine ⟨29595675535044351930772213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39460900713392469241029617 29595675535044351930772213)
    ·
      refine ⟨2774594581410407993509895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29595675535044351930772213 2774594581410407993509895)
      ·
        refine ⟨4161891872115611990264843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774594581410407993509895 4161891872115611990264843)
        ·
          refine ⟨6242837808173417985397265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161891872115611990264843 6242837808173417985397265)
          ·
            refine ⟨4682128356130063489047949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6242837808173417985397265 4682128356130063489047949)
            ·
              refine ⟨1755798133548773808392981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4682128356130063489047949 1755798133548773808392981)
              ·
                refine ⟨82303037510098772268421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1755798133548773808392981 82303037510098772268421)
                ·
                  rfl

theorem cell21_1081921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 6].length) (baseStart_1081921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081921 prefixEnd_1081921 := by exact prefixLift 1081921
  have htrace : WordTrace (prefixWord ++ tailWord_1081921) baseStart_1081921 baseEnd_1081921 := by
    simpa [prefixWord, tailWord_1081921, baseEnd_1081921] using wordTrace_append hprefix tailTrace_1081921
  have hstable : (prefixWord ++ tailWord_1081921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081921).length < 2 ^ (prefixWord ++ tailWord_1081921).sum := by decide
  have hdescent : baseEnd_1081921 < baseStart_1081921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1081952 : List Nat := [2, 1, 1, 3, 2, 1, 3, 5, 3]
def baseStart_1081952 : Nat := 118140960795 + 1081952 * 2 ^ 59
def prefixEnd_1081952 : Nat := 4983230072969 + 3 ^ 40 * 1081952 * 2
def baseEnd_1081952 : Nat := 246916187152647151788533

theorem tailTrace_1081952 : CollatzResearch.WordTrace tailWord_1081952 prefixEnd_1081952 246916187152647151788533 := by
  unfold tailWord_1081952
  simp only [CollatzResearch.WordTrace]
  refine ⟨19731015688140080767704055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26308020917520107690272073 19731015688140080767704055)
  ·
    refine ⟨29596523532210121151556083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19731015688140080767704055 29596523532210121151556083)
    ·
      refine ⟨44394785298315181727334125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29596523532210121151556083 44394785298315181727334125)
      ·
        refine ⟨16648044486868193147750297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44394785298315181727334125 16648044486868193147750297)
        ·
          refine ⟨12486033365151144860812723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16648044486868193147750297 12486033365151144860812723)
          ·
            refine ⟨18729050047726717291219085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12486033365151144860812723 18729050047726717291219085)
            ·
              refine ⟨7023393767897518984207157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18729050047726717291219085 7023393767897518984207157)
              ·
                refine ⟨658443165740392404769421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7023393767897518984207157 658443165740392404769421)
                ·
                  refine ⟨246916187152647151788533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658443165740392404769421 246916187152647151788533)
                  ·
                    rfl

theorem cell21_1081952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_1081952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1081952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1081952 prefixEnd_1081952 := by exact prefixLift 1081952
  have htrace : WordTrace (prefixWord ++ tailWord_1081952) baseStart_1081952 baseEnd_1081952 := by
    simpa [prefixWord, tailWord_1081952, baseEnd_1081952] using wordTrace_append hprefix tailTrace_1081952
  have hstable : (prefixWord ++ tailWord_1081952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1081952).length < 2 ^ (prefixWord ++ tailWord_1081952).sum := by decide
  have hdescent : baseEnd_1081952 < baseStart_1081952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1081952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082042 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_1082042 : Nat := 118140960795 + 1082042 * 2 ^ 59
def prefixEnd_1082042 : Nat := 4983230072969 + 3 ^ 40 * 1082042 * 2
def baseEnd_1082042 : Nat := 246936726378826995288349

theorem tailTrace_1082042 : CollatzResearch.WordTrace tailWord_1082042 prefixEnd_1082042 246936726378826995288349 := by
  unfold tailWord_1082042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9866328486488526726546095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26310209297302737937456253 9866328486488526726546095)
  ·
    refine ⟨14799492729732790089819143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9866328486488526726546095 14799492729732790089819143)
    ·
      refine ⟨22199239094599185134728715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14799492729732790089819143 22199239094599185134728715)
      ·
        refine ⟨33298858641898777702093073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22199239094599185134728715 33298858641898777702093073)
        ·
          refine ⟨24974143981424083276569805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33298858641898777702093073 24974143981424083276569805)
          ·
            refine ⟨9365303993034031228713677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24974143981424083276569805 9365303993034031228713677)
            ·
              refine ⟨3511988997387761710767629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9365303993034031228713677 3511988997387761710767629)
              ·
                refine ⟨1316995874020410641537861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3511988997387761710767629 1316995874020410641537861)
                ·
                  refine ⟨246936726378826995288349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1316995874020410641537861 246936726378826995288349)
                  ·
                    rfl

theorem cell21_1082042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_1082042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082042 prefixEnd_1082042 := by exact prefixLift 1082042
  have htrace : WordTrace (prefixWord ++ tailWord_1082042) baseStart_1082042 baseEnd_1082042 := by
    simpa [prefixWord, tailWord_1082042, baseEnd_1082042] using wordTrace_append hprefix tailTrace_1082042
  have hstable : (prefixWord ++ tailWord_1082042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082042).length < 2 ^ (prefixWord ++ tailWord_1082042).sum := by decide
  have hdescent : baseEnd_1082042 < baseStart_1082042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082056 : List Nat := [2, 1, 3, 1, 2, 3, 2, 7]
def baseStart_1082056 : Nat := 118140960795 + 1082056 * 2 ^ 59
def prefixEnd_1082056 : Nat := 4983230072969 + 3 ^ 40 * 1082056 * 2
def baseEnd_1082056 : Nat := 82313307123188694018329

theorem tailTrace_1082056 : CollatzResearch.WordTrace tailWord_1082056 prefixEnd_1082056 82313307123188694018329 := by
  unfold tailWord_1082056
  simp only [CollatzResearch.WordTrace]
  refine ⟨19732912283951693648597011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26310549711935591531462681 19732912283951693648597011)
  ·
    refine ⟨29599368425927540472895517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19732912283951693648597011 29599368425927540472895517)
    ·
      refine ⟨11099763159722827677335819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29599368425927540472895517 11099763159722827677335819)
      ·
        refine ⟨16649644739584241516003729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11099763159722827677335819 16649644739584241516003729)
        ·
          refine ⟨12487233554688181137002797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16649644739584241516003729 12487233554688181137002797)
          ·
            refine ⟨4682712583008067926376049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12487233554688181137002797 4682712583008067926376049)
            ·
              refine ⟨3512034437256050944782037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4682712583008067926376049 3512034437256050944782037)
              ·
                refine ⟨82313307123188694018329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3512034437256050944782037 82313307123188694018329)
                ·
                  rfl

theorem cell21_1082056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_1082056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082056 prefixEnd_1082056 := by exact prefixLift 1082056
  have htrace : WordTrace (prefixWord ++ tailWord_1082056) baseStart_1082056 baseEnd_1082056 := by
    simpa [prefixWord, tailWord_1082056, baseEnd_1082056] using wordTrace_append hprefix tailTrace_1082056
  have hstable : (prefixWord ++ tailWord_1082056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082056).length < 2 ^ (prefixWord ++ tailWord_1082056).sum := by decide
  have hdescent : baseEnd_1082056 < baseStart_1082056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082076 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1082076 : Nat := 118140960795 + 1082076 * 2 ^ 59
def prefixEnd_1082076 : Nat := 4983230072969 + 3 ^ 40 * 1082076 * 2
def baseEnd_1082076 : Nat := 246944485642050491721613

theorem tailTrace_1082076 : CollatzResearch.WordTrace tailWord_1082076 prefixEnd_1082076 246944485642050491721613 := by
  unfold tailWord_1082076
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733277013915465356461041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26311036018553953808614721 19733277013915465356461041)
  ·
    refine ⟨14799957760436599017345781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19733277013915465356461041 14799957760436599017345781)
    ·
      refine ⟨1387496040040931157876167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14799957760436599017345781 1387496040040931157876167)
      ·
        refine ⟨2081244060061396736814251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1387496040040931157876167 2081244060061396736814251)
        ·
          refine ⟨3121866090092095105221377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081244060061396736814251 3121866090092095105221377)
          ·
            refine ⟨2341399567569071328916033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3121866090092095105221377 2341399567569071328916033)
            ·
              refine ⟨1756049675676803496687025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341399567569071328916033 1756049675676803496687025)
              ·
                refine ⟨1317037256757602622515269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1756049675676803496687025 1317037256757602622515269)
                ·
                  refine ⟨246944485642050491721613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317037256757602622515269 246944485642050491721613)
                  ·
                    rfl

theorem cell21_1082076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1082076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082076 prefixEnd_1082076 := by exact prefixLift 1082076
  have htrace : WordTrace (prefixWord ++ tailWord_1082076) baseStart_1082076 baseEnd_1082076 := by
    simpa [prefixWord, tailWord_1082076, baseEnd_1082076] using wordTrace_append hprefix tailTrace_1082076
  have hstable : (prefixWord ++ tailWord_1082076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082076).length < 2 ^ (prefixWord ++ tailWord_1082076).sum := by decide
  have hdescent : baseEnd_1082076 < baseStart_1082076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082163 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 5]
def baseStart_1082163 : Nat := 118140960795 + 1082163 * 2 ^ 59
def prefixEnd_1082163 : Nat := 4983230072969 + 3 ^ 40 * 1082163 * 2
def baseEnd_1082163 : Nat := 246964340227357673771435

theorem tailTrace_1082163 : CollatzResearch.WordTrace tailWord_1082163 prefixEnd_1082163 246964340227357673771435 := by
  unfold tailWord_1082163
  simp only [CollatzResearch.WordTrace]
  refine ⟨39469727178515744571339143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26313151452343829714226095 39469727178515744571339143)
  ·
    refine ⟨59204590767773616857008715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39469727178515744571339143 59204590767773616857008715)
    ·
      refine ⟨88806886151660425285513073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59204590767773616857008715 88806886151660425285513073)
      ·
        refine ⟨66605164613745318964134805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88806886151660425285513073 66605164613745318964134805)
        ·
          refine ⟨3122117091269311826443819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66605164613745318964134805 3122117091269311826443819)
          ·
            refine ⟨4683175636903967739665729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122117091269311826443819 4683175636903967739665729)
            ·
              refine ⟨3512381727677975804749297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4683175636903967739665729 3512381727677975804749297)
              ·
                refine ⟨2634286295758481853561973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3512381727677975804749297 2634286295758481853561973)
                ·
                  refine ⟨246964340227357673771435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2634286295758481853561973 246964340227357673771435)
                  ·
                    rfl

theorem cell21_1082163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_1082163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082163 prefixEnd_1082163 := by exact prefixLift 1082163
  have htrace : WordTrace (prefixWord ++ tailWord_1082163) baseStart_1082163 baseEnd_1082163 := by
    simpa [prefixWord, tailWord_1082163, baseEnd_1082163] using wordTrace_append hprefix tailTrace_1082163
  have hstable : (prefixWord ++ tailWord_1082163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082163).length < 2 ^ (prefixWord ++ tailWord_1082163).sum := by decide
  have hdescent : baseEnd_1082163 < baseStart_1082163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082166 : List Nat := [5, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1082166 : Nat := 118140960795 + 1082166 * 2 ^ 59
def prefixEnd_1082166 : Nat := 4983230072969 + 3 ^ 40 * 1082166 * 2
def baseEnd_1082166 : Nat := 82321674956076778407143

theorem tailTrace_1082166 : CollatzResearch.WordTrace tailWord_1082166 prefixEnd_1082166 82321674956076778407143 := by
  unfold tailWord_1082166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466864787344054755231147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26313224398336584055798901 2466864787344054755231147)
  ·
    refine ⟨3700297181016082132846721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2466864787344054755231147 3700297181016082132846721)
    ·
      refine ⟨2775222885762061599635041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3700297181016082132846721 2775222885762061599635041)
      ·
        refine ⟨2081417164321546199726281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2775222885762061599635041 2081417164321546199726281)
        ·
          refine ⟨1561062873241159649794711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2081417164321546199726281 1561062873241159649794711)
          ·
            refine ⟨2341594309861739474692067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561062873241159649794711 2341594309861739474692067)
            ·
              refine ⟨3512391464792609212038101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341594309861739474692067 3512391464792609212038101)
              ·
                refine ⟨82321674956076778407143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3512391464792609212038101 82321674956076778407143)
                ·
                  rfl

theorem cell21_1082166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1082166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082166 prefixEnd_1082166 := by exact prefixLift 1082166
  have htrace : WordTrace (prefixWord ++ tailWord_1082166) baseStart_1082166 baseEnd_1082166 := by
    simpa [prefixWord, tailWord_1082166, baseEnd_1082166] using wordTrace_append hprefix tailTrace_1082166
  have hstable : (prefixWord ++ tailWord_1082166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082166).length < 2 ^ (prefixWord ++ tailWord_1082166).sum := by decide
  have hdescent : baseEnd_1082166 < baseStart_1082166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082194 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1082194 : Nat := 118140960795 + 1082194 * 2 ^ 59
def prefixEnd_1082194 : Nat := 4983230072969 + 3 ^ 40 * 1082194 * 2
def baseEnd_1082194 : Nat := 246971414849708508754705

theorem tailTrace_1082194 : CollatzResearch.WordTrace tailWord_1082194 prefixEnd_1082194 246971414849708508754705 := by
  unfold tailWord_1082194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9867714460350859216429409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26313905227602291243811757 9867714460350859216429409)
  ·
    refine ⟨7400785845263144412322057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9867714460350859216429409 7400785845263144412322057)
    ·
      refine ⟨5550589383947358309241543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7400785845263144412322057 5550589383947358309241543)
      ·
        refine ⟨8325884075921037463862315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5550589383947358309241543 8325884075921037463862315)
        ·
          refine ⟨12488826113881556195793473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8325884075921037463862315 12488826113881556195793473)
          ·
            refine ⟨9366619585411167146845105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12488826113881556195793473 9366619585411167146845105)
            ·
              refine ⟨7024964689058375360133829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9366619585411167146845105 7024964689058375360133829)
              ·
                refine ⟨1317180879198445380025093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7024964689058375360133829 1317180879198445380025093)
                ·
                  refine ⟨246971414849708508754705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317180879198445380025093 246971414849708508754705)
                  ·
                    rfl

theorem cell21_1082194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1082194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082194 prefixEnd_1082194 := by exact prefixLift 1082194
  have htrace : WordTrace (prefixWord ++ tailWord_1082194) baseStart_1082194 baseEnd_1082194 := by
    simpa [prefixWord, tailWord_1082194, baseEnd_1082194] using wordTrace_append hprefix tailTrace_1082194
  have hstable : (prefixWord ++ tailWord_1082194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082194).length < 2 ^ (prefixWord ++ tailWord_1082194).sum := by decide
  have hdescent : baseEnd_1082194 < baseStart_1082194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082197 : List Nat := [1, 3, 2, 2, 2, 1, 5, 2, 3]
def baseStart_1082197 : Nat := 118140960795 + 1082197 * 2 ^ 59
def prefixEnd_1082197 : Nat := 4983230072969 + 3 ^ 40 * 1082197 * 2
def baseEnd_1082197 : Nat := 246972099490581170204699

theorem tailTrace_1082197 : CollatzResearch.WordTrace tailWord_1082197 prefixEnd_1082197 246972099490581170204699 := by
  unfold tailWord_1082197
  simp only [CollatzResearch.WordTrace]
  refine ⟨39470967260392568378076845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26313978173595045585384563 39470967260392568378076845)
  ·
    refine ⟨14801612722647213141778817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39470967260392568378076845 14801612722647213141778817)
    ·
      refine ⟨11101209541985409856334113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14801612722647213141778817 11101209541985409856334113)
      ·
        refine ⟨8325907156489057392250585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11101209541985409856334113 8325907156489057392250585)
        ·
          refine ⟨6244430367366793044187939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8325907156489057392250585 6244430367366793044187939)
          ·
            refine ⟨9366645551050189566281909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6244430367366793044187939 9366645551050189566281909)
            ·
              refine ⟨878123020410955271838929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9366645551050189566281909 878123020410955271838929)
              ·
                refine ⟨658592265308216453879197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878123020410955271838929 658592265308216453879197)
                ·
                  refine ⟨246972099490581170204699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658592265308216453879197 246972099490581170204699)
                  ·
                    rfl

theorem cell21_1082197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_1082197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082197 prefixEnd_1082197 := by exact prefixLift 1082197
  have htrace : WordTrace (prefixWord ++ tailWord_1082197) baseStart_1082197 baseEnd_1082197 := by
    simpa [prefixWord, tailWord_1082197, baseEnd_1082197] using wordTrace_append hprefix tailTrace_1082197
  have hstable : (prefixWord ++ tailWord_1082197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082197).length < 2 ^ (prefixWord ++ tailWord_1082197).sum := by decide
  have hdescent : baseEnd_1082197 < baseStart_1082197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082208 : List Nat := [2, 1, 1, 3, 3, 1, 4, 6]
def baseStart_1082208 : Nat := 118140960795 + 1082208 * 2 ^ 59
def prefixEnd_1082208 : Nat := 4983230072969 + 3 ^ 40 * 1082208 * 2
def baseEnd_1082208 : Nat := 82324869946815865173781

theorem tailTrace_1082208 : CollatzResearch.WordTrace tailWord_1082208 prefixEnd_1082208 82324869946815865173781 := by
  unfold tailWord_1082208
  simp only [CollatzResearch.WordTrace]
  refine ⟨19735684231676358628363639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26314245642235144837818185 19735684231676358628363639)
  ·
    refine ⟨29603526347514537942545459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19735684231676358628363639 29603526347514537942545459)
    ·
      refine ⟨44405289521271806913818189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29603526347514537942545459 44405289521271806913818189)
      ·
        refine ⟨16651983570476927592681821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44405289521271806913818189 16651983570476927592681821)
        ·
          refine ⟨6244493838928847847255683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16651983570476927592681821 6244493838928847847255683)
          ·
            refine ⟨9366740758393271770883525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6244493838928847847255683 9366740758393271770883525)
            ·
              refine ⟨1756263892198738457040661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9366740758393271770883525 1756263892198738457040661)
              ·
                refine ⟨82324869946815865173781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1756263892198738457040661 82324869946815865173781)
                ·
                  rfl

theorem cell21_1082208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_1082208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082208 prefixEnd_1082208 := by exact prefixLift 1082208
  have htrace : WordTrace (prefixWord ++ tailWord_1082208) baseStart_1082208 baseEnd_1082208 := by
    simpa [prefixWord, tailWord_1082208, baseEnd_1082208] using wordTrace_append hprefix tailTrace_1082208
  have hstable : (prefixWord ++ tailWord_1082208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082208).length < 2 ^ (prefixWord ++ tailWord_1082208).sum := by decide
  have hdescent : baseEnd_1082208 < baseStart_1082208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082211 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 4]
def baseStart_1082211 : Nat := 118140960795 + 1082211 * 2 ^ 59
def prefixEnd_1082211 : Nat := 4983230072969 + 3 ^ 40 * 1082211 * 2
def baseEnd_1082211 : Nat := 246975294481320256971337

theorem tailTrace_1082211 : CollatzResearch.WordTrace tailWord_1082211 prefixEnd_1082211 246975294481320256971337 := by
  unfold tailWord_1082211
  simp only [CollatzResearch.WordTrace]
  refine ⟨39471477882341848769086487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26314318588227899179390991 39471477882341848769086487)
  ·
    refine ⟨59207216823512773153629731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39471477882341848769086487 59207216823512773153629731)
    ·
      refine ⟨88810825235269159730444597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59207216823512773153629731 88810825235269159730444597)
      ·
        refine ⟨8326014865806483724729181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88810825235269159730444597 8326014865806483724729181)
        ·
          refine ⟨3122255574677431396773443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8326014865806483724729181 3122255574677431396773443)
          ·
            refine ⟨4683383362016147095160165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122255574677431396773443 4683383362016147095160165)
            ·
              refine ⟨878134380378027580342531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4683383362016147095160165 878134380378027580342531)
              ·
                refine ⟨1317201570567041370513797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878134380378027580342531 1317201570567041370513797)
                ·
                  refine ⟨246975294481320256971337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317201570567041370513797 246975294481320256971337)
                  ·
                    rfl

theorem cell21_1082211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 4].length) (baseStart_1082211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082211 prefixEnd_1082211 := by exact prefixLift 1082211
  have htrace : WordTrace (prefixWord ++ tailWord_1082211) baseStart_1082211 baseEnd_1082211 := by
    simpa [prefixWord, tailWord_1082211, baseEnd_1082211] using wordTrace_append hprefix tailTrace_1082211
  have hstable : (prefixWord ++ tailWord_1082211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082211).length < 2 ^ (prefixWord ++ tailWord_1082211).sum := by decide
  have hdescent : baseEnd_1082211 < baseStart_1082211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082242 : List Nat := [3, 4, 2, 2, 1, 9]
def baseStart_1082242 : Nat := 118140960795 + 1082242 * 2 ^ 59
def prefixEnd_1082242 : Nat := 4983230072969 + 3 ^ 40 * 1082242 * 2
def baseEnd_1082242 : Nat := 9147495151987818220541

theorem tailTrace_1082242 : CollatzResearch.WordTrace tailWord_1082242 prefixEnd_1082242 9147495151987818220541 := by
  unfold tailWord_1082242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868152136307385265866245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26315072363486360708976653 9868152136307385265866245)
  ·
    refine ⟨1850278525557634737349921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9868152136307385265866245 1850278525557634737349921)
    ·
      refine ⟨1387708894168226053012441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1850278525557634737349921 1387708894168226053012441)
      ·
        refine ⟨1040781670626169539759331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1387708894168226053012441 1040781670626169539759331)
        ·
          refine ⟨1561172505939254309638997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040781670626169539759331 1561172505939254309638997)
          ·
            refine ⟨9147495151987818220541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1561172505939254309638997 9147495151987818220541)
            ·
              rfl

theorem cell21_1082242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 9].length) (baseStart_1082242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082242 prefixEnd_1082242 := by exact prefixLift 1082242
  have htrace : WordTrace (prefixWord ++ tailWord_1082242) baseStart_1082242 baseEnd_1082242 := by
    simpa [prefixWord, tailWord_1082242, baseEnd_1082242] using wordTrace_append hprefix tailTrace_1082242
  have hstable : (prefixWord ++ tailWord_1082242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082242).length < 2 ^ (prefixWord ++ tailWord_1082242).sum := by decide
  have hdescent : baseEnd_1082242 < baseStart_1082242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082298 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1082298 : Nat := 118140960795 + 1082298 * 2 ^ 59
def prefixEnd_1082298 : Nat := 4983230072969 + 3 ^ 40 * 1082298 * 2
def baseEnd_1082298 : Nat := 246995149066627439021159

theorem tailTrace_1082298 : CollatzResearch.WordTrace tailWord_1082298 prefixEnd_1082298 246995149066627439021159 := by
  unfold tailWord_1082298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868662758256665656875887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26316434022017775085002365 9868662758256665656875887)
  ·
    refine ⟨14802994137384998485313831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9868662758256665656875887 14802994137384998485313831)
    ·
      refine ⟨22204491206077497727970747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14802994137384998485313831 22204491206077497727970747)
      ·
        refine ⟨33306736809116246591956121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22204491206077497727970747 33306736809116246591956121)
        ·
          refine ⟨24980052606837184943967091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33306736809116246591956121 24980052606837184943967091)
          ·
            refine ⟨37470078910255777415950637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24980052606837184943967091 37470078910255777415950637)
            ·
              refine ⟨14051279591345916530981489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37470078910255777415950637 14051279591345916530981489)
              ·
                refine ⟨10538459693509437398236117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14051279591345916530981489 10538459693509437398236117)
                ·
                  refine ⟨246995149066627439021159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10538459693509437398236117 246995149066627439021159)
                  ·
                    rfl

theorem cell21_1082298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1082298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082298 prefixEnd_1082298 := by exact prefixLift 1082298
  have htrace : WordTrace (prefixWord ++ tailWord_1082298) baseStart_1082298 baseEnd_1082298 := by
    simpa [prefixWord, tailWord_1082298, baseEnd_1082298] using wordTrace_append hprefix tailTrace_1082298
  have hstable : (prefixWord ++ tailWord_1082298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082298).length < 2 ^ (prefixWord ++ tailWord_1082298).sum := by decide
  have hdescent : baseEnd_1082298 < baseStart_1082298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082315 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 5]
def baseStart_1082315 : Nat := 118140960795 + 1082315 * 2 ^ 59
def prefixEnd_1082315 : Nat := 4983230072969 + 3 ^ 40 * 1082315 * 2
def baseEnd_1082315 : Nat := 246999028698239187237791

theorem tailTrace_1082315 : CollatzResearch.WordTrace tailWord_1082315 prefixEnd_1082315 246999028698239187237791 := by
  unfold tailWord_1082315
  simp only [CollatzResearch.WordTrace]
  refine ⟨39475271073965074530872399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26316847382643383020581599 39475271073965074530872399)
  ·
    refine ⟨59212906610947611796308599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39475271073965074530872399 59212906610947611796308599)
    ·
      refine ⟨88819359916421417694462899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59212906610947611796308599 88819359916421417694462899)
      ·
        refine ⟨133229039874632126541694349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88819359916421417694462899 133229039874632126541694349)
        ·
          refine ⟨49960889952987047453135381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133229039874632126541694349 49960889952987047453135381)
          ·
            refine ⟨2341916716546267849365721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49960889952987047453135381 2341916716546267849365721)
            ·
              refine ⟨1756437537409700887024291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341916716546267849365721 1756437537409700887024291)
              ·
                refine ⟨2634656306114551330536437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756437537409700887024291 2634656306114551330536437)
                ·
                  refine ⟨246999028698239187237791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2634656306114551330536437 246999028698239187237791)
                  ·
                    rfl

theorem cell21_1082315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_1082315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082315 prefixEnd_1082315 := by exact prefixLift 1082315
  have htrace : WordTrace (prefixWord ++ tailWord_1082315) baseStart_1082315 baseEnd_1082315 := by
    simpa [prefixWord, tailWord_1082315, baseEnd_1082315] using wordTrace_append hprefix tailTrace_1082315
  have hstable : (prefixWord ++ tailWord_1082315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082315).length < 2 ^ (prefixWord ++ tailWord_1082315).sum := by decide
  have hdescent : baseEnd_1082315 < baseStart_1082315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082366 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1082366 : Nat := 118140960795 + 1082366 * 2 ^ 59
def prefixEnd_1082366 : Nat := 4983230072969 + 3 ^ 40 * 1082366 * 2
def baseEnd_1082366 : Nat := 247010667593074431887687

theorem tailTrace_1082366 : CollatzResearch.WordTrace tailWord_1082366 prefixEnd_1082366 247010667593074431887687 := by
  unfold tailWord_1082366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4934641399597538780122369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26318087464520206827319301 4934641399597538780122369)
  ·
    refine ⟨3700981049698154085091777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4934641399597538780122369 3700981049698154085091777)
    ·
      refine ⟨2775735787273615563818833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3700981049698154085091777 2775735787273615563818833)
      ·
        refine ⟨2081801840455211672864125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2775735787273615563818833 2081801840455211672864125)
        ·
          refine ⟨780675690170704377324047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2081801840455211672864125 780675690170704377324047)
          ·
            refine ⟨1171013535256056565986071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780675690170704377324047 1171013535256056565986071)
            ·
              refine ⟨1756520302884084848979107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171013535256056565986071 1756520302884084848979107)
              ·
                refine ⟨2634780454326127273468661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756520302884084848979107 2634780454326127273468661)
                ·
                  refine ⟨247010667593074431887687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2634780454326127273468661 247010667593074431887687)
                  ·
                    rfl

theorem cell21_1082366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1082366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082366 prefixEnd_1082366 := by exact prefixLift 1082366
  have htrace : WordTrace (prefixWord ++ tailWord_1082366) baseStart_1082366 baseEnd_1082366 := by
    simpa [prefixWord, tailWord_1082366, baseEnd_1082366] using wordTrace_append hprefix tailTrace_1082366
  have hstable : (prefixWord ++ tailWord_1082366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082366).length < 2 ^ (prefixWord ++ tailWord_1082366).sum := by decide
  have hdescent : baseEnd_1082366 < baseStart_1082366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082425 : List Nat := [1, 2, 1, 5, 2, 1, 4, 2, 3]
def baseStart_1082425 : Nat := 118140960795 + 1082425 * 2 ^ 59
def prefixEnd_1082425 : Nat := 4983230072969 + 3 ^ 40 * 1082425 * 2
def baseEnd_1082425 : Nat := 247024132196903440404233

theorem tailTrace_1082425 : CollatzResearch.WordTrace tailWord_1082425 prefixEnd_1082425 247024132196903440404233 := by
  unfold tailWord_1082425
  simp only [CollatzResearch.WordTrace]
  refine ⟨39479283103566563317376729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26319522069044375544917819 39479283103566563317376729)
  ·
    refine ⟨29609462327674922488032547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39479283103566563317376729 29609462327674922488032547)
    ·
      refine ⟨44414193491512383732048821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29609462327674922488032547 44414193491512383732048821)
      ·
        refine ⟨4163830639829285974879577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44414193491512383732048821 4163830639829285974879577)
        ·
          refine ⟨3122872979871964481159683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4163830639829285974879577 3122872979871964481159683)
          ·
            refine ⟨4684309469807946721739525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122872979871964481159683 4684309469807946721739525)
            ·
              refine ⟨878308025588990010326161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4684309469807946721739525 878308025588990010326161)
              ·
                refine ⟨658731019191742507744621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878308025588990010326161 658731019191742507744621)
                ·
                  refine ⟨247024132196903440404233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658731019191742507744621 247024132196903440404233)
                  ·
                    rfl

theorem cell21_1082425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_1082425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082425 prefixEnd_1082425 := by exact prefixLift 1082425
  have htrace : WordTrace (prefixWord ++ tailWord_1082425) baseStart_1082425 baseEnd_1082425 := by
    simpa [prefixWord, tailWord_1082425, baseEnd_1082425] using wordTrace_append hprefix tailTrace_1082425
  have hstable : (prefixWord ++ tailWord_1082425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082425).length < 2 ^ (prefixWord ++ tailWord_1082425).sum := by decide
  have hdescent : baseEnd_1082425 < baseStart_1082425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082481 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 4]
def baseStart_1082481 : Nat := 118140960795 + 1082481 * 2 ^ 59
def prefixEnd_1082481 : Nat := 4983230072969 + 3 ^ 40 * 1082481 * 2
def baseEnd_1082481 : Nat := 247036912159859787470785

theorem tailTrace_1082481 : CollatzResearch.WordTrace tailWord_1082481 prefixEnd_1082481 247036912159859787470785 := by
  unfold tailWord_1082481
  simp only [CollatzResearch.WordTrace]
  refine ⟨39481325591363684881415297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26320883727575789920943531 39481325591363684881415297)
  ·
    refine ⟨29610994193522763661061473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39481325591363684881415297 29610994193522763661061473)
    ·
      refine ⟨22208245645142072745796105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29610994193522763661061473 22208245645142072745796105)
      ·
        refine ⟨16656184233856554559347079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22208245645142072745796105 16656184233856554559347079)
        ·
          refine ⟨24984276350784831839020619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16656184233856554559347079 24984276350784831839020619)
          ·
            refine ⟨37476414526177247758530929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24984276350784831839020619 37476414526177247758530929)
            ·
              refine ⟨28107310894632935818898197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37476414526177247758530929 28107310894632935818898197)
              ·
                refine ⟨1317530198185918866510853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28107310894632935818898197 1317530198185918866510853)
                ·
                  refine ⟨247036912159859787470785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317530198185918866510853 247036912159859787470785)
                  ·
                    rfl

theorem cell21_1082481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_1082481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082481 prefixEnd_1082481 := by exact prefixLift 1082481
  have htrace : WordTrace (prefixWord ++ tailWord_1082481) baseStart_1082481 baseEnd_1082481 := by
    simpa [prefixWord, tailWord_1082481, baseEnd_1082481] using wordTrace_append hprefix tailTrace_1082481
  have hstable : (prefixWord ++ tailWord_1082481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082481).length < 2 ^ (prefixWord ++ tailWord_1082481).sum := by decide
  have hdescent : baseEnd_1082481 < baseStart_1082481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082543 : List Nat := [1, 1, 2, 1, 2, 3, 2, 6, 3]
def baseStart_1082543 : Nat := 118140960795 + 1082543 * 2 ^ 59
def prefixEnd_1082543 : Nat := 4983230072969 + 3 ^ 40 * 1082543 * 2
def baseEnd_1082543 : Nat := 247051061404561457437325

theorem tailTrace_1082543 : CollatzResearch.WordTrace tailWord_1082543 prefixEnd_1082543 247051061404561457437325 := by
  unfold tailWord_1082543
  simp only [CollatzResearch.WordTrace]
  refine ⟨39483586917139069470172283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26322391278092712980114855 39483586917139069470172283)
  ·
    refine ⟨59225380375708604205258425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39483586917139069470172283 59225380375708604205258425)
    ·
      refine ⟨44419035281781453153943819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59225380375708604205258425 44419035281781453153943819)
      ·
        refine ⟨66628552922672179730915729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44419035281781453153943819 66628552922672179730915729)
        ·
          refine ⟨49971414692004134798186797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66628552922672179730915729 49971414692004134798186797)
          ·
            refine ⟨18739280509501550549320049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49971414692004134798186797 18739280509501550549320049)
            ·
              refine ⟨14054460382126162911990037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18739280509501550549320049 14054460382126162911990037)
              ·
                refine ⟨658802830412163886499533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14054460382126162911990037 658802830412163886499533)
                ·
                  refine ⟨247051061404561457437325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658802830412163886499533 247051061404561457437325)
                  ·
                    rfl

theorem cell21_1082543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 3].length) (baseStart_1082543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082543 prefixEnd_1082543 := by exact prefixLift 1082543
  have htrace : WordTrace (prefixWord ++ tailWord_1082543) baseStart_1082543 baseEnd_1082543 := by
    simpa [prefixWord, tailWord_1082543, baseEnd_1082543] using wordTrace_append hprefix tailTrace_1082543
  have hstable : (prefixWord ++ tailWord_1082543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082543).length < 2 ^ (prefixWord ++ tailWord_1082543).sum := by decide
  have hdescent : baseEnd_1082543 < baseStart_1082543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082605 : List Nat := [1, 5, 1, 2, 2, 3, 1, 6]
def baseStart_1082605 : Nat := 118140960795 + 1082605 * 2 ^ 59
def prefixEnd_1082605 : Nat := 4983230072969 + 3 ^ 40 * 1082605 * 2
def baseEnd_1082605 : Nat := 82355070216421042467955

theorem tailTrace_1082605 : CollatzResearch.WordTrace tailWord_1082605 prefixEnd_1082605 82355070216421042467955 := by
  unfold tailWord_1082605
  simp only [CollatzResearch.WordTrace]
  refine ⟨39485848242914454058929269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26323898828609636039286179 39485848242914454058929269)
  ·
    refine ⟨3701798272773230068024619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39485848242914454058929269 3701798272773230068024619)
    ·
      refine ⟨5552697409159845102036929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3701798272773230068024619 5552697409159845102036929)
      ·
        refine ⟨4164523056869883826527697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5552697409159845102036929 4164523056869883826527697)
        ·
          refine ⟨3123392292652412869895773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4164523056869883826527697 3123392292652412869895773)
          ·
            refine ⟨1171272109744654826210915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3123392292652412869895773 1171272109744654826210915)
            ·
              refine ⟨1756908164616982239316373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171272109744654826210915 1756908164616982239316373)
              ·
                refine ⟨82355070216421042467955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1756908164616982239316373 82355070216421042467955)
                ·
                  rfl

theorem cell21_1082605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 6].length) (baseStart_1082605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082605 prefixEnd_1082605 := by exact prefixLift 1082605
  have htrace : WordTrace (prefixWord ++ tailWord_1082605) baseStart_1082605 baseEnd_1082605 := by
    simpa [prefixWord, tailWord_1082605, baseEnd_1082605] using wordTrace_append hprefix tailTrace_1082605
  have hstable : (prefixWord ++ tailWord_1082605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082605).length < 2 ^ (prefixWord ++ tailWord_1082605).sum := by decide
  have hdescent : baseEnd_1082605 < baseStart_1082605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082616 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_1082616 : Nat := 118140960795 + 1082616 * 2 ^ 59
def prefixEnd_1082616 : Nat := 4983230072969 + 3 ^ 40 * 1082616 * 2
def baseEnd_1082616 : Nat := 247067720999129552720509

theorem tailTrace_1082616 : CollatzResearch.WordTrace tailWord_1082616 prefixEnd_1082616 247067720999129552720509 := by
  unfold tailWord_1082616
  simp only [CollatzResearch.WordTrace]
  refine ⟨19743124722937301468789851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26324166297249735291719801 19743124722937301468789851)
  ·
    refine ⟨29614687084405952203184777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19743124722937301468789851 29614687084405952203184777)
    ·
      refine ⟨22211015313304464152388583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29614687084405952203184777 22211015313304464152388583)
      ·
        refine ⟨33316522969956696228582875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22211015313304464152388583 33316522969956696228582875)
        ·
          refine ⟨49974784454935044342874313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33316522969956696228582875 49974784454935044342874313)
          ·
            refine ⟨37481088341201283257155735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49974784454935044342874313 37481088341201283257155735)
            ·
              refine ⟨56221632511801924885733603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37481088341201283257155735 56221632511801924885733603)
              ·
                refine ⟨84332448767702887328600405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56221632511801924885733603 84332448767702887328600405)
                ·
                  refine ⟨247067720999129552720509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84332448767702887328600405 247067720999129552720509)
                  ·
                    rfl

theorem cell21_1082616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_1082616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082616 prefixEnd_1082616 := by exact prefixLift 1082616
  have htrace : WordTrace (prefixWord ++ tailWord_1082616) baseStart_1082616 baseEnd_1082616 := by
    simpa [prefixWord, tailWord_1082616, baseEnd_1082616] using wordTrace_append hprefix tailTrace_1082616
  have hstable : (prefixWord ++ tailWord_1082616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082616).length < 2 ^ (prefixWord ++ tailWord_1082616).sum := by decide
  have hdescent : baseEnd_1082616 < baseStart_1082616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082636 : List Nat := [2, 2, 1, 2, 2, 4, 2, 3, 3]
def baseStart_1082636 : Nat := 118140960795 + 1082636 * 2 ^ 59
def prefixEnd_1082636 : Nat := 4983230072969 + 3 ^ 40 * 1082636 * 2
def baseEnd_1082636 : Nat := 247072285271613962387135

theorem tailTrace_1082636 : CollatzResearch.WordTrace tailWord_1082636 prefixEnd_1082636 247072285271613962387135 := by
  unfold tailWord_1082636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19743489452901073176653881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26324652603868097568871841 19743489452901073176653881)
  ·
    refine ⟨14807617089675804882490411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19743489452901073176653881 14807617089675804882490411)
    ·
      refine ⟨22211425634513707323735617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14807617089675804882490411 22211425634513707323735617)
      ·
        refine ⟨16658569225885280492801713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22211425634513707323735617 16658569225885280492801713)
        ·
          refine ⟨12493926919413960369601285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16658569225885280492801713 12493926919413960369601285)
          ·
            refine ⟨2342611297390117569300241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12493926919413960369601285 2342611297390117569300241)
            ·
              refine ⟨1756958473042588176975181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2342611297390117569300241 1756958473042588176975181)
              ·
                refine ⟨658859427390970566365693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1756958473042588176975181 658859427390970566365693)
                ·
                  refine ⟨247072285271613962387135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658859427390970566365693 247072285271613962387135)
                  ·
                    rfl

theorem cell21_1082636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_1082636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082636 prefixEnd_1082636 := by exact prefixLift 1082636
  have htrace : WordTrace (prefixWord ++ tailWord_1082636) baseStart_1082636 baseEnd_1082636 := by
    simpa [prefixWord, tailWord_1082636, baseEnd_1082636] using wordTrace_append hprefix tailTrace_1082636
  have hstable : (prefixWord ++ tailWord_1082636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082636).length < 2 ^ (prefixWord ++ tailWord_1082636).sum := by decide
  have hdescent : baseEnd_1082636 < baseStart_1082636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082647 : List Nat := [1, 1, 3, 4, 1, 1, 10]
def baseStart_1082647 : Nat := 118140960795 + 1082647 * 2 ^ 59
def prefixEnd_1082647 : Nat := 4983230072969 + 3 ^ 40 * 1082647 * 2
def baseEnd_1082647 : Nat := 27452755069053376411531

theorem tailTrace_1082647 : CollatzResearch.WordTrace tailWord_1082647 prefixEnd_1082647 27452755069053376411531 := by
  unfold tailWord_1082647
  simp only [CollatzResearch.WordTrace]
  refine ⟨39487380108762295231958195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26324920072508196821305463 39487380108762295231958195)
  ·
    refine ⟨59231070163143442847937293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39487380108762295231958195 59231070163143442847937293)
    ·
      refine ⟨22211651311178791067976485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59231070163143442847937293 22211651311178791067976485)
      ·
        refine ⟨4164684620846023325245591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22211651311178791067976485 4164684620846023325245591)
        ·
          refine ⟨6247026931269034987868387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164684620846023325245591 6247026931269034987868387)
          ·
            refine ⟨9370540396903552481802581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247026931269034987868387 9370540396903552481802581)
            ·
              refine ⟨27452755069053376411531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9370540396903552481802581 27452755069053376411531)
              ·
                rfl

theorem cell21_1082647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 10].length) (baseStart_1082647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082647 prefixEnd_1082647 := by exact prefixLift 1082647
  have htrace : WordTrace (prefixWord ++ tailWord_1082647) baseStart_1082647 baseEnd_1082647 := by
    simpa [prefixWord, tailWord_1082647, baseEnd_1082647] using wordTrace_append hprefix tailTrace_1082647
  have hstable : (prefixWord ++ tailWord_1082647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082647).length < 2 ^ (prefixWord ++ tailWord_1082647).sum := by decide
  have hdescent : baseEnd_1082647 < baseStart_1082647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082650 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1082650 : Nat := 118140960795 + 1082650 * 2 ^ 59
def prefixEnd_1082650 : Nat := 4983230072969 + 3 ^ 40 * 1082650 * 2
def baseEnd_1082650 : Nat := 247075480262353049153773

theorem tailTrace_1082650 : CollatzResearch.WordTrace tailWord_1082650 prefixEnd_1082650 247075480262353049153773 := by
  unfold tailWord_1082650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9871872381937856686079351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26324993018500951162878269 9871872381937856686079351)
  ·
    refine ⟨14807808572906785029119027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9871872381937856686079351 14807808572906785029119027)
    ·
      refine ⟨22211712859360177543678541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14807808572906785029119027 22211712859360177543678541)
      ·
        refine ⟨8329392322260066578879453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22211712859360177543678541 8329392322260066578879453)
        ·
          refine ⟨3123522120847524967079795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8329392322260066578879453 3123522120847524967079795)
          ·
            refine ⟨4685283181271287450619693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123522120847524967079795 4685283181271287450619693)
            ·
              refine ⟨1756981192976732793982385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4685283181271287450619693 1756981192976732793982385)
              ·
                refine ⟨1317735894732549595486789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1756981192976732793982385 1317735894732549595486789)
                ·
                  refine ⟨247075480262353049153773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317735894732549595486789 247075480262353049153773)
                  ·
                    rfl

theorem cell21_1082650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1082650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082650 prefixEnd_1082650 := by exact prefixLift 1082650
  have htrace : WordTrace (prefixWord ++ tailWord_1082650) baseStart_1082650 baseEnd_1082650 := by
    simpa [prefixWord, tailWord_1082650, baseEnd_1082650] using wordTrace_append hprefix tailTrace_1082650
  have hstable : (prefixWord ++ tailWord_1082650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082650).length < 2 ^ (prefixWord ++ tailWord_1082650).sum := by decide
  have hdescent : baseEnd_1082650 < baseStart_1082650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082709 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 6]
def baseStart_1082709 : Nat := 118140960795 + 1082709 * 2 ^ 59
def prefixEnd_1082709 : Nat := 4983230072969 + 3 ^ 40 * 1082709 * 2
def baseEnd_1082709 : Nat := 247088944866182057670319

theorem tailTrace_1082709 : CollatzResearch.WordTrace tailWord_1082709 prefixEnd_1082709 247088944866182057670319 := by
  unfold tailWord_1082709
  simp only [CollatzResearch.WordTrace]
  refine ⟨39489641434537679820715181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26326427623025119880476787 39489641434537679820715181)
  ·
    refine ⟨14808615537951629932768193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39489641434537679820715181 14808615537951629932768193)
    ·
      refine ⟨11106461653463722449576145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14808615537951629932768193 11106461653463722449576145)
      ·
        refine ⟨8329846240097791837182109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11106461653463722449576145 8329846240097791837182109)
        ·
          refine ⟨3123692340036671938943291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8329846240097791837182109 3123692340036671938943291)
          ·
            refine ⟨4685538510055007908414937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123692340036671938943291 4685538510055007908414937)
            ·
              refine ⟨3514153882541255931311203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4685538510055007908414937 3514153882541255931311203)
              ·
                refine ⟨5271230823811883896966805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514153882541255931311203 5271230823811883896966805)
                ·
                  refine ⟨247088944866182057670319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5271230823811883896966805 247088944866182057670319)
                  ·
                    rfl

theorem cell21_1082709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_1082709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082709 prefixEnd_1082709 := by exact prefixLift 1082709
  have htrace : WordTrace (prefixWord ++ tailWord_1082709) baseStart_1082709 baseEnd_1082709 := by
    simpa [prefixWord, tailWord_1082709, baseEnd_1082709] using wordTrace_append hprefix tailTrace_1082709
  have hstable : (prefixWord ++ tailWord_1082709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082709).length < 2 ^ (prefixWord ++ tailWord_1082709).sum := by decide
  have hdescent : baseEnd_1082709 < baseStart_1082709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082712 : List Nat := [2, 1, 2, 2, 1, 1, 7, 2, 3]
def baseStart_1082712 : Nat := 118140960795 + 1082712 * 2 ^ 59
def prefixEnd_1082712 : Nat := 4983230072969 + 3 ^ 40 * 1082712 * 2
def baseEnd_1082712 : Nat := 247089629507054719120313

theorem tailTrace_1082712 : CollatzResearch.WordTrace tailWord_1082712 prefixEnd_1082712 247089629507054719120313 := by
  unfold tailWord_1082712
  simp only [CollatzResearch.WordTrace]
  refine ⟨19744875426763405666537195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26326500569017874222049593 19744875426763405666537195)
  ·
    refine ⟨29617313140145108499805793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19744875426763405666537195 29617313140145108499805793)
    ·
      refine ⟨22212984855108831374854345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29617313140145108499805793 22212984855108831374854345)
      ·
        refine ⟨16659738641331623531140759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22212984855108831374854345 16659738641331623531140759)
        ·
          refine ⟨24989607961997435296711139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16659738641331623531140759 24989607961997435296711139)
          ·
            refine ⟨37484411942996152945066709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24989607961997435296711139 37484411942996152945066709)
            ·
              refine ⟨878540904913972334650001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37484411942996152945066709 878540904913972334650001)
              ·
                refine ⟨658905678685479250987501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878540904913972334650001 658905678685479250987501)
                ·
                  refine ⟨247089629507054719120313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658905678685479250987501 247089629507054719120313)
                  ·
                    rfl

theorem cell21_1082712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_1082712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082712 prefixEnd_1082712 := by exact prefixLift 1082712
  have htrace : WordTrace (prefixWord ++ tailWord_1082712) baseStart_1082712 baseEnd_1082712 := by
    simpa [prefixWord, tailWord_1082712, baseEnd_1082712] using wordTrace_append hprefix tailTrace_1082712
  have hstable : (prefixWord ++ tailWord_1082712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082712).length < 2 ^ (prefixWord ++ tailWord_1082712).sum := by decide
  have hdescent : baseEnd_1082712 < baseStart_1082712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082723 : List Nat := [1, 1, 1, 5, 2, 2, 1, 8]
def baseStart_1082723 : Nat := 118140960795 + 1082723 * 2 ^ 59
def prefixEnd_1082723 : Nat := 4983230072969 + 3 ^ 40 * 1082723 * 2
def baseEnd_1082723 : Nat := 82364046618973714812319

theorem tailTrace_1082723 : CollatzResearch.WordTrace tailWord_1082723 prefixEnd_1082723 82364046618973714812319 := by
  unfold tailWord_1082723
  simp only [CollatzResearch.WordTrace]
  refine ⟨39490152056486960211724823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26326768037657973474483215 39490152056486960211724823)
  ·
    refine ⟨59235228084730440317587235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39490152056486960211724823 59235228084730440317587235)
    ·
      refine ⟨88852842127095660476380853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59235228084730440317587235 88852842127095660476380853)
      ·
        refine ⟨8329953949415218169660705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88852842127095660476380853 8329953949415218169660705)
        ·
          refine ⟨6247465462061413627245529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8329953949415218169660705 6247465462061413627245529)
          ·
            refine ⟨4685599096546060220434147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6247465462061413627245529 4685599096546060220434147)
            ·
              refine ⟨7028398644819090330651221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4685599096546060220434147 7028398644819090330651221)
              ·
                refine ⟨82364046618973714812319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7028398644819090330651221 82364046618973714812319)
                ·
                  rfl

theorem cell21_1082723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_1082723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082723 prefixEnd_1082723 := by exact prefixLift 1082723
  have htrace : WordTrace (prefixWord ++ tailWord_1082723) baseStart_1082723 baseEnd_1082723 := by
    simpa [prefixWord, tailWord_1082723, baseEnd_1082723] using wordTrace_append hprefix tailTrace_1082723
  have hstable : (prefixWord ++ tailWord_1082723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082723).length < 2 ^ (prefixWord ++ tailWord_1082723).sum := by decide
  have hdescent : baseEnd_1082723 < baseStart_1082723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082830 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1082830 : Nat := 118140960795 + 1082830 * 2 ^ 59
def prefixEnd_1082830 : Nat := 4983230072969 + 3 ^ 40 * 1082830 * 2
def baseEnd_1082830 : Nat := 247116558714712736153405

theorem tailTrace_1082830 : CollatzResearch.WordTrace tailWord_1082830 prefixEnd_1082830 247116558714712736153405 := by
  unfold tailWord_1082830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936756833387414685733743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26329369778066211657246629 4936756833387414685733743)
  ·
    refine ⟨7405135250081122028600615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4936756833387414685733743 7405135250081122028600615)
    ·
      refine ⟨11107702875121683042900923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7405135250081122028600615 11107702875121683042900923)
      ·
        refine ⟨16661554312682524564351385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11107702875121683042900923 16661554312682524564351385)
        ·
          refine ⟨12496165734511893423263539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16661554312682524564351385 12496165734511893423263539)
          ·
            refine ⟨18744248601767840134895309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12496165734511893423263539 18744248601767840134895309)
            ·
              refine ⟨7029093225662940050585741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18744248601767840134895309 7029093225662940050585741)
              ·
                refine ⟨2635909959623602518969653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7029093225662940050585741 2635909959623602518969653)
                ·
                  refine ⟨247116558714712736153405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2635909959623602518969653 247116558714712736153405)
                  ·
                    rfl

theorem cell21_1082830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1082830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082830 prefixEnd_1082830 := by exact prefixLift 1082830
  have htrace : WordTrace (prefixWord ++ tailWord_1082830) baseStart_1082830 baseEnd_1082830 := by
    simpa [prefixWord, tailWord_1082830, baseEnd_1082830] using wordTrace_append hprefix tailTrace_1082830
  have hstable : (prefixWord ++ tailWord_1082830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082830).length < 2 ^ (prefixWord ++ tailWord_1082830).sum := by decide
  have hdescent : baseEnd_1082830 < baseStart_1082830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082864 : List Nat := [2, 1, 1, 1, 3, 6, 1, 3, 3]
def baseStart_1082864 : Nat := 118140960795 + 1082864 * 2 ^ 59
def prefixEnd_1082864 : Nat := 4983230072969 + 3 ^ 40 * 1082864 * 2
def baseEnd_1082864 : Nat := 247124317977936232586669

theorem tailTrace_1082864 : CollatzResearch.WordTrace tailWord_1082864 prefixEnd_1082864 247124317977936232586669 := by
  unfold tailWord_1082864
  simp only [CollatzResearch.WordTrace]
  refine ⟨19747647374488070646303823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26330196499317427528405097 19747647374488070646303823)
  ·
    refine ⟨29621471061732105969455735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19747647374488070646303823 29621471061732105969455735)
    ·
      refine ⟨44432206592598158954183603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29621471061732105969455735 44432206592598158954183603)
      ·
        refine ⟨66648309888897238431275405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44432206592598158954183603 66648309888897238431275405)
        ·
          refine ⟨24993116208336464411728277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66648309888897238431275405 24993116208336464411728277)
          ·
            refine ⟨1171552322265771769299763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24993116208336464411728277 1171552322265771769299763)
            ·
              refine ⟨1757328483398657653949645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171552322265771769299763 1757328483398657653949645)
              ·
                refine ⟨658998181274496620231117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1757328483398657653949645 658998181274496620231117)
                ·
                  refine ⟨247124317977936232586669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658998181274496620231117 247124317977936232586669)
                  ·
                    rfl

theorem cell21_1082864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_1082864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082864 prefixEnd_1082864 := by exact prefixLift 1082864
  have htrace : WordTrace (prefixWord ++ tailWord_1082864) baseStart_1082864 baseEnd_1082864 := by
    simpa [prefixWord, tailWord_1082864, baseEnd_1082864] using wordTrace_append hprefix tailTrace_1082864
  have hstable : (prefixWord ++ tailWord_1082864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082864).length < 2 ^ (prefixWord ++ tailWord_1082864).sum := by decide
  have hdescent : baseEnd_1082864 < baseStart_1082864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082881 : List Nat := [1, 2, 4, 1, 4, 1, 3, 2, 3]
def baseStart_1082881 : Nat := 118140960795 + 1082881 * 2 ^ 59
def prefixEnd_1082881 : Nat := 4983230072969 + 3 ^ 40 * 1082881 * 2
def baseEnd_1082881 : Nat := 247128197609547980803301

theorem tailTrace_1082881 : CollatzResearch.WordTrace tailWord_1082881 prefixEnd_1082881 247128197609547980803301 := by
  unfold tailWord_1082881
  simp only [CollatzResearch.WordTrace]
  refine ⟨39495914789914553195976497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26330609859943035463984331 39495914789914553195976497)
  ·
    refine ⟨29621936092435914896982373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39495914789914553195976497 29621936092435914896982373)
    ·
      refine ⟨5554113017331734043184195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29621936092435914896982373 5554113017331734043184195)
      ·
        refine ⟨8331169525997601064776293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554113017331734043184195 8331169525997601064776293)
        ·
          refine ⟨1562094286124550199645555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8331169525997601064776293 1562094286124550199645555)
          ·
            refine ⟨2343141429186825299468333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562094286124550199645555 2343141429186825299468333)
            ·
              refine ⟨878678035945059487300625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2343141429186825299468333 878678035945059487300625)
              ·
                refine ⟨659008526958794615475469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878678035945059487300625 659008526958794615475469)
                ·
                  refine ⟨247128197609547980803301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659008526958794615475469 247128197609547980803301)
                  ·
                    rfl

theorem cell21_1082881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_1082881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082881 prefixEnd_1082881 := by exact prefixLift 1082881
  have htrace : WordTrace (prefixWord ++ tailWord_1082881) baseStart_1082881 baseEnd_1082881 := by
    simpa [prefixWord, tailWord_1082881, baseEnd_1082881] using wordTrace_append hprefix tailTrace_1082881
  have hstable : (prefixWord ++ tailWord_1082881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082881).length < 2 ^ (prefixWord ++ tailWord_1082881).sum := by decide
  have hdescent : baseEnd_1082881 < baseStart_1082881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082892 : List Nat := [2, 2, 1, 2, 5, 1, 2, 6]
def baseStart_1082892 : Nat := 118140960795 + 1082892 * 2 ^ 59
def prefixEnd_1082892 : Nat := 4983230072969 + 3 ^ 40 * 1082892 * 2
def baseEnd_1082892 : Nat := 82376902653138135373315

theorem tailTrace_1082892 : CollatzResearch.WordTrace tailWord_1082892 prefixEnd_1082892 82376902653138135373315 := by
  unfold tailWord_1082892
  simp only [CollatzResearch.WordTrace]
  refine ⟨19748157996437351037313465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26330877328583134716417953 19748157996437351037313465)
  ·
    refine ⟨14811118497328013277985099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19748157996437351037313465 14811118497328013277985099)
    ·
      refine ⟨22216677745992019916977649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14811118497328013277985099 22216677745992019916977649)
      ·
        refine ⟨16662508309494014937733237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22216677745992019916977649 16662508309494014937733237)
        ·
          refine ⟨1562110154015063900412491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16662508309494014937733237 1562110154015063900412491)
          ·
            refine ⟨2343165231022595850618737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562110154015063900412491 2343165231022595850618737)
            ·
              refine ⟨1757373923266946887964053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2343165231022595850618737 1757373923266946887964053)
              ·
                refine ⟨82376902653138135373315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1757373923266946887964053 82376902653138135373315)
                ·
                  rfl

theorem cell21_1082892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_1082892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082892 prefixEnd_1082892 := by exact prefixLift 1082892
  have htrace : WordTrace (prefixWord ++ tailWord_1082892) baseStart_1082892 baseEnd_1082892 := by
    simpa [prefixWord, tailWord_1082892, baseEnd_1082892] using wordTrace_append hprefix tailTrace_1082892
  have hstable : (prefixWord ++ tailWord_1082892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082892).length < 2 ^ (prefixWord ++ tailWord_1082892).sum := by decide
  have hdescent : baseEnd_1082892 < baseStart_1082892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082937 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 4]
def baseStart_1082937 : Nat := 118140960795 + 1082937 * 2 ^ 59
def prefixEnd_1082937 : Nat := 4983230072969 + 3 ^ 40 * 1082937 * 2
def baseEnd_1082937 : Nat := 247140977572504327869853

theorem tailTrace_1082937 : CollatzResearch.WordTrace tailWord_1082937 prefixEnd_1082937 247140977572504327869853 := by
  unfold tailWord_1082937
  simp only [CollatzResearch.WordTrace]
  refine ⟨39497957277711674760015065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26331971518474449840010043 39497957277711674760015065)
  ·
    refine ⟨29623467958283756070011299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39497957277711674760015065 29623467958283756070011299)
    ·
      refine ⟨44435201937425634105016949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29623467958283756070011299 44435201937425634105016949)
      ·
        refine ⟨4165800181633653197345339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44435201937425634105016949 4165800181633653197345339)
        ·
          refine ⟨6248700272450479796018009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165800181633653197345339 6248700272450479796018009)
          ·
            refine ⟨4686525204337859847013507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6248700272450479796018009 4686525204337859847013507)
            ·
              refine ⟨7029787806506789770520261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686525204337859847013507 7029787806506789770520261)
              ·
                refine ⟨1318085213720023081972549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7029787806506789770520261 1318085213720023081972549)
                ·
                  refine ⟨247140977572504327869853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318085213720023081972549 247140977572504327869853)
                  ·
                    rfl

theorem cell21_1082937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_1082937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082937 prefixEnd_1082937 := by exact prefixLift 1082937
  have htrace : WordTrace (prefixWord ++ tailWord_1082937) baseStart_1082937 baseEnd_1082937 := by
    simpa [prefixWord, tailWord_1082937, baseEnd_1082937] using wordTrace_append hprefix tailTrace_1082937
  have hstable : (prefixWord ++ tailWord_1082937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082937).length < 2 ^ (prefixWord ++ tailWord_1082937).sum := by decide
  have hdescent : baseEnd_1082937 < baseStart_1082937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1082940 : List Nat := [2, 2, 2, 2, 4, 1, 1, 4, 3]
def baseStart_1082940 : Nat := 118140960795 + 1082940 * 2 ^ 59
def prefixEnd_1082940 : Nat := 4983230072969 + 3 ^ 40 * 1082940 * 2
def baseEnd_1082940 : Nat := 247141662213376989319847

theorem tailTrace_1082940 : CollatzResearch.WordTrace tailWord_1082940 prefixEnd_1082940 247141662213376989319847 := by
  unfold tailWord_1082940
  simp only [CollatzResearch.WordTrace]
  refine ⟨19749033348350403136187137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26332044464467204181582849 19749033348350403136187137)
  ·
    refine ⟨14811775011262802352140353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19749033348350403136187137 14811775011262802352140353)
    ·
      refine ⟨11108831258447101764105265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14811775011262802352140353 11108831258447101764105265)
      ·
        refine ⟨8331623443835326323078949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11108831258447101764105265 8331623443835326323078949)
        ·
          refine ⟨1562179395719123685577303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8331623443835326323078949 1562179395719123685577303)
          ·
            refine ⟨2343269093578685528365955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562179395719123685577303 2343269093578685528365955)
            ·
              refine ⟨3514903640368028292548933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343269093578685528365955 3514903640368028292548933)
              ·
                refine ⟨659044432569005304852925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3514903640368028292548933 659044432569005304852925)
                ·
                  refine ⟨247141662213376989319847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659044432569005304852925 247141662213376989319847)
                  ·
                    rfl

theorem cell21_1082940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_1082940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1082940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1082940 prefixEnd_1082940 := by exact prefixLift 1082940
  have htrace : WordTrace (prefixWord ++ tailWord_1082940) baseStart_1082940 baseEnd_1082940 := by
    simpa [prefixWord, tailWord_1082940, baseEnd_1082940] using wordTrace_append hprefix tailTrace_1082940
  have hstable : (prefixWord ++ tailWord_1082940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1082940).length < 2 ^ (prefixWord ++ tailWord_1082940).sum := by decide
  have hdescent : baseEnd_1082940 < baseStart_1082940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1082940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083058 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1083058 : Nat := 118140960795 + 1083058 * 2 ^ 59
def prefixEnd_1083058 : Nat := 4983230072969 + 3 ^ 40 * 1083058 * 2
def baseEnd_1083058 : Nat := 247168591421035006352939

theorem tailTrace_1083058 : CollatzResearch.WordTrace tailWord_1083058 prefixEnd_1083058 247168591421035006352939 := by
  unfold tailWord_1083058
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875592627568328106292457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26334913673515541616779885 9875592627568328106292457)
  ·
    refine ⟨7406694470676246079719343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9875592627568328106292457 7406694470676246079719343)
    ·
      refine ⟨11110041706014369119579015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406694470676246079719343 11110041706014369119579015)
      ·
        refine ⟨16665062559021553679368523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11110041706014369119579015 16665062559021553679368523)
        ·
          refine ⟨24997593838532330519052785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16665062559021553679368523 24997593838532330519052785)
          ·
            refine ⟨18748195378899247889289589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24997593838532330519052785 18748195378899247889289589)
            ·
              refine ⟨1757643316771804489620899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18748195378899247889289589 1757643316771804489620899)
              ·
                refine ⟨2636464975157706734431349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757643316771804489620899 2636464975157706734431349)
                ·
                  refine ⟨247168591421035006352939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2636464975157706734431349 247168591421035006352939)
                  ·
                    rfl

theorem cell21_1083058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1083058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083058 prefixEnd_1083058 := by exact prefixLift 1083058
  have htrace : WordTrace (prefixWord ++ tailWord_1083058) baseStart_1083058 baseEnd_1083058 := by
    simpa [prefixWord, tailWord_1083058, baseEnd_1083058] using wordTrace_append hprefix tailTrace_1083058
  have hstable : (prefixWord ++ tailWord_1083058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083058).length < 2 ^ (prefixWord ++ tailWord_1083058).sum := by decide
  have hdescent : baseEnd_1083058 < baseStart_1083058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083278 : List Nat := [4, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_1083278 : Nat := 118140960795 + 1083278 * 2 ^ 59
def prefixEnd_1083278 : Nat := 4983230072969 + 3 ^ 40 * 1083278 * 2
def baseEnd_1083278 : Nat := 247218798418363512685823

theorem tailTrace_1083278 : CollatzResearch.WordTrace tailWord_1083278 prefixEnd_1083278 247218798418363512685823 := by
  unfold tailWord_1083278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938799321184536249772311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26340263046317526665452325 4938799321184536249772311)
  ·
    refine ⟨7408198981776804374658467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938799321184536249772311 7408198981776804374658467)
    ·
      refine ⟨11112298472665206561987701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408198981776804374658467 11112298472665206561987701)
      ·
        refine ⟨1041777981812363115186347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11112298472665206561987701 1041777981812363115186347)
        ·
          refine ⟨1562666972718544672779521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041777981812363115186347 1562666972718544672779521)
          ·
            refine ⟨1172000229538908504584641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562666972718544672779521 1172000229538908504584641)
            ·
              refine ⟨879000172154181378438481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172000229538908504584641 879000172154181378438481)
              ·
                refine ⟨659250129115636033828861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879000172154181378438481 659250129115636033828861)
                ·
                  refine ⟨247218798418363512685823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659250129115636033828861 247218798418363512685823)
                  ·
                    rfl

theorem cell21_1083278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_1083278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083278 prefixEnd_1083278 := by exact prefixLift 1083278
  have htrace : WordTrace (prefixWord ++ tailWord_1083278) baseStart_1083278 baseEnd_1083278 := by
    simpa [prefixWord, tailWord_1083278, baseEnd_1083278] using wordTrace_append hprefix tailTrace_1083278
  have hstable : (prefixWord ++ tailWord_1083278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083278).length < 2 ^ (prefixWord ++ tailWord_1083278).sum := by decide
  have hdescent : baseEnd_1083278 < baseStart_1083278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083283 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 10]
def baseStart_1083283 : Nat := 118140960795 + 1083283 * 2 ^ 59
def prefixEnd_1083283 : Nat := 4983230072969 + 3 ^ 40 * 1083283 * 2
def baseEnd_1083283 : Nat := 247219939486484615102479

theorem tailTrace_1083283 : CollatzResearch.WordTrace tailWord_1083283 prefixEnd_1083283 247219939486484615102479 := by
  unfold tailWord_1083283
  simp only [CollatzResearch.WordTrace]
  refine ⟨39510576934458175852110503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26340384622972117234740335 39510576934458175852110503)
  ·
    refine ⟨59265865401687263778165755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39510576934458175852110503 59265865401687263778165755)
    ·
      refine ⟨88898798102530895667248633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59265865401687263778165755 88898798102530895667248633)
      ·
        refine ⟨66674098576898171750436475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88898798102530895667248633 66674098576898171750436475)
        ·
          refine ⟨100011147865347257625654713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66674098576898171750436475 100011147865347257625654713)
          ·
            refine ⟨75008360899010443219241035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100011147865347257625654713 75008360899010443219241035)
            ·
              refine ⟨112512541348515664828861553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75008360899010443219241035 112512541348515664828861553)
              ·
                refine ⟨84384406011386748621646165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112512541348515664828861553 84384406011386748621646165)
                ·
                  refine ⟨247219939486484615102479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84384406011386748621646165 247219939486484615102479)
                  ·
                    rfl

theorem cell21_1083283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_1083283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083283 prefixEnd_1083283 := by exact prefixLift 1083283
  have htrace : WordTrace (prefixWord ++ tailWord_1083283) baseStart_1083283 baseEnd_1083283 := by
    simpa [prefixWord, tailWord_1083283, baseEnd_1083283] using wordTrace_append hprefix tailTrace_1083283
  have hstable : (prefixWord ++ tailWord_1083283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083283).length < 2 ^ (prefixWord ++ tailWord_1083283).sum := by decide
  have hdescent : baseEnd_1083283 < baseStart_1083283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083314 : List Nat := [3, 2, 1, 1, 1, 1, 1, 11]
def baseStart_1083314 : Nat := 118140960795 + 1083314 * 2 ^ 59
def prefixEnd_1083314 : Nat := 4983230072969 + 3 ^ 40 * 1083314 * 2
def baseEnd_1083314 : Nat := 82409004702945150028583

theorem tailTrace_1083314 : CollatzResearch.WordTrace tailWord_1083314 prefixEnd_1083314 82409004702945150028583 := by
  unfold tailWord_1083314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9877926899336467036622249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26341138398230578764325997 9877926899336467036622249)
  ·
    refine ⟨7408445174502350277466687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9877926899336467036622249 7408445174502350277466687)
    ·
      refine ⟨11112667761753525416200031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7408445174502350277466687 11112667761753525416200031)
      ·
        refine ⟨16669001642630288124300047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11112667761753525416200031 16669001642630288124300047)
        ·
          refine ⟨25003502463945432186450071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16669001642630288124300047 25003502463945432186450071)
          ·
            refine ⟨37505253695918148279675107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25003502463945432186450071 37505253695918148279675107)
            ·
              refine ⟨56257880543877222419512661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37505253695918148279675107 56257880543877222419512661)
              ·
                refine ⟨82409004702945150028583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56257880543877222419512661 82409004702945150028583)
                ·
                  rfl

theorem cell21_1083314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_1083314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083314 prefixEnd_1083314 := by exact prefixLift 1083314
  have htrace : WordTrace (prefixWord ++ tailWord_1083314) baseStart_1083314 baseEnd_1083314 := by
    simpa [prefixWord, tailWord_1083314, baseEnd_1083314] using wordTrace_append hprefix tailTrace_1083314
  have hstable : (prefixWord ++ tailWord_1083314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083314).length < 2 ^ (prefixWord ++ tailWord_1083314).sum := by decide
  have hdescent : baseEnd_1083314 < baseStart_1083314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083396 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1083396 : Nat := 118140960795 + 1083396 * 2 ^ 59
def prefixEnd_1083396 : Nat := 4983230072969 + 3 ^ 40 * 1083396 * 2
def baseEnd_1083396 : Nat := 247245727626021529718915

theorem tailTrace_1083396 : CollatzResearch.WordTrace tailWord_1083396 prefixEnd_1083396 247245727626021529718915 := by
  unfold tailWord_1083396
  simp only [CollatzResearch.WordTrace]
  refine ⟨19757349191524398075487021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26343132255365864100649361 19757349191524398075487021)
  ·
    refine ⟨7409005946821649278307633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19757349191524398075487021 7409005946821649278307633)
    ·
      refine ⟨5556754460116236958730725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7409005946821649278307633 5556754460116236958730725)
      ·
        refine ⟨1041891461271794429762011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5556754460116236958730725 1041891461271794429762011)
        ·
          refine ⟨1562837191907691644643017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041891461271794429762011 1562837191907691644643017)
          ·
            refine ⟨1172127893930768733482263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562837191907691644643017 1172127893930768733482263)
            ·
              refine ⟨1758191840896153100223395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172127893930768733482263 1758191840896153100223395)
              ·
                refine ⟨2637287761344229650335093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758191840896153100223395 2637287761344229650335093)
                ·
                  refine ⟨247245727626021529718915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2637287761344229650335093 247245727626021529718915)
                  ·
                    rfl

theorem cell21_1083396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1083396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083396 prefixEnd_1083396 := by exact prefixLift 1083396
  have htrace : WordTrace (prefixWord ++ tailWord_1083396) baseStart_1083396 baseEnd_1083396 := by
    simpa [prefixWord, tailWord_1083396, baseEnd_1083396] using wordTrace_append hprefix tailTrace_1083396
  have hstable : (prefixWord ++ tailWord_1083396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083396).length < 2 ^ (prefixWord ++ tailWord_1083396).sum := by decide
  have hdescent : baseEnd_1083396 < baseStart_1083396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083435 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 6]
def baseStart_1083435 : Nat := 118140960795 + 1083435 * 2 ^ 59
def prefixEnd_1083435 : Nat := 4983230072969 + 3 ^ 40 * 1083435 * 2
def baseEnd_1083435 : Nat := 247254627957366128568835

theorem tailTrace_1083435 : CollatzResearch.WordTrace tailWord_1083435 prefixEnd_1083435 247254627957366128568835 := by
  unfold tailWord_1083435
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516120829907505811643759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26344080553271670541095839 39516120829907505811643759)
  ·
    refine ⟨59274181244861258717465639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39516120829907505811643759 59274181244861258717465639)
    ·
      refine ⟨88911271867291888076198459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59274181244861258717465639 88911271867291888076198459)
      ·
        refine ⟨133366907800937832114297689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88911271867291888076198459 133366907800937832114297689)
        ·
          refine ⟨100025180850703374085723267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133366907800937832114297689 100025180850703374085723267)
          ·
            refine ⟨150037771276055061128584901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100025180850703374085723267 150037771276055061128584901)
            ·
              refine ⟨28132082114260323961609669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150037771276055061128584901 28132082114260323961609669)
              ·
                refine ⟨5274765396423810742801813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28132082114260323961609669 5274765396423810742801813)
                ·
                  refine ⟨247254627957366128568835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5274765396423810742801813 247254627957366128568835)
                  ·
                    rfl

theorem cell21_1083435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_1083435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083435 prefixEnd_1083435 := by exact prefixLift 1083435
  have htrace : WordTrace (prefixWord ++ tailWord_1083435) baseStart_1083435 baseEnd_1083435 := by
    simpa [prefixWord, tailWord_1083435, baseEnd_1083435] using wordTrace_append hprefix tailTrace_1083435
  have hstable : (prefixWord ++ tailWord_1083435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083435).length < 2 ^ (prefixWord ++ tailWord_1083435).sum := by decide
  have hdescent : baseEnd_1083435 < baseStart_1083435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083455 : List Nat := [1, 1, 2, 2, 3, 1, 6, 2, 3]
def baseStart_1083455 : Nat := 118140960795 + 1083455 * 2 ^ 59
def prefixEnd_1083455 : Nat := 4983230072969 + 3 ^ 40 * 1083455 * 2
def baseEnd_1083455 : Nat := 247259192229850538235461

theorem tailTrace_1083455 : CollatzResearch.WordTrace tailWord_1083455 prefixEnd_1083455 247259192229850538235461 := by
  unfold tailWord_1083455
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516850289835049227371819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26344566859890032818247879 39516850289835049227371819)
  ·
    refine ⟨59275275434752573841057729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39516850289835049227371819 59275275434752573841057729)
    ·
      refine ⟨44456456576064430380793297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59275275434752573841057729 44456456576064430380793297)
      ·
        refine ⟨33342342432048322785594973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44456456576064430380793297 33342342432048322785594973)
        ·
          refine ⟨12503378412018121044598115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33342342432048322785594973 12503378412018121044598115)
          ·
            refine ⟨18755067618027181566897173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12503378412018121044598115 18755067618027181566897173)
            ·
              refine ⟨879143794595024135948305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18755067618027181566897173 879143794595024135948305)
              ·
                refine ⟨659357845946268101961229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879143794595024135948305 659357845946268101961229)
                ·
                  refine ⟨247259192229850538235461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659357845946268101961229 247259192229850538235461)
                  ·
                    rfl

theorem cell21_1083455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 3].length) (baseStart_1083455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083455 prefixEnd_1083455 := by exact prefixLift 1083455
  have htrace : WordTrace (prefixWord ++ tailWord_1083455) baseStart_1083455 baseEnd_1083455 := by
    simpa [prefixWord, tailWord_1083455, baseEnd_1083455] using wordTrace_append hprefix tailTrace_1083455
  have hstable : (prefixWord ++ tailWord_1083455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083455).length < 2 ^ (prefixWord ++ tailWord_1083455).sum := by decide
  have hdescent : baseEnd_1083455 < baseStart_1083455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083469 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1083469 : Nat := 118140960795 + 1083469 * 2 ^ 59
def prefixEnd_1083469 : Nat := 4983230072969 + 3 ^ 40 * 1083469 * 2
def baseEnd_1083469 : Nat := 247262387220589625002099

theorem tailTrace_1083469 : CollatzResearch.WordTrace tailWord_1083469 prefixEnd_1083469 247262387220589625002099 := by
  unfold tailWord_1083469
  simp only [CollatzResearch.WordTrace]
  refine ⟨39517360911784329618381461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26344907274522886412254307 39517360911784329618381461)
  ·
    refine ⟨1852376292739890450861631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39517360911784329618381461 1852376292739890450861631)
    ·
      refine ⟨2778564439109835676292447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852376292739890450861631 2778564439109835676292447)
      ·
        refine ⟨4167846658664753514438671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778564439109835676292447 4167846658664753514438671)
        ·
          refine ⟨6251769987997130271658007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4167846658664753514438671 6251769987997130271658007)
          ·
            refine ⟨9377654981995695407487011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251769987997130271658007 9377654981995695407487011)
            ·
              refine ⟨14066482472993543111230517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9377654981995695407487011 14066482472993543111230517)
              ·
                refine ⟨1318732731843144666677861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14066482472993543111230517 1318732731843144666677861)
                ·
                  refine ⟨247262387220589625002099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318732731843144666677861 247262387220589625002099)
                  ·
                    rfl

theorem cell21_1083469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1083469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083469 prefixEnd_1083469 := by exact prefixLift 1083469
  have htrace : WordTrace (prefixWord ++ tailWord_1083469) baseStart_1083469 baseEnd_1083469 := by
    simpa [prefixWord, tailWord_1083469, baseEnd_1083469] using wordTrace_append hprefix tailTrace_1083469
  have hstable : (prefixWord ++ tailWord_1083469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083469).length < 2 ^ (prefixWord ++ tailWord_1083469).sum := by decide
  have hdescent : baseEnd_1083469 < baseStart_1083469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083621 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1083621 : Nat := 118140960795 + 1083621 * 2 ^ 59
def prefixEnd_1083621 : Nat := 4983230072969 + 3 ^ 40 * 1083621 * 2
def baseEnd_1083621 : Nat := 247297075691471138468455

theorem tailTrace_1083621 : CollatzResearch.WordTrace tailWord_1083621 prefixEnd_1083621 247297075691471138468455 := by
  unfold tailWord_1083621
  simp only [CollatzResearch.WordTrace]
  refine ⟨39522904807233659577914717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26348603204822439718609811 39522904807233659577914717)
  ·
    refine ⟨14821089302712622341718019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39522904807233659577914717 14821089302712622341718019)
    ·
      refine ⟨22231633954068933512577029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14821089302712622341718019 22231633954068933512577029)
      ·
        refine ⟨4168431366387925033608193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22231633954068933512577029 4168431366387925033608193)
        ·
          refine ⟨3126323524790943775206145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168431366387925033608193 3126323524790943775206145)
          ·
            refine ⟨2344742643593207831404609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126323524790943775206145 2344742643593207831404609)
            ·
              refine ⟨1758556982694905873553457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344742643593207831404609 1758556982694905873553457)
              ·
                refine ⟨1318917737021179405165093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758556982694905873553457 1318917737021179405165093)
                ·
                  refine ⟨247297075691471138468455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318917737021179405165093 247297075691471138468455)
                  ·
                    rfl

theorem cell21_1083621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1083621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083621 prefixEnd_1083621 := by exact prefixLift 1083621
  have htrace : WordTrace (prefixWord ++ tailWord_1083621) baseStart_1083621 baseEnd_1083621 := by
    simpa [prefixWord, tailWord_1083621, baseEnd_1083621] using wordTrace_append hprefix tailTrace_1083621
  have hstable : (prefixWord ++ tailWord_1083621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083621).length < 2 ^ (prefixWord ++ tailWord_1083621).sum := by decide
  have hdescent : baseEnd_1083621 < baseStart_1083621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083624 : List Nat := [2, 1, 4, 1, 2, 4, 2, 2, 3]
def baseStart_1083624 : Nat := 118140960795 + 1083624 * 2 ^ 59
def prefixEnd_1083624 : Nat := 4983230072969 + 3 ^ 40 * 1083624 * 2
def baseEnd_1083624 : Nat := 247297760332343799918449

theorem tailTrace_1083624 : CollatzResearch.WordTrace tailWord_1083624 prefixEnd_1083624 247297760332343799918449 := by
  unfold tailWord_1083624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19761507113111395545136963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26348676150815194060182617 19761507113111395545136963)
  ·
    refine ⟨29642260669667093317705445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19761507113111395545136963 29642260669667093317705445)
    ·
      refine ⟨5557923875562579997069771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29642260669667093317705445 5557923875562579997069771)
      ·
        refine ⟨8336885813343869995604657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5557923875562579997069771 8336885813343869995604657)
        ·
          refine ⟨6252664360007902496703493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8336885813343869995604657 6252664360007902496703493)
          ·
            refine ⟨1172374567501481718131905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6252664360007902496703493 1172374567501481718131905)
            ·
              refine ⟨879280925626111288598929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172374567501481718131905 879280925626111288598929)
              ·
                refine ⟨659460694219583466449197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879280925626111288598929 659460694219583466449197)
                ·
                  refine ⟨247297760332343799918449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659460694219583466449197 247297760332343799918449)
                  ·
                    rfl

theorem cell21_1083624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_1083624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083624 prefixEnd_1083624 := by exact prefixLift 1083624
  have htrace : WordTrace (prefixWord ++ tailWord_1083624) baseStart_1083624 baseEnd_1083624 := by
    simpa [prefixWord, tailWord_1083624, baseEnd_1083624] using wordTrace_append hprefix tailTrace_1083624
  have hstable : (prefixWord ++ tailWord_1083624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083624).length < 2 ^ (prefixWord ++ tailWord_1083624).sum := by decide
  have hdescent : baseEnd_1083624 < baseStart_1083624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083632 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_1083632 : Nat := 118140960795 + 1083632 * 2 ^ 59
def prefixEnd_1083632 : Nat := 4983230072969 + 3 ^ 40 * 1083632 * 2
def baseEnd_1083632 : Nat := 247299586041337563785099

theorem tailTrace_1083632 : CollatzResearch.WordTrace tailWord_1083632 prefixEnd_1083632 247299586041337563785099 := by
  unfold tailWord_1083632
  simp only [CollatzResearch.WordTrace]
  refine ⟨19761653005096904228282575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26348870673462538971043433 19761653005096904228282575)
  ·
    refine ⟨29642479507645356342423863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19761653005096904228282575 29642479507645356342423863)
    ·
      refine ⟨44463719261468034513635795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29642479507645356342423863 44463719261468034513635795)
      ·
        refine ⟨66695578892202051770453693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44463719261468034513635795 66695578892202051770453693)
        ·
          refine ⟨25010842084575769413920135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66695578892202051770453693 25010842084575769413920135)
          ·
            refine ⟨37516263126863654120880203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25010842084575769413920135 37516263126863654120880203)
            ·
              refine ⟨56274394690295481181320305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37516263126863654120880203 56274394690295481181320305)
              ·
                refine ⟨42205796017721610885990229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56274394690295481181320305 42205796017721610885990229)
                ·
                  refine ⟨247299586041337563785099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42205796017721610885990229 247299586041337563785099)
                  ·
                    rfl

theorem cell21_1083632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_1083632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083632 prefixEnd_1083632 := by exact prefixLift 1083632
  have htrace : WordTrace (prefixWord ++ tailWord_1083632) baseStart_1083632 baseEnd_1083632 := by
    simpa [prefixWord, tailWord_1083632, baseEnd_1083632] using wordTrace_append hprefix tailTrace_1083632
  have hstable : (prefixWord ++ tailWord_1083632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083632).length < 2 ^ (prefixWord ++ tailWord_1083632).sum := by decide
  have hdescent : baseEnd_1083632 < baseStart_1083632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083649 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 5]
def baseStart_1083649 : Nat := 118140960795 + 1083649 * 2 ^ 59
def prefixEnd_1083649 : Nat := 4983230072969 + 3 ^ 40 * 1083649 * 2
def baseEnd_1083649 : Nat := 247303465672949312001731

theorem tailTrace_1083649 : CollatzResearch.WordTrace tailWord_1083649 prefixEnd_1083649 247303465672949312001731 := by
  unfold tailWord_1083649
  simp only [CollatzResearch.WordTrace]
  refine ⟨39523926051132220359934001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26349284034088146906622667 39523926051132220359934001)
  ·
    refine ⟨29642944538349165269950501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39523926051132220359934001 29642944538349165269950501)
    ·
      refine ⟨5558052100940468488115719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29642944538349165269950501 5558052100940468488115719)
      ·
        refine ⟨8337078151410702732173579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5558052100940468488115719 8337078151410702732173579)
        ·
          refine ⟨12505617227116054098260369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8337078151410702732173579 12505617227116054098260369)
          ·
            refine ⟨9379212920337040573695277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12505617227116054098260369 9379212920337040573695277)
            ·
              refine ⟨3517204845126390215135729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9379212920337040573695277 3517204845126390215135729)
              ·
                refine ⟨2637903633844792661351797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3517204845126390215135729 2637903633844792661351797)
                ·
                  refine ⟨247303465672949312001731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2637903633844792661351797 247303465672949312001731)
                  ·
                    rfl

theorem cell21_1083649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_1083649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083649 prefixEnd_1083649 := by exact prefixLift 1083649
  have htrace : WordTrace (prefixWord ++ tailWord_1083649) baseStart_1083649 baseEnd_1083649 := by
    simpa [prefixWord, tailWord_1083649, baseEnd_1083649] using wordTrace_append hprefix tailTrace_1083649
  have hstable : (prefixWord ++ tailWord_1083649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083649).length < 2 ^ (prefixWord ++ tailWord_1083649).sum := by decide
  have hdescent : baseEnd_1083649 < baseStart_1083649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083652 : List Nat := [2, 3, 2, 2, 3, 1, 3, 5]
def baseStart_1083652 : Nat := 118140960795 + 1083652 * 2 ^ 59
def prefixEnd_1083652 : Nat := 4983230072969 + 3 ^ 40 * 1083652 * 2
def baseEnd_1083652 : Nat := 82434716771273991150575

theorem tailTrace_1083652 : CollatzResearch.WordTrace tailWord_1083652 prefixEnd_1083652 82434716771273991150575 := by
  unfold tailWord_1083652
  simp only [CollatzResearch.WordTrace]
  refine ⟨19762017735060675936146605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26349356980080901248195473 19762017735060675936146605)
  ·
    refine ⟨7410756650647753476054977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19762017735060675936146605 7410756650647753476054977)
    ·
      refine ⟨5558067487985815107041233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7410756650647753476054977 5558067487985815107041233)
      ·
        refine ⟨4168550615989361330280925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5558067487985815107041233 4168550615989361330280925)
        ·
          refine ⟨1563206480996010498855347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4168550615989361330280925 1563206480996010498855347)
          ·
            refine ⟨2344809721494015748283021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563206480996010498855347 2344809721494015748283021)
            ·
              refine ⟨879303645560255905606133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2344809721494015748283021 879303645560255905606133)
              ·
                refine ⟨82434716771273991150575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879303645560255905606133 82434716771273991150575)
                ·
                  rfl

theorem cell21_1083652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_1083652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083652 prefixEnd_1083652 := by exact prefixLift 1083652
  have htrace : WordTrace (prefixWord ++ tailWord_1083652) baseStart_1083652 baseEnd_1083652 := by
    simpa [prefixWord, tailWord_1083652, baseEnd_1083652] using wordTrace_append hprefix tailTrace_1083652
  have hstable : (prefixWord ++ tailWord_1083652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083652).length < 2 ^ (prefixWord ++ tailWord_1083652).sum := by decide
  have hdescent : baseEnd_1083652 < baseStart_1083652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083680 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_1083680 : Nat := 118140960795 + 1083680 * 2 ^ 59
def prefixEnd_1083680 : Nat := 4983230072969 + 3 ^ 40 * 1083680 * 2
def baseEnd_1083680 : Nat := 247310540295300146985001

theorem tailTrace_1083680 : CollatzResearch.WordTrace tailWord_1083680 prefixEnd_1083680 247310540295300146985001 := by
  unfold tailWord_1083680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19762528357009956327156247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26350037809346608436208329 19762528357009956327156247)
  ·
    refine ⟨29643792535514934490734371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19762528357009956327156247 29643792535514934490734371)
    ·
      refine ⟨44465688803272401736101557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29643792535514934490734371 44465688803272401736101557)
      ·
        refine ⟨4168658325306787662759521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44465688803272401736101557 4168658325306787662759521)
        ·
          refine ⟨3126493743980090747069641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168658325306787662759521 3126493743980090747069641)
          ·
            refine ⟨2344870307985068060302231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126493743980090747069641 2344870307985068060302231)
            ·
              refine ⟨3517305461977602090453347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344870307985068060302231 3517305461977602090453347)
              ·
                refine ⟨5275958192966403135680021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3517305461977602090453347 5275958192966403135680021)
                ·
                  refine ⟨247310540295300146985001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5275958192966403135680021 247310540295300146985001)
                  ·
                    rfl

theorem cell21_1083680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_1083680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083680 prefixEnd_1083680 := by exact prefixLift 1083680
  have htrace : WordTrace (prefixWord ++ tailWord_1083680) baseStart_1083680 baseEnd_1083680 := by
    simpa [prefixWord, tailWord_1083680, baseEnd_1083680] using wordTrace_append hprefix tailTrace_1083680
  have hstable : (prefixWord ++ tailWord_1083680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083680).length < 2 ^ (prefixWord ++ tailWord_1083680).sum := by decide
  have hdescent : baseEnd_1083680 < baseStart_1083680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083908 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1083908 : Nat := 118140960795 + 1083908 * 2 ^ 59
def prefixEnd_1083908 : Nat := 4983230072969 + 3 ^ 40 * 1083908 * 2
def baseEnd_1083908 : Nat := 247362573001622417184535

theorem tailTrace_1083908 : CollatzResearch.WordTrace tailWord_1083908 prefixEnd_1083908 247362573001622417184535 := by
  unfold tailWord_1083908
  simp only [CollatzResearch.WordTrace]
  refine ⟨19766686278596953796806189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26355581704795938395741585 19766686278596953796806189)
  ·
    refine ⟨7412507354473857673802321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19766686278596953796806189 7412507354473857673802321)
    ·
      refine ⟨5559380515855393255351741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7412507354473857673802321 5559380515855393255351741)
      ·
        refine ⟨2084767693445772470756903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5559380515855393255351741 2084767693445772470756903)
        ·
          refine ⟨3127151540168658706135355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084767693445772470756903 3127151540168658706135355)
          ·
            refine ⟨4690727310252988059203033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127151540168658706135355 4690727310252988059203033)
            ·
              refine ⟨3518045482689741044402275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4690727310252988059203033 3518045482689741044402275)
              ·
                refine ⟨5277068224034611566603413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518045482689741044402275 5277068224034611566603413)
                ·
                  refine ⟨247362573001622417184535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5277068224034611566603413 247362573001622417184535)
                  ·
                    rfl

theorem cell21_1083908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1083908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083908 prefixEnd_1083908 := by exact prefixLift 1083908
  have htrace : WordTrace (prefixWord ++ tailWord_1083908) baseStart_1083908 baseEnd_1083908 := by
    simpa [prefixWord, tailWord_1083908, baseEnd_1083908] using wordTrace_append hprefix tailTrace_1083908
  have hstable : (prefixWord ++ tailWord_1083908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083908).length < 2 ^ (prefixWord ++ tailWord_1083908).sum := by decide
  have hdescent : baseEnd_1083908 < baseStart_1083908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083911 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 5]
def baseStart_1083911 : Nat := 118140960795 + 1083911 * 2 ^ 59
def prefixEnd_1083911 : Nat := 4983230072969 + 3 ^ 40 * 1083911 * 2
def baseEnd_1083911 : Nat := 247363257642495078634529

theorem tailTrace_1083911 : CollatzResearch.WordTrace tailWord_1083911 prefixEnd_1083911 247363257642495078634529 := by
  unfold tailWord_1083911
  simp only [CollatzResearch.WordTrace]
  refine ⟨39533481976183039105971587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26355654650788692737314391 39533481976183039105971587)
  ·
    refine ⟨59300222964274558658957381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39533481976183039105971587 59300222964274558658957381)
    ·
      refine ⟨11118791805801479748554509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59300222964274558658957381 11118791805801479748554509)
      ·
        refine ⟨4169546927175554905707941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11118791805801479748554509 4169546927175554905707941)
        ·
          refine ⟨781790048845416544820239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4169546927175554905707941 781790048845416544820239)
          ·
            refine ⟨1172685073268124817230359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781790048845416544820239 1172685073268124817230359)
            ·
              refine ⟨1759027609902187225845539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172685073268124817230359 1759027609902187225845539)
              ·
                refine ⟨2638541414853280838768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759027609902187225845539 2638541414853280838768309)
                ·
                  refine ⟨247363257642495078634529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2638541414853280838768309 247363257642495078634529)
                  ·
                    rfl

theorem cell21_1083911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 5].length) (baseStart_1083911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083911 prefixEnd_1083911 := by exact prefixLift 1083911
  have htrace : WordTrace (prefixWord ++ tailWord_1083911) baseStart_1083911 baseEnd_1083911 := by
    simpa [prefixWord, tailWord_1083911, baseEnd_1083911] using wordTrace_append hprefix tailTrace_1083911
  have hstable : (prefixWord ++ tailWord_1083911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083911).length < 2 ^ (prefixWord ++ tailWord_1083911).sum := by decide
  have hdescent : baseEnd_1083911 < baseStart_1083911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083956 : List Nat := [2, 5, 1, 3, 2, 8]
def baseStart_1083956 : Nat := 118140960795 + 1083956 * 2 ^ 59
def prefixEnd_1083956 : Nat := 4983230072969 + 3 ^ 40 * 1083956 * 2
def baseEnd_1083956 : Nat := 9161982490947592606831

theorem tailTrace_1083956 : CollatzResearch.WordTrace tailWord_1083956 prefixEnd_1083956 9161982490947592606831 := by
  unfold tailWord_1083956
  simp only [CollatzResearch.WordTrace]
  refine ⟨19767561630510005895679861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26356748840680007860906481 19767561630510005895679861)
  ·
    refine ⟨1853208902860313052719987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19767561630510005895679861 1853208902860313052719987)
    ·
      refine ⟨2779813354290469579079981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853208902860313052719987 2779813354290469579079981)
      ·
        refine ⟨1042430007858926092154993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2779813354290469579079981 1042430007858926092154993)
        ·
          refine ⟨781822505894194569116245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042430007858926092154993 781822505894194569116245)
          ·
            refine ⟨9161982490947592606831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 781822505894194569116245 9161982490947592606831)
            ·
              rfl

theorem cell21_1083956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 8].length) (baseStart_1083956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1083956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1083956 prefixEnd_1083956 := by exact prefixLift 1083956
  have htrace : WordTrace (prefixWord ++ tailWord_1083956) baseStart_1083956 baseEnd_1083956 := by
    simpa [prefixWord, tailWord_1083956, baseEnd_1083956] using wordTrace_append hprefix tailTrace_1083956
  have hstable : (prefixWord ++ tailWord_1083956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083956).length < 2 ^ (prefixWord ++ tailWord_1083956).sum := by decide
  have hdescent : baseEnd_1083956 < baseStart_1083956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084018 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1084018 : Nat := 118140960795 + 1084018 * 2 ^ 59
def prefixEnd_1084018 : Nat := 4983230072969 + 3 ^ 40 * 1084018 * 2
def baseEnd_1084018 : Nat := 247387676500286670350977

theorem tailTrace_1084018 : CollatzResearch.WordTrace tailWord_1084018 prefixEnd_1084018 247387676500286670350977 := by
  unfold tailWord_1084018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9884346146698849095029177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26358256391196930920077805 9884346146698849095029177)
  ·
    refine ⟨7413259610024136821271883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9884346146698849095029177 7413259610024136821271883)
    ·
      refine ⟨11119889415036205231907825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7413259610024136821271883 11119889415036205231907825)
      ·
        refine ⟨8339917061277153923930869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11119889415036205231907825 8339917061277153923930869)
        ·
          refine ⟨781867224494733180368519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8339917061277153923930869 781867224494733180368519)
          ·
            refine ⟨1172800836742099770552779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781867224494733180368519 1172800836742099770552779)
            ·
              refine ⟨1759201255113149655829169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172800836742099770552779 1759201255113149655829169)
              ·
                refine ⟨1319400941334862241871877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1759201255113149655829169 1319400941334862241871877)
                ·
                  refine ⟨247387676500286670350977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319400941334862241871877 247387676500286670350977)
                  ·
                    rfl

theorem cell21_1084018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1084018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084018 prefixEnd_1084018 := by exact prefixLift 1084018
  have htrace : WordTrace (prefixWord ++ tailWord_1084018) baseStart_1084018 baseEnd_1084018 := by
    simpa [prefixWord, tailWord_1084018, baseEnd_1084018] using wordTrace_append hprefix tailTrace_1084018
  have hstable : (prefixWord ++ tailWord_1084018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084018).length < 2 ^ (prefixWord ++ tailWord_1084018).sum := by decide
  have hdescent : baseEnd_1084018 < baseStart_1084018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084057 : List Nat := [1, 2, 1, 2, 1, 2, 5, 7]
def baseStart_1084057 : Nat := 118140960795 + 1084057 * 2 ^ 59
def prefixEnd_1084057 : Nat := 4983230072969 + 3 ^ 40 * 1084057 * 2
def baseEnd_1084057 : Nat := 82465525610543756400299

theorem tailTrace_1084057 : CollatzResearch.WordTrace tailWord_1084057 prefixEnd_1084057 82465525610543756400299 := by
  unfold tailWord_1084057
  simp only [CollatzResearch.WordTrace]
  refine ⟨39538807033654106040786425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26359204689102737360524283 39538807033654106040786425)
  ·
    refine ⟨29654105275240579530589819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39538807033654106040786425 29654105275240579530589819)
    ·
      refine ⟨44481157912860869295884729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29654105275240579530589819 44481157912860869295884729)
      ·
        refine ⟨33360868434645651971913547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44481157912860869295884729 33360868434645651971913547)
        ·
          refine ⟨50041302651968477957870321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33360868434645651971913547 50041302651968477957870321)
          ·
            refine ⟨37530976988976358468402741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50041302651968477957870321 37530976988976358468402741)
            ·
              refine ⟨3518529092716533606412757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37530976988976358468402741 3518529092716533606412757)
              ·
                refine ⟨82465525610543756400299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3518529092716533606412757 82465525610543756400299)
                ·
                  rfl

theorem cell21_1084057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 7].length) (baseStart_1084057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084057 prefixEnd_1084057 := by exact prefixLift 1084057
  have htrace : WordTrace (prefixWord ++ tailWord_1084057) baseStart_1084057 baseEnd_1084057 := by
    simpa [prefixWord, tailWord_1084057, baseEnd_1084057] using wordTrace_append hprefix tailTrace_1084057
  have hstable : (prefixWord ++ tailWord_1084057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084057).length < 2 ^ (prefixWord ++ tailWord_1084057).sum := by decide
  have hdescent : baseEnd_1084057 < baseStart_1084057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084133 : List Nat := [1, 3, 1, 4, 1, 11]
def baseStart_1084133 : Nat := 118140960795 + 1084133 * 2 ^ 59
def prefixEnd_1084133 : Nat := 4983230072969 + 3 ^ 40 * 1084133 * 2
def baseEnd_1084133 : Nat := 9163478558039704664225

theorem tailTrace_1084133 : CollatzResearch.WordTrace tailWord_1084133 prefixEnd_1084133 9163478558039704664225 := by
  unfold tailWord_1084133
  simp only [CollatzResearch.WordTrace]
  refine ⟨39541578981378771020553053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26361052654252514013702035 39541578981378771020553053)
  ·
    refine ⟨14828092118017039132707395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39541578981378771020553053 14828092118017039132707395)
    ·
      refine ⟨22242138177025558699061093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14828092118017039132707395 22242138177025558699061093)
      ·
        refine ⟨4170400908192292256073955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22242138177025558699061093 4170400908192292256073955)
        ·
          refine ⟨6255601362288438384110933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4170400908192292256073955 6255601362288438384110933)
          ·
            refine ⟨9163478558039704664225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6255601362288438384110933 9163478558039704664225)
            ·
              rfl

theorem cell21_1084133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 11].length) (baseStart_1084133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084133 prefixEnd_1084133 := by exact prefixLift 1084133
  have htrace : WordTrace (prefixWord ++ tailWord_1084133) baseStart_1084133 baseEnd_1084133 := by
    simpa [prefixWord, tailWord_1084133, baseEnd_1084133] using wordTrace_append hprefix tailTrace_1084133
  have hstable : (prefixWord ++ tailWord_1084133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084133).length < 2 ^ (prefixWord ++ tailWord_1084133).sum := by decide
  have hdescent : baseEnd_1084133 < baseStart_1084133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084167 : List Nat := [1, 1, 4, 4, 1, 2, 3, 5]
def baseStart_1084167 : Nat := 118140960795 + 1084167 * 2 ^ 59
def prefixEnd_1084167 : Nat := 4983230072969 + 3 ^ 40 * 1084167 * 2
def baseEnd_1084167 : Nat := 82473893443431840789113

theorem tailTrace_1084167 : CollatzResearch.WordTrace tailWord_1084167 prefixEnd_1084167 82473893443431840789113 := by
  unfold tailWord_1084167
  simp only [CollatzResearch.WordTrace]
  refine ⟨39542819063255594827290755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26361879375503729884860503 39542819063255594827290755)
  ·
    refine ⟨59314228594883392240936133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39542819063255594827290755 59314228594883392240936133)
    ·
      refine ⟨11121417861540636045175525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59314228594883392240936133 11121417861540636045175525)
      ·
        refine ⟨2085265849038869258470411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11121417861540636045175525 2085265849038869258470411)
        ·
          refine ⟨3127898773558303887705617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2085265849038869258470411 3127898773558303887705617)
          ·
            refine ⟨2345924080168727915779213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3127898773558303887705617 2345924080168727915779213)
            ·
              refine ⟨879721530063272968417205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2345924080168727915779213 879721530063272968417205)
              ·
                refine ⟨82473893443431840789113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879721530063272968417205 82473893443431840789113)
                ·
                  rfl

theorem cell21_1084167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 5].length) (baseStart_1084167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084167 prefixEnd_1084167 := by exact prefixLift 1084167
  have htrace : WordTrace (prefixWord ++ tailWord_1084167) baseStart_1084167 baseEnd_1084167 := by
    simpa [prefixWord, tailWord_1084167, baseEnd_1084167] using wordTrace_append hprefix tailTrace_1084167
  have hstable : (prefixWord ++ tailWord_1084167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084167).length < 2 ^ (prefixWord ++ tailWord_1084167).sum := by decide
  have hdescent : baseEnd_1084167 < baseStart_1084167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084209 : List Nat := [1, 2, 2, 3, 2, 1, 2, 8]
def baseStart_1084209 : Nat := 118140960795 + 1084209 * 2 ^ 59
def prefixEnd_1084209 : Nat := 4983230072969 + 3 ^ 40 * 1084209 * 2
def baseEnd_1084209 : Nat := 82477088434170927555751

theorem tailTrace_1084209 : CollatzResearch.WordTrace tailWord_1084209 prefixEnd_1084209 82477088434170927555751 := by
  unfold tailWord_1084209
  simp only [CollatzResearch.WordTrace]
  refine ⟨39544350929103436000319681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26362900619402290666879787 39544350929103436000319681)
  ·
    refine ⟨29658263196827577000239761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39544350929103436000319681 29658263196827577000239761)
    ·
      refine ⟨22243697397620682750179821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29658263196827577000239761 22243697397620682750179821)
      ·
        refine ⟨8341386524107756031317433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22243697397620682750179821 8341386524107756031317433)
        ·
          refine ⟨6256039893080817023488075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8341386524107756031317433 6256039893080817023488075)
          ·
            refine ⟨9384059839621225535232113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6256039893080817023488075 9384059839621225535232113)
            ·
              refine ⟨7038044879715919151424085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9384059839621225535232113 7038044879715919151424085)
              ·
                refine ⟨82477088434170927555751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7038044879715919151424085 82477088434170927555751)
                ·
                  rfl

theorem cell21_1084209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 8].length) (baseStart_1084209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084209 prefixEnd_1084209 := by exact prefixLift 1084209
  have htrace : WordTrace (prefixWord ++ tailWord_1084209) baseStart_1084209 baseEnd_1084209 := by
    simpa [prefixWord, tailWord_1084209, baseEnd_1084209] using wordTrace_append hprefix tailTrace_1084209
  have hstable : (prefixWord ++ tailWord_1084209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084209).length < 2 ^ (prefixWord ++ tailWord_1084209).sum := by decide
  have hdescent : baseEnd_1084209 < baseStart_1084209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084285 : List Nat := [1, 4, 1, 1, 2, 1, 4, 7]
def baseStart_1084285 : Nat := 118140960795 + 1084285 * 2 ^ 59
def prefixEnd_1084285 : Nat := 4983230072969 + 3 ^ 40 * 1084285 * 2
def baseEnd_1084285 : Nat := 82482869845984513133477

theorem tailTrace_1084285 : CollatzResearch.WordTrace tailWord_1084285 prefixEnd_1084285 82482869845984513133477 := by
  unfold tailWord_1084285
  simp only [CollatzResearch.WordTrace]
  refine ⟨39547122876828100980086309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26364748584552067320057539 39547122876828100980086309)
  ·
    refine ⟨7415085539405268933766183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39547122876828100980086309 7415085539405268933766183)
    ·
      refine ⟨11122628309107903400649275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7415085539405268933766183 11122628309107903400649275)
      ·
        refine ⟨16683942463661855100973913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11122628309107903400649275 16683942463661855100973913)
        ·
          refine ⟨12512956847746391325730435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16683942463661855100973913 12512956847746391325730435)
          ·
            refine ⟨18769435271619586988595653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12512956847746391325730435 18769435271619586988595653)
            ·
              refine ⟨3519269113428672560361685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18769435271619586988595653 3519269113428672560361685)
              ·
                refine ⟨82482869845984513133477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3519269113428672560361685 82482869845984513133477)
                ·
                  rfl

theorem cell21_1084285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 7].length) (baseStart_1084285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084285 prefixEnd_1084285 := by exact prefixLift 1084285
  have htrace : WordTrace (prefixWord ++ tailWord_1084285) baseStart_1084285 baseEnd_1084285 := by
    simpa [prefixWord, tailWord_1084285, baseEnd_1084285] using wordTrace_append hprefix tailTrace_1084285
  have hstable : (prefixWord ++ tailWord_1084285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084285).length < 2 ^ (prefixWord ++ tailWord_1084285).sum := by decide
  have hdescent : baseEnd_1084285 < baseStart_1084285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084350 : List Nat := [4, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_1084350 : Nat := 118140960795 + 1084350 * 2 ^ 59
def prefixEnd_1084350 : Nat := 4983230072969 + 3 ^ 40 * 1084350 * 2
def baseEnd_1084350 : Nat := 247463443423527870816965

theorem tailTrace_1084350 : CollatzResearch.WordTrace tailWord_1084350 prefixEnd_1084350 247463443423527870816965 := by
  unfold tailWord_1084350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943686702699077135150313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26366329081061744720801669 4943686702699077135150313)
  ·
    refine ⟨3707765027024307851362735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4943686702699077135150313 3707765027024307851362735)
    ·
      refine ⟨5561647540536461777044103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3707765027024307851362735 5561647540536461777044103)
      ·
        refine ⟨8342471310804692665566155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5561647540536461777044103 8342471310804692665566155)
        ·
          refine ⟨12513706966207038998349233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8342471310804692665566155 12513706966207038998349233)
          ·
            refine ⟨9385280224655279248761925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12513706966207038998349233 9385280224655279248761925)
            ·
              refine ⟨1759740042122864859142861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9385280224655279248761925 1759740042122864859142861)
              ·
                refine ⟨659902515796074322178573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1759740042122864859142861 659902515796074322178573)
                ·
                  refine ⟨247463443423527870816965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659902515796074322178573 247463443423527870816965)
                  ·
                    rfl

theorem cell21_1084350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_1084350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084350 prefixEnd_1084350 := by exact prefixLift 1084350
  have htrace : WordTrace (prefixWord ++ tailWord_1084350) baseStart_1084350 baseEnd_1084350 := by
    simpa [prefixWord, tailWord_1084350, baseEnd_1084350] using wordTrace_append hprefix tailTrace_1084350
  have hstable : (prefixWord ++ tailWord_1084350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084350).length < 2 ^ (prefixWord ++ tailWord_1084350).sum := by decide
  have hdescent : baseEnd_1084350 < baseStart_1084350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084381 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 4]
def baseStart_1084381 : Nat := 118140960795 + 1084381 * 2 ^ 59
def prefixEnd_1084381 : Nat := 4983230072969 + 3 ^ 40 * 1084381 * 2
def baseEnd_1084381 : Nat := 247470518045878705800235

theorem tailTrace_1084381 : CollatzResearch.WordTrace tailWord_1084381 prefixEnd_1084381 247470518045878705800235 := by
  unfold tailWord_1084381
  simp only [CollatzResearch.WordTrace]
  refine ⟨39550624284480309375580997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26367082856320206250387331 39550624284480309375580997)
  ·
    refine ⟨7415742053340058007921437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39550624284480309375580997 7415742053340058007921437)
    ·
      refine ⟨2780903270002521752970539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7415742053340058007921437 2780903270002521752970539)
      ·
        refine ⟨4171354905003782629455809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780903270002521752970539 4171354905003782629455809)
        ·
          refine ⟨3128516178752836972091857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4171354905003782629455809 3128516178752836972091857)
          ·
            refine ⟨2346387134064627729068893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3128516178752836972091857 2346387134064627729068893)
            ·
              refine ⟨879895175274235398400835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2346387134064627729068893 879895175274235398400835)
              ·
                refine ⟨1319842762911353097601253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879895175274235398400835 1319842762911353097601253)
                ·
                  refine ⟨247470518045878705800235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319842762911353097601253 247470518045878705800235)
                  ·
                    rfl

theorem cell21_1084381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_1084381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084381 prefixEnd_1084381 := by exact prefixLift 1084381
  have htrace : WordTrace (prefixWord ++ tailWord_1084381) baseStart_1084381 baseEnd_1084381 := by
    simpa [prefixWord, tailWord_1084381, baseEnd_1084381] using wordTrace_append hprefix tailTrace_1084381
  have hstable : (prefixWord ++ tailWord_1084381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084381).length < 2 ^ (prefixWord ++ tailWord_1084381).sum := by decide
  have hdescent : baseEnd_1084381 < baseStart_1084381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084392 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_1084392 : Nat := 118140960795 + 1084392 * 2 ^ 59
def prefixEnd_1084392 : Nat := 4983230072969 + 3 ^ 40 * 1084392 * 2
def baseEnd_1084392 : Nat := 247473028395745131116879

theorem tailTrace_1084392 : CollatzResearch.WordTrace tailWord_1084392 prefixEnd_1084392 247473028395745131116879 := by
  unfold tailWord_1084392
  simp only [CollatzResearch.WordTrace]
  refine ⟨19775512743720229127115715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26367350324960305502820953 19775512743720229127115715)
  ·
    refine ⟨29663269115580343690673573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19775512743720229127115715 29663269115580343690673573)
    ·
      refine ⟨5561862959171314442001295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29663269115580343690673573 5561862959171314442001295)
      ·
        refine ⟨8342794438756971663001943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5561862959171314442001295 8342794438756971663001943)
        ·
          refine ⟨12514191658135457494502915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8342794438756971663001943 12514191658135457494502915)
          ·
            refine ⟨18771287487203186241754373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12514191658135457494502915 18771287487203186241754373)
            ·
              refine ⟨3519616403850597420328945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18771287487203186241754373 3519616403850597420328945)
              ·
                refine ⟨2639712302887948065246709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3519616403850597420328945 2639712302887948065246709)
                ·
                  refine ⟨247473028395745131116879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2639712302887948065246709 247473028395745131116879)
                  ·
                    rfl

theorem cell21_1084392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_1084392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084392 prefixEnd_1084392 := by exact prefixLift 1084392
  have htrace : WordTrace (prefixWord ++ tailWord_1084392) baseStart_1084392 baseEnd_1084392 := by
    simpa [prefixWord, tailWord_1084392, baseEnd_1084392] using wordTrace_append hprefix tailTrace_1084392
  have hstable : (prefixWord ++ tailWord_1084392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084392).length < 2 ^ (prefixWord ++ tailWord_1084392).sum := by decide
  have hdescent : baseEnd_1084392 < baseStart_1084392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084423 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 4]
def baseStart_1084423 : Nat := 118140960795 + 1084423 * 2 ^ 59
def prefixEnd_1084423 : Nat := 4983230072969 + 3 ^ 40 * 1084423 * 2
def baseEnd_1084423 : Nat := 247480103018095966100149

theorem tailTrace_1084423 : CollatzResearch.WordTrace tailWord_1084423 prefixEnd_1084423 247480103018095966100149 := by
  unfold tailWord_1084423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39552156150328150548609923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26368104100218767032406615 39552156150328150548609923)
  ·
    refine ⟨59328234225492225822914885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39552156150328150548609923 59328234225492225822914885)
    ·
      refine ⟨11124043917279792341796541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59328234225492225822914885 11124043917279792341796541)
      ·
        refine ⟨4171516468979922128173703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11124043917279792341796541 4171516468979922128173703)
        ·
          refine ⟨6257274703469883192260555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171516468979922128173703 6257274703469883192260555)
          ·
            refine ⟨9385912055204824788390833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257274703469883192260555 9385912055204824788390833)
            ·
              refine ⟨7039434041403618591293125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9385912055204824788390833 7039434041403618591293125)
              ·
                refine ⟨1319893882763178485867461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7039434041403618591293125 1319893882763178485867461)
                ·
                  refine ⟨247480103018095966100149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319893882763178485867461 247480103018095966100149)
                  ·
                    rfl

theorem cell21_1084423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_1084423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084423 prefixEnd_1084423 := by exact prefixLift 1084423
  have htrace : WordTrace (prefixWord ++ tailWord_1084423) baseStart_1084423 baseEnd_1084423 := by
    simpa [prefixWord, tailWord_1084423, baseEnd_1084423] using wordTrace_append hprefix tailTrace_1084423
  have hstable : (prefixWord ++ tailWord_1084423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084423).length < 2 ^ (prefixWord ++ tailWord_1084423).sum := by decide
  have hdescent : baseEnd_1084423 < baseStart_1084423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084437 : List Nat := [1, 3, 2, 1, 4, 1, 1, 8]
def baseStart_1084437 : Nat := 118140960795 + 1084437 * 2 ^ 59
def prefixEnd_1084437 : Nat := 4983230072969 + 3 ^ 40 * 1084437 * 2
def baseEnd_1084437 : Nat := 82494432669611684288929

theorem tailTrace_1084437 : CollatzResearch.WordTrace tailWord_1084437 prefixEnd_1084437 82494432669611684288929 := by
  unfold tailWord_1084437
  simp only [CollatzResearch.WordTrace]
  refine ⟨39552666772277430939619565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26368444514851620626413043 39552666772277430939619565)
  ·
    refine ⟨14832250039604036602357337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39552666772277430939619565 14832250039604036602357337)
    ·
      refine ⟨11124187529703027451768003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14832250039604036602357337 11124187529703027451768003)
      ·
        refine ⟨16686281294554541177652005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11124187529703027451768003 16686281294554541177652005)
        ·
          refine ⟨3128677742728976470809751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16686281294554541177652005 3128677742728976470809751)
          ·
            refine ⟨4693016614093464706214627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128677742728976470809751 4693016614093464706214627)
            ·
              refine ⟨7039524921140197059321941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693016614093464706214627 7039524921140197059321941)
              ·
                refine ⟨82494432669611684288929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7039524921140197059321941 82494432669611684288929)
                ·
                  rfl

theorem cell21_1084437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 8].length) (baseStart_1084437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084437 prefixEnd_1084437 := by exact prefixLift 1084437
  have htrace : WordTrace (prefixWord ++ tailWord_1084437) baseStart_1084437 baseEnd_1084437 := by
    simpa [prefixWord, tailWord_1084437, baseEnd_1084437] using wordTrace_append hprefix tailTrace_1084437
  have hstable : (prefixWord ++ tailWord_1084437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084437).length < 2 ^ (prefixWord ++ tailWord_1084437).sum := by decide
  have hdescent : baseEnd_1084437 < baseStart_1084437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084440 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_1084440 : Nat := 118140960795 + 1084440 * 2 ^ 59
def prefixEnd_1084440 : Nat := 4983230072969 + 3 ^ 40 * 1084440 * 2
def baseEnd_1084440 : Nat := 247483982649707714316781

theorem tailTrace_1084440 : CollatzResearch.WordTrace tailWord_1084440 prefixEnd_1084440 247483982649707714316781 := by
  unfold tailWord_1084440
  simp only [CollatzResearch.WordTrace]
  refine ⟨19776388095633281225989387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26368517460844374967985849 19776388095633281225989387)
  ·
    refine ⟨29664582143449921838984081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19776388095633281225989387 29664582143449921838984081)
    ·
      refine ⟨22248436607587441379238061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29664582143449921838984081 22248436607587441379238061)
      ·
        refine ⟨8343163727845290517214273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22248436607587441379238061 8343163727845290517214273)
        ·
          refine ⟨6257372795883967887910705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8343163727845290517214273 6257372795883967887910705)
          ·
            refine ⟨4693029596912975915933029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257372795883967887910705 4693029596912975915933029)
            ·
              refine ⟨879943049421182984237443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4693029596912975915933029 879943049421182984237443)
              ·
                refine ⟨1319914574131774476356165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879943049421182984237443 1319914574131774476356165)
                ·
                  refine ⟨247483982649707714316781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319914574131774476356165 247483982649707714316781)
                  ·
                    rfl

theorem cell21_1084440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_1084440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084440 prefixEnd_1084440 := by exact prefixLift 1084440
  have htrace : WordTrace (prefixWord ++ tailWord_1084440) baseStart_1084440 baseEnd_1084440 := by
    simpa [prefixWord, tailWord_1084440, baseEnd_1084440] using wordTrace_append hprefix tailTrace_1084440
  have hstable : (prefixWord ++ tailWord_1084440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084440).length < 2 ^ (prefixWord ++ tailWord_1084440).sum := by decide
  have hdescent : baseEnd_1084440 < baseStart_1084440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084527 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 7]
def baseStart_1084527 : Nat := 118140960795 + 1084527 * 2 ^ 59
def prefixEnd_1084527 : Nat := 4983230072969 + 3 ^ 40 * 1084527 * 2
def baseEnd_1084527 : Nat := 247503837235014896366603

theorem tailTrace_1084527 : CollatzResearch.WordTrace tailWord_1084527 prefixEnd_1084527 247503837235014896366603 := by
  unfold tailWord_1084527
  simp only [CollatzResearch.WordTrace]
  refine ⟨39555949341951376310395835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26370632894634250873597223 39555949341951376310395835)
  ·
    refine ⟨59333924012927064465593753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39555949341951376310395835 59333924012927064465593753)
    ·
      refine ⟨44500443009695298349195315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59333924012927064465593753 44500443009695298349195315)
      ·
        refine ⟨66750664514542947523792973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44500443009695298349195315 66750664514542947523792973)
        ·
          refine ⟨25031499192953605321422365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66750664514542947523792973 25031499192953605321422365)
          ·
            refine ⟨9386812197357601995533387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25031499192953605321422365 9386812197357601995533387)
            ·
              refine ⟨14080218296036402993300081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9386812197357601995533387 14080218296036402993300081)
              ·
                refine ⟨10560163722027302244975061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14080218296036402993300081 10560163722027302244975061)
                ·
                  refine ⟨247503837235014896366603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10560163722027302244975061 247503837235014896366603)
                  ·
                    rfl

theorem cell21_1084527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_1084527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084527 prefixEnd_1084527 := by exact prefixLift 1084527
  have htrace : WordTrace (prefixWord ++ tailWord_1084527) baseStart_1084527 baseEnd_1084527 := by
    simpa [prefixWord, tailWord_1084527, baseEnd_1084527] using wordTrace_append hprefix tailTrace_1084527
  have hstable : (prefixWord ++ tailWord_1084527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084527).length < 2 ^ (prefixWord ++ tailWord_1084527).sum := by decide
  have hdescent : baseEnd_1084527 < baseStart_1084527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084603 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 5]
def baseStart_1084603 : Nat := 118140960795 + 1084603 * 2 ^ 59
def prefixEnd_1084603 : Nat := 4983230072969 + 3 ^ 40 * 1084603 * 2
def baseEnd_1084603 : Nat := 247521181470455653099781

theorem tailTrace_1084603 : CollatzResearch.WordTrace tailWord_1084603 prefixEnd_1084603 247521181470455653099781 := by
  unfold tailWord_1084603
  simp only [CollatzResearch.WordTrace]
  refine ⟨39558721289676041290162463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26372480859784027526774975 39558721289676041290162463)
  ·
    refine ⟨59338081934514061935243695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39558721289676041290162463 59338081934514061935243695)
    ·
      refine ⟨89007122901771092902865543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59338081934514061935243695 89007122901771092902865543)
      ·
        refine ⟨133510684352656639354298315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89007122901771092902865543 133510684352656639354298315)
        ·
          refine ⟨200266026528984959031447473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133510684352656639354298315 200266026528984959031447473)
          ·
            refine ⟨150199519896738719273585605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200266026528984959031447473 150199519896738719273585605)
            ·
              refine ⟨28162409980638509863797301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150199519896738719273585605 28162409980638509863797301)
              ·
                refine ⟨2640225935684860299730997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28162409980638509863797301 2640225935684860299730997)
                ·
                  refine ⟨247521181470455653099781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2640225935684860299730997 247521181470455653099781)
                  ·
                    rfl

theorem cell21_1084603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_1084603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084603 prefixEnd_1084603 := by exact prefixLift 1084603
  have htrace : WordTrace (prefixWord ++ tailWord_1084603) baseStart_1084603 baseEnd_1084603 := by
    simpa [prefixWord, tailWord_1084603, baseEnd_1084603] using wordTrace_append hprefix tailTrace_1084603
  have hstable : (prefixWord ++ tailWord_1084603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084603).length < 2 ^ (prefixWord ++ tailWord_1084603).sum := by decide
  have hdescent : baseEnd_1084603 < baseStart_1084603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084606 : List Nat := [4, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1084606 : Nat := 118140960795 + 1084606 * 2 ^ 59
def prefixEnd_1084606 : Nat := 4983230072969 + 3 ^ 40 * 1084606 * 2
def baseEnd_1084606 : Nat := 82507288703776104849925

theorem tailTrace_1084606 : CollatzResearch.WordTrace tailWord_1084606 prefixEnd_1084606 82507288703776104849925 := by
  unfold tailWord_1084606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4944853838583146600315209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26372553805776781868347781 4944853838583146600315209)
  ·
    refine ⟨3708640378937359950236407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4944853838583146600315209 3708640378937359950236407)
    ·
      refine ⟨5562960568406039925354611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3708640378937359950236407 5562960568406039925354611)
      ·
        refine ⟨8344440852609059888031917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5562960568406039925354611 8344440852609059888031917)
        ·
          refine ⟨3129165319728397458011969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8344440852609059888031917 3129165319728397458011969)
          ·
            refine ⟨2346873989796298093508977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3129165319728397458011969 2346873989796298093508977)
            ·
              refine ⟨1760155492347223570131733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346873989796298093508977 1760155492347223570131733)
              ·
                refine ⟨82507288703776104849925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1760155492347223570131733 82507288703776104849925)
                ·
                  rfl

theorem cell21_1084606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1084606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084606 prefixEnd_1084606 := by exact prefixLift 1084606
  have htrace : WordTrace (prefixWord ++ tailWord_1084606) baseStart_1084606 baseEnd_1084606 := by
    simpa [prefixWord, tailWord_1084606, baseEnd_1084606] using wordTrace_append hprefix tailTrace_1084606
  have hstable : (prefixWord ++ tailWord_1084606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084606).length < 2 ^ (prefixWord ++ tailWord_1084606).sum := by decide
  have hdescent : baseEnd_1084606 < baseStart_1084606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084609 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 4]
def baseStart_1084609 : Nat := 118140960795 + 1084609 * 2 ^ 59
def prefixEnd_1084609 : Nat := 4983230072969 + 3 ^ 40 * 1084609 * 2
def baseEnd_1084609 : Nat := 247522550752200975999769

theorem tailTrace_1084609 : CollatzResearch.WordTrace tailWord_1084609 prefixEnd_1084609 247522550752200975999769 := by
  unfold tailWord_1084609
  simp only [CollatzResearch.WordTrace]
  refine ⟨39558940127654304314880881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26372626751769536209920587 39558940127654304314880881)
  ·
    refine ⟨29669205095740728236160661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39558940127654304314880881 29669205095740728236160661)
    ·
      refine ⟨1390743988862846636070031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29669205095740728236160661 1390743988862846636070031)
      ·
        refine ⟨2086115983294269954105047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1390743988862846636070031 2086115983294269954105047)
        ·
          refine ⟨3129173974941404931157571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086115983294269954105047 3129173974941404931157571)
          ·
            refine ⟨4693760962412107396736357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129173974941404931157571 4693760962412107396736357)
            ·
              refine ⟨880080180452270136888067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4693760962412107396736357 880080180452270136888067)
              ·
                refine ⟨1320120270678405205332101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880080180452270136888067 1320120270678405205332101)
                ·
                  refine ⟨247522550752200975999769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320120270678405205332101 247522550752200975999769)
                  ·
                    rfl

theorem cell21_1084609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_1084609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084609 prefixEnd_1084609 := by exact prefixLift 1084609
  have htrace : WordTrace (prefixWord ++ tailWord_1084609) baseStart_1084609 baseEnd_1084609 := by
    simpa [prefixWord, tailWord_1084609, baseEnd_1084609] using wordTrace_append hprefix tailTrace_1084609
  have hstable : (prefixWord ++ tailWord_1084609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084609).length < 2 ^ (prefixWord ++ tailWord_1084609).sum := by decide
  have hdescent : baseEnd_1084609 < baseStart_1084609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084651 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 4]
def baseStart_1084651 : Nat := 118140960795 + 1084651 * 2 ^ 59
def prefixEnd_1084651 : Nat := 4983230072969 + 3 ^ 40 * 1084651 * 2
def baseEnd_1084651 : Nat := 247532135724418236299683

theorem tailTrace_1084651 : CollatzResearch.WordTrace tailWord_1084651 prefixEnd_1084651 247532135724418236299683 := by
  unfold tailWord_1084651
  simp only [CollatzResearch.WordTrace]
  refine ⟨39560471993502145487909807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26373647995668096991939871 39560471993502145487909807)
  ·
    refine ⟨59340707990253218231864711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39560471993502145487909807 59340707990253218231864711)
    ·
      refine ⟨89011061985379827347797067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59340707990253218231864711 89011061985379827347797067)
      ·
        refine ⟨133516592978069741021695601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89011061985379827347797067 133516592978069741021695601)
        ·
          refine ⟨100137444733552305766271701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133516592978069741021695601 100137444733552305766271701)
          ·
            refine ⟨2346971360942632166396993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 100137444733552305766271701 2346971360942632166396993)
            ·
              refine ⟨1760228520706974124797745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346971360942632166396993 1760228520706974124797745)
              ·
                refine ⟨1320171390530230593598309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760228520706974124797745 1320171390530230593598309)
                ·
                  refine ⟨247532135724418236299683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320171390530230593598309 247532135724418236299683)
                  ·
                    rfl

theorem cell21_1084651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_1084651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084651 prefixEnd_1084651 := by exact prefixLift 1084651
  have htrace : WordTrace (prefixWord ++ tailWord_1084651) baseStart_1084651 baseEnd_1084651 := by
    simpa [prefixWord, tailWord_1084651, baseEnd_1084651] using wordTrace_append hprefix tailTrace_1084651
  have hstable : (prefixWord ++ tailWord_1084651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084651).length < 2 ^ (prefixWord ++ tailWord_1084651).sum := by decide
  have hdescent : baseEnd_1084651 < baseStart_1084651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084654 : List Nat := [4, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_1084654 : Nat := 118140960795 + 1084654 * 2 ^ 59
def prefixEnd_1084654 : Nat := 4983230072969 + 3 ^ 40 * 1084654 * 2
def baseEnd_1084654 : Nat := 247532820365290897749677

theorem tailTrace_1084654 : CollatzResearch.WordTrace tailWord_1084654 prefixEnd_1084654 247532820365290897749677 := by
  unfold tailWord_1084654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4945072676561409625033627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26373720941660851333512677 4945072676561409625033627)
  ·
    refine ⟨7417609014842114437550441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4945072676561409625033627 7417609014842114437550441)
    ·
      refine ⟨5563206761131585828162831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7417609014842114437550441 5563206761131585828162831)
      ·
        refine ⟨8344810141697378742244247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5563206761131585828162831 8344810141697378742244247)
        ·
          refine ⟨12517215212546068113366371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8344810141697378742244247 12517215212546068113366371)
          ·
            refine ⟨18775822818819102170049557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12517215212546068113366371 18775822818819102170049557)
            ·
              refine ⟨880116694632145414221073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18775822818819102170049557 880116694632145414221073)
              ·
                refine ⟨660087520974109060665805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880116694632145414221073 660087520974109060665805)
                ·
                  refine ⟨247532820365290897749677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660087520974109060665805 247532820365290897749677)
                  ·
                    rfl

theorem cell21_1084654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_1084654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084654 prefixEnd_1084654 := by exact prefixLift 1084654
  have htrace : WordTrace (prefixWord ++ tailWord_1084654) baseStart_1084654 baseEnd_1084654 := by
    simpa [prefixWord, tailWord_1084654, baseEnd_1084654] using wordTrace_append hprefix tailTrace_1084654
  have hstable : (prefixWord ++ tailWord_1084654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084654).length < 2 ^ (prefixWord ++ tailWord_1084654).sum := by decide
  have hdescent : baseEnd_1084654 < baseStart_1084654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084702 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1084702 : Nat := 118140960795 + 1084702 * 2 ^ 59
def prefixEnd_1084702 : Nat := 4983230072969 + 3 ^ 40 * 1084702 * 2
def baseEnd_1084702 : Nat := 247543774619253480949579

theorem tailTrace_1084702 : CollatzResearch.WordTrace tailWord_1084702 prefixEnd_1084702 247543774619253480949579 := by
  unfold tailWord_1084702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4945291514539672649752045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26374888077544920798677573 4945291514539672649752045)
  ·
    refine ⟨1854484317952377243657017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4945291514539672649752045 1854484317952377243657017)
    ·
      refine ⟨1390863238464282932742763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1854484317952377243657017 1390863238464282932742763)
      ·
        refine ⟨2086294857696424399114145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1390863238464282932742763 2086294857696424399114145)
        ·
          refine ⟨1564721143272318299335609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2086294857696424399114145 1564721143272318299335609)
          ·
            refine ⟨1173540857454238724501707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1564721143272318299335609 1173540857454238724501707)
            ·
              refine ⟨1760311286181358086752561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173540857454238724501707 1760311286181358086752561)
              ·
                refine ⟨1320233464636018565064421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760311286181358086752561 1320233464636018565064421)
                ·
                  refine ⟨247543774619253480949579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320233464636018565064421 247543774619253480949579)
                  ·
                    rfl

theorem cell21_1084702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1084702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084702 prefixEnd_1084702 := by exact prefixLift 1084702
  have htrace : WordTrace (prefixWord ++ tailWord_1084702) baseStart_1084702 baseEnd_1084702 := by
    simpa [prefixWord, tailWord_1084702, baseEnd_1084702] using wordTrace_append hprefix tailTrace_1084702
  have hstable : (prefixWord ++ tailWord_1084702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084702).length < 2 ^ (prefixWord ++ tailWord_1084702).sum := by decide
  have hdescent : baseEnd_1084702 < baseStart_1084702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084772 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_1084772 : Nat := 118140960795 + 1084772 * 2 ^ 59
def prefixEnd_1084772 : Nat := 4983230072969 + 3 ^ 40 * 1084772 * 2
def baseEnd_1084772 : Nat := 247559749572948914782769

theorem tailTrace_1084772 : CollatzResearch.WordTrace tailWord_1084772 prefixEnd_1084772 247559749572948914782769 := by
  unfold tailWord_1084772
  simp only [CollatzResearch.WordTrace]
  refine ⟨19782442613031891576532285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26376590150709188768709713 19782442613031891576532285)
  ·
    refine ⟨7418415979886959341199607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19782442613031891576532285 7418415979886959341199607)
    ·
      refine ⟨11127623969830439011799411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7418415979886959341199607 11127623969830439011799411)
      ·
        refine ⟨16691435954745658517699117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11127623969830439011799411 16691435954745658517699117)
        ·
          refine ⟨6259288483029621944137169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16691435954745658517699117 6259288483029621944137169)
          ·
            refine ⟨4694466362272216458102877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6259288483029621944137169 4694466362272216458102877)
            ·
              refine ⟨1760424885852081171788579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4694466362272216458102877 1760424885852081171788579)
              ·
                refine ⟨2640637328778121757682869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760424885852081171788579 2640637328778121757682869)
                ·
                  refine ⟨247559749572948914782769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2640637328778121757682869 247559749572948914782769)
                  ·
                    rfl

theorem cell21_1084772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_1084772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084772 prefixEnd_1084772 := by exact prefixLift 1084772
  have htrace : WordTrace (prefixWord ++ tailWord_1084772) baseStart_1084772 baseEnd_1084772 := by
    simpa [prefixWord, tailWord_1084772, baseEnd_1084772] using wordTrace_append hprefix tailTrace_1084772
  have hstable : (prefixWord ++ tailWord_1084772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084772).length < 2 ^ (prefixWord ++ tailWord_1084772).sum := by decide
  have hdescent : baseEnd_1084772 < baseStart_1084772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084778 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_1084778 : Nat := 118140960795 + 1084778 * 2 ^ 59
def prefixEnd_1084778 : Nat := 4983230072969 + 3 ^ 40 * 1084778 * 2
def baseEnd_1084778 : Nat := 247561118854694237682757

theorem tailTrace_1084778 : CollatzResearch.WordTrace tailWord_1084778 prefixEnd_1084778 247561118854694237682757 := by
  unfold tailWord_1084778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891276016010511544445747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26376736042694697451855325 9891276016010511544445747)
  ·
    refine ⟨14836914024015767316668621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9891276016010511544445747 14836914024015767316668621)
    ·
      refine ⟨5563842759005912743750733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14836914024015767316668621 5563842759005912743750733)
      ·
        refine ⟨2086441034627217278906525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5563842759005912743750733 2086441034627217278906525)
        ·
          refine ⟨782415387985206479589947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2086441034627217278906525 782415387985206479589947)
          ·
            refine ⟨1173623081977809719384921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782415387985206479589947 1173623081977809719384921)
            ·
              refine ⟨880217311483357289538691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173623081977809719384921 880217311483357289538691)
              ·
                refine ⟨1320325967225035934308037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880217311483357289538691 1320325967225035934308037)
                ·
                  refine ⟨247561118854694237682757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320325967225035934308037 247561118854694237682757)
                  ·
                    rfl

theorem cell21_1084778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_1084778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084778 prefixEnd_1084778 := by exact prefixLift 1084778
  have htrace : WordTrace (prefixWord ++ tailWord_1084778) baseStart_1084778 baseEnd_1084778 := by
    simpa [prefixWord, tailWord_1084778, baseEnd_1084778] using wordTrace_append hprefix tailTrace_1084778
  have hstable : (prefixWord ++ tailWord_1084778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084778).length < 2 ^ (prefixWord ++ tailWord_1084778).sum := by decide
  have hdescent : baseEnd_1084778 < baseStart_1084778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084820 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1084820 : Nat := 118140960795 + 1084820 * 2 ^ 59
def prefixEnd_1084820 : Nat := 4983230072969 + 3 ^ 40 * 1084820 * 2
def baseEnd_1084820 : Nat := 247570703826911497982671

theorem tailTrace_1084820 : CollatzResearch.WordTrace tailWord_1084820 prefixEnd_1084820 247570703826911497982671 := by
  unfold tailWord_1084820
  simp only [CollatzResearch.WordTrace]
  refine ⟨19783317964944943675405957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26377757286593258233874609 19783317964944943675405957)
  ·
    refine ⟨3709372118427176939138617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19783317964944943675405957 3709372118427176939138617)
    ·
      refine ⟨2782029088820382704353963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3709372118427176939138617 2782029088820382704353963)
      ·
        refine ⟨4173043633230574056530945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2782029088820382704353963 4173043633230574056530945)
        ·
          refine ⟨3129782724922930542398209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4173043633230574056530945 3129782724922930542398209)
          ·
            refine ⟨2347337043692197906798657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3129782724922930542398209 2347337043692197906798657)
            ·
              refine ⟨1760502782769148430098993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2347337043692197906798657 1760502782769148430098993)
              ·
                refine ⟨1320377087076861322574245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760502782769148430098993 1320377087076861322574245)
                ·
                  refine ⟨247570703826911497982671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320377087076861322574245 247570703826911497982671)
                  ·
                    rfl

theorem cell21_1084820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1084820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084820 prefixEnd_1084820 := by exact prefixLift 1084820
  have htrace : WordTrace (prefixWord ++ tailWord_1084820) baseStart_1084820 baseEnd_1084820 := by
    simpa [prefixWord, tailWord_1084820, baseEnd_1084820] using wordTrace_append hprefix tailTrace_1084820
  have hstable : (prefixWord ++ tailWord_1084820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084820).length < 2 ^ (prefixWord ++ tailWord_1084820).sum := by decide
  have hdescent : baseEnd_1084820 < baseStart_1084820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084834 : List Nat := [3, 3, 1, 2, 1, 4, 1, 6]
def baseStart_1084834 : Nat := 118140960795 + 1084834 * 2 ^ 59
def prefixEnd_1084834 : Nat := 4983230072969 + 3 ^ 40 * 1084834 * 2
def baseEnd_1084834 : Nat := 82524632939216861583103

theorem tailTrace_1084834 : CollatzResearch.WordTrace tailWord_1084834 prefixEnd_1084834 82524632939216861583103 := by
  unfold tailWord_1084834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891786637959791935455389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26378097701226111827881037 9891786637959791935455389)
  ·
    refine ⟨3709419989234921975795771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9891786637959791935455389 3709419989234921975795771)
    ·
      refine ⟨5564129983852382963693657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709419989234921975795771 5564129983852382963693657)
      ·
        refine ⟨4173097487889287222770243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5564129983852382963693657 4173097487889287222770243)
        ·
          refine ⟨6259646231833930834155365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4173097487889287222770243 6259646231833930834155365)
          ·
            refine ⟨1173683668468862031404131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6259646231833930834155365 1173683668468862031404131)
            ·
              refine ⟨1760525502703293047106197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173683668468862031404131 1760525502703293047106197)
              ·
                refine ⟨82524632939216861583103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1760525502703293047106197 82524632939216861583103)
                ·
                  rfl

theorem cell21_1084834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_1084834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084834 prefixEnd_1084834 := by exact prefixLift 1084834
  have htrace : WordTrace (prefixWord ++ tailWord_1084834) baseStart_1084834 baseEnd_1084834 := by
    simpa [prefixWord, tailWord_1084834, baseEnd_1084834] using wordTrace_append hprefix tailTrace_1084834
  have hstable : (prefixWord ++ tailWord_1084834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084834).length < 2 ^ (prefixWord ++ tailWord_1084834).sum := by decide
  have hdescent : baseEnd_1084834 < baseStart_1084834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084862 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1084862 : Nat := 118140960795 + 1084862 * 2 ^ 59
def prefixEnd_1084862 : Nat := 4983230072969 + 3 ^ 40 * 1084862 * 2
def baseEnd_1084862 : Nat := 247580288799128758282585

theorem tailTrace_1084862 : CollatzResearch.WordTrace tailWord_1084862 prefixEnd_1084862 247580288799128758282585 := by
  unfold tailWord_1084862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946020974467216065480105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26378778530491819015893893 4946020974467216065480105)
  ·
    refine ⟨3709515730850412049110079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4946020974467216065480105 3709515730850412049110079)
    ·
      refine ⟨5564273596275618073665119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709515730850412049110079 5564273596275618073665119)
      ·
        refine ⟨8346410394413427110497679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5564273596275618073665119 8346410394413427110497679)
        ·
          refine ⟨12519615591620140665746519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8346410394413427110497679 12519615591620140665746519)
          ·
            refine ⟨18779423387430210998619779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12519615591620140665746519 18779423387430210998619779)
            ·
              refine ⟨28169135081145316497929669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18779423387430210998619779 28169135081145316497929669)
              ·
                refine ⟨5281712827714746843361813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28169135081145316497929669 5281712827714746843361813)
                ·
                  refine ⟨247580288799128758282585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5281712827714746843361813 247580288799128758282585)
                  ·
                    rfl

theorem cell21_1084862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1084862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084862 prefixEnd_1084862 := by exact prefixLift 1084862
  have htrace : WordTrace (prefixWord ++ tailWord_1084862) baseStart_1084862 baseEnd_1084862 := by
    simpa [prefixWord, tailWord_1084862, baseEnd_1084862] using wordTrace_append hprefix tailTrace_1084862
  have hstable : (prefixWord ++ tailWord_1084862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084862).length < 2 ^ (prefixWord ++ tailWord_1084862).sum := by decide
  have hdescent : baseEnd_1084862 < baseStart_1084862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084938 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1084938 : Nat := 118140960795 + 1084938 * 2 ^ 59
def prefixEnd_1084938 : Nat := 4983230072969 + 3 ^ 40 * 1084938 * 2
def baseEnd_1084938 : Nat := 247597633034569515015763

theorem tailTrace_1084938 : CollatzResearch.WordTrace tailWord_1084938 prefixEnd_1084938 247597633034569515015763 := by
  unfold tailWord_1084938
  simp only [CollatzResearch.WordTrace]
  refine ⟨9892734935865598375901867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26380626495641595669071645 9892734935865598375901867)
  ·
    refine ⟨14839102403798397563852801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9892734935865598375901867 14839102403798397563852801)
    ·
      refine ⟨11129326802848798172889601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14839102403798397563852801 11129326802848798172889601)
      ·
        refine ⟨8346995102136598629667201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11129326802848798172889601 8346995102136598629667201)
        ·
          refine ⟨6260246326602448972250401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8346995102136598629667201 6260246326602448972250401)
          ·
            refine ⟨4695184744951836729187801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6260246326602448972250401 4695184744951836729187801)
            ·
              refine ⟨3521388558713877546890851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4695184744951836729187801 3521388558713877546890851)
              ·
                refine ⟨5282082838070816320336277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521388558713877546890851 5282082838070816320336277)
                ·
                  refine ⟨247597633034569515015763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5282082838070816320336277 247597633034569515015763)
                  ·
                    rfl

theorem cell21_1084938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1084938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1084938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1084938 prefixEnd_1084938 := by exact prefixLift 1084938
  have htrace : WordTrace (prefixWord ++ tailWord_1084938) baseStart_1084938 baseEnd_1084938 := by
    simpa [prefixWord, tailWord_1084938, baseEnd_1084938] using wordTrace_append hprefix tailTrace_1084938
  have hstable : (prefixWord ++ tailWord_1084938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084938).length < 2 ^ (prefixWord ++ tailWord_1084938).sum := by decide
  have hdescent : baseEnd_1084938 < baseStart_1084938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085045 : List Nat := [1, 3, 4, 2, 1, 2, 8]
def baseStart_1085045 : Nat := 118140960795 + 1085045 * 2 ^ 59
def prefixEnd_1085045 : Nat := 4983230072969 + 3 ^ 40 * 1085045 * 2
def baseEnd_1085045 : Nat := 27513561321373456303579

theorem tailTrace_1085045 : CollatzResearch.WordTrace tailWord_1085045 prefixEnd_1085045 27513561321373456303579 := by
  unfold tailWord_1085045
  simp only [CollatzResearch.WordTrace]
  refine ⟨39574842354074750777752589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26383228236049833851835059 39574842354074750777752589)
  ·
    refine ⟨14840565882778031541657221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39574842354074750777752589 14840565882778031541657221)
    ·
      refine ⟨2782606103020880914060729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14840565882778031541657221 2782606103020880914060729)
      ·
        refine ⟨2086954577265660685545547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2782606103020880914060729 2086954577265660685545547)
        ·
          refine ⟨3130431865898491028318321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086954577265660685545547 3130431865898491028318321)
          ·
            refine ⟨2347823899423868271238741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3130431865898491028318321 2347823899423868271238741)
            ·
              refine ⟨27513561321373456303579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2347823899423868271238741 27513561321373456303579)
              ·
                rfl

theorem cell21_1085045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 8].length) (baseStart_1085045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085045 prefixEnd_1085045 := by exact prefixLift 1085045
  have htrace : WordTrace (prefixWord ++ tailWord_1085045) baseStart_1085045 baseEnd_1085045 := by
    simpa [prefixWord, tailWord_1085045, baseEnd_1085045] using wordTrace_append hprefix tailTrace_1085045
  have hstable : (prefixWord ++ tailWord_1085045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085045).length < 2 ^ (prefixWord ++ tailWord_1085045).sum := by decide
  have hdescent : baseEnd_1085045 < baseStart_1085045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085096 : List Nat := [2, 1, 7, 1, 2, 1, 7]
def baseStart_1085096 : Nat := 118140960795 + 1085096 * 2 ^ 59
def prefixEnd_1085096 : Nat := 4983230072969 + 3 ^ 40 * 1085096 * 2
def baseEnd_1085096 : Nat := 27514854531910705709123

theorem tailTrace_1085096 : CollatzResearch.WordTrace tailWord_1085096 prefixEnd_1085096 27514854531910705709123 := by
  unfold tailWord_1085096
  simp only [CollatzResearch.WordTrace]
  refine ⟨19788351238444993243929571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26384468317926657658572761 19788351238444993243929571)
  ·
    refine ⟨29682526857667489865894357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19788351238444993243929571 29682526857667489865894357)
    ·
      refine ⟨695684223226581793731899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 29682526857667489865894357 695684223226581793731899)
      ·
        refine ⟨1043526334839872690597849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695684223226581793731899 1043526334839872690597849)
        ·
          refine ⟨782644751129904517948387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043526334839872690597849 782644751129904517948387)
          ·
            refine ⟨1173967126694856776922581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782644751129904517948387 1173967126694856776922581)
            ·
              refine ⟨27514854531910705709123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1173967126694856776922581 27514854531910705709123)
              ·
                rfl

theorem cell21_1085096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 7].length) (baseStart_1085096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085096 prefixEnd_1085096 := by exact prefixLift 1085096
  have htrace : WordTrace (prefixWord ++ tailWord_1085096) baseStart_1085096 baseEnd_1085096 := by
    simpa [prefixWord, tailWord_1085096, baseEnd_1085096] using wordTrace_append hprefix tailTrace_1085096
  have hstable : (prefixWord ++ tailWord_1085096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085096).length < 2 ^ (prefixWord ++ tailWord_1085096).sum := by decide
  have hdescent : baseEnd_1085096 < baseStart_1085096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085110 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1085110 : Nat := 118140960795 + 1085110 * 2 ^ 59
def prefixEnd_1085110 : Nat := 4983230072969 + 3 ^ 40 * 1085110 * 2
def baseEnd_1085110 : Nat := 247636885777935438148745

theorem tailTrace_1085110 : CollatzResearch.WordTrace tailWord_1085110 prefixEnd_1085110 247636885777935438148745 := by
  unfold tailWord_1085110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473575818677454179929299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26384808732559511252579189 2473575818677454179929299)
  ·
    refine ⟨3710363728016181269893949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2473575818677454179929299 3710363728016181269893949)
    ·
      refine ⟨1391386398006067976210231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3710363728016181269893949 1391386398006067976210231)
      ·
        refine ⟨2087079597009101964315347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391386398006067976210231 2087079597009101964315347)
        ·
          refine ⟨3130619395513652946473021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087079597009101964315347 3130619395513652946473021)
          ·
            refine ⟨1173982273317619854927383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3130619395513652946473021 1173982273317619854927383)
            ·
              refine ⟨1760973409976429782391075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173982273317619854927383 1760973409976429782391075)
              ·
                refine ⟨2641460114964644673586613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760973409976429782391075 2641460114964644673586613)
                ·
                  refine ⟨247636885777935438148745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2641460114964644673586613 247636885777935438148745)
                  ·
                    rfl

theorem cell21_1085110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1085110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085110 prefixEnd_1085110 := by exact prefixLift 1085110
  have htrace : WordTrace (prefixWord ++ tailWord_1085110) baseStart_1085110 baseEnd_1085110 := by
    simpa [prefixWord, tailWord_1085110, baseEnd_1085110] using wordTrace_append hprefix tailTrace_1085110
  have hstable : (prefixWord ++ tailWord_1085110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085110).length < 2 ^ (prefixWord ++ tailWord_1085110).sum := by decide
  have hdescent : baseEnd_1085110 < baseStart_1085110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085169 : List Nat := [1, 2, 2, 2, 2, 3, 4, 2, 3]
def baseStart_1085169 : Nat := 118140960795 + 1085169 * 2 ^ 59
def prefixEnd_1085169 : Nat := 4983230072969 + 3 ^ 40 * 1085169 * 2
def baseEnd_1085169 : Nat := 247650350381764446665291

theorem tailTrace_1085169 : CollatzResearch.WordTrace tailWord_1085169 prefixEnd_1085169 247650350381764446665291 := by
  unfold tailWord_1085169
  simp only [CollatzResearch.WordTrace]
  refine ⟨39579365005625519955266561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26386243337083679970177707 39579365005625519955266561)
  ·
    refine ⟨29684523754219139966449921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39579365005625519955266561 29684523754219139966449921)
    ·
      refine ⟨22263392815664354974837441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29684523754219139966449921 22263392815664354974837441)
      ·
        refine ⟨16697544611748266231128081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22263392815664354974837441 16697544611748266231128081)
        ·
          refine ⟨12523158458811199673346061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16697544611748266231128081 12523158458811199673346061)
          ·
            refine ⟨4696184422054199877504773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12523158458811199673346061 4696184422054199877504773)
            ·
              refine ⟨880534579135162477032145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4696184422054199877504773 880534579135162477032145)
              ·
                refine ⟨660400934351371857774109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880534579135162477032145 660400934351371857774109)
                ·
                  refine ⟨247650350381764446665291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660400934351371857774109 247650350381764446665291)
                  ·
                    rfl

theorem cell21_1085169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_1085169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085169 prefixEnd_1085169 := by exact prefixLift 1085169
  have htrace : WordTrace (prefixWord ++ tailWord_1085169) baseStart_1085169 baseEnd_1085169 := by
    simpa [prefixWord, tailWord_1085169, baseEnd_1085169] using wordTrace_append hprefix tailTrace_1085169
  have hstable : (prefixWord ++ tailWord_1085169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085169).length < 2 ^ (prefixWord ++ tailWord_1085169).sum := by decide
  have hdescent : baseEnd_1085169 < baseStart_1085169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085228 : List Nat := [2, 2, 1, 1, 1, 5, 2, 4, 3]
def baseStart_1085228 : Nat := 118140960795 + 1085228 * 2 ^ 59
def prefixEnd_1085228 : Nat := 4983230072969 + 3 ^ 40 * 1085228 * 2
def baseEnd_1085228 : Nat := 247663814985593455181837

theorem tailTrace_1085228 : CollatzResearch.WordTrace tailWord_1085228 prefixEnd_1085228 247663814985593455181837 := by
  unfold tailWord_1085228
  simp only [CollatzResearch.WordTrace]
  refine ⟨19790758456205886515832169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26387677941607848687776225 19790758456205886515832169)
  ·
    refine ⟨14843068842154414886874127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19790758456205886515832169 14843068842154414886874127)
    ·
      refine ⟨22264603263231622330311191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14843068842154414886874127 22264603263231622330311191)
      ·
        refine ⟨33396904894847433495466787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22264603263231622330311191 33396904894847433495466787)
        ·
          refine ⟨50095357342271150243200181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33396904894847433495466787 50095357342271150243200181)
          ·
            refine ⟨4696439750837920335300017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50095357342271150243200181 4696439750837920335300017)
            ·
              refine ⟨3522329813128440251475013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696439750837920335300017 3522329813128440251475013)
              ·
                refine ⟨660436839961582547151565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3522329813128440251475013 660436839961582547151565)
                ·
                  refine ⟨247663814985593455181837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660436839961582547151565 247663814985593455181837)
                  ·
                    rfl

theorem cell21_1085228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_1085228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085228 prefixEnd_1085228 := by exact prefixLift 1085228
  have htrace : WordTrace (prefixWord ++ tailWord_1085228) baseStart_1085228 baseEnd_1085228 := by
    simpa [prefixWord, tailWord_1085228, baseEnd_1085228] using wordTrace_append hprefix tailTrace_1085228
  have hstable : (prefixWord ++ tailWord_1085228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085228).length < 2 ^ (prefixWord ++ tailWord_1085228).sum := by decide
  have hdescent : baseEnd_1085228 < baseStart_1085228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085256 : List Nat := [2, 1, 3, 1, 1, 5, 1, 7]
def baseStart_1085256 : Nat := 118140960795 + 1085256 * 2 ^ 59
def prefixEnd_1085256 : Nat := 4983230072969 + 3 ^ 40 * 1085256 * 2
def baseEnd_1085256 : Nat := 82556734989023876238371

theorem tailTrace_1085256 : CollatzResearch.WordTrace tailWord_1085256 prefixEnd_1085256 82556734989023876238371 := by
  unfold tailWord_1085256
  simp only [CollatzResearch.WordTrace]
  refine ⟨19791269078155166906841811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26388358770873555875789081 19791269078155166906841811)
  ·
    refine ⟨29686903617232750360262717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19791269078155166906841811 29686903617232750360262717)
    ·
      refine ⟨11132588856462281385098519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29686903617232750360262717 11132588856462281385098519)
      ·
        refine ⟨16698883284693422077647779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11132588856462281385098519 16698883284693422077647779)
        ·
          refine ⟨25048324927040133116471669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16698883284693422077647779 25048324927040133116471669)
          ·
            refine ⟨2348280461910012479669219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25048324927040133116471669 2348280461910012479669219)
            ·
              refine ⟨3522420692865018719503829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348280461910012479669219 3522420692865018719503829)
              ·
                refine ⟨82556734989023876238371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3522420692865018719503829 82556734989023876238371)
                ·
                  rfl

theorem cell21_1085256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_1085256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085256 prefixEnd_1085256 := by exact prefixLift 1085256
  have htrace : WordTrace (prefixWord ++ tailWord_1085256) baseStart_1085256 baseEnd_1085256 := by
    simpa [prefixWord, tailWord_1085256, baseEnd_1085256] using wordTrace_append hprefix tailTrace_1085256
  have hstable : (prefixWord ++ tailWord_1085256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085256).length < 2 ^ (prefixWord ++ tailWord_1085256).sum := by decide
  have hdescent : baseEnd_1085256 < baseStart_1085256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085290 : List Nat := [3, 1, 3, 4, 1, 1, 2, 6]
def baseStart_1085290 : Nat := 118140960795 + 1085290 * 2 ^ 59
def prefixEnd_1085290 : Nat := 4983230072969 + 3 ^ 40 * 1085290 * 2
def baseEnd_1085290 : Nat := 82559321410098375049459

theorem tailTrace_1085290 : CollatzResearch.WordTrace tailWord_1085290 prefixEnd_1085290 82559321410098375049459 := by
  unfold tailWord_1085290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9895944559546789405105331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26389185492124771746947549 9895944559546789405105331)
  ·
    refine ⟨14843916839320184107657997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9895944559546789405105331 14843916839320184107657997)
    ·
      refine ⟨5566468814745069040371749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14843916839320184107657997 5566468814745069040371749)
      ·
        refine ⟨1043712902764700445069703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5566468814745069040371749 1043712902764700445069703)
        ·
          refine ⟨1565569354147050667604555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043712902764700445069703 1565569354147050667604555)
          ·
            refine ⟨2348354031220576001406833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565569354147050667604555 2348354031220576001406833)
            ·
              refine ⟨1761265523415432001055125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2348354031220576001406833 1761265523415432001055125)
              ·
                refine ⟨82559321410098375049459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1761265523415432001055125 82559321410098375049459)
                ·
                  rfl

theorem cell21_1085290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_1085290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085290 prefixEnd_1085290 := by exact prefixLift 1085290
  have htrace : WordTrace (prefixWord ++ tailWord_1085290) baseStart_1085290 baseEnd_1085290 := by
    simpa [prefixWord, tailWord_1085290, baseEnd_1085290] using wordTrace_append hprefix tailTrace_1085290
  have hstable : (prefixWord ++ tailWord_1085290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085290).length < 2 ^ (prefixWord ++ tailWord_1085290).sum := by decide
  have hdescent : baseEnd_1085290 < baseStart_1085290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085332 : List Nat := [2, 4, 2, 1, 1, 11]
def baseStart_1085332 : Nat := 118140960795 + 1085332 * 2 ^ 59
def prefixEnd_1085332 : Nat := 4983230072969 + 3 ^ 40 * 1085332 * 2
def baseEnd_1085332 : Nat := 9173612933426384646233

theorem tailTrace_1085332 : CollatzResearch.WordTrace tailWord_1085332 prefixEnd_1085332 9173612933426384646233 := by
  unfold tailWord_1085332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19792655052017499396725125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26390206736023332528966833 19792655052017499396725125)
  ·
    refine ⟨3711122822253281136885961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19792655052017499396725125 3711122822253281136885961)
    ·
      refine ⟨2783342116689960852664471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3711122822253281136885961 2783342116689960852664471)
      ·
        refine ⟨4175013175034941278996707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783342116689960852664471 4175013175034941278996707)
        ·
          refine ⟨6262519762552411918495061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175013175034941278996707 6262519762552411918495061)
          ·
            refine ⟨9173612933426384646233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6262519762552411918495061 9173612933426384646233)
            ·
              rfl

theorem cell21_1085332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 11].length) (baseStart_1085332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085332 prefixEnd_1085332 := by exact prefixLift 1085332
  have htrace : WordTrace (prefixWord ++ tailWord_1085332) baseStart_1085332 baseEnd_1085332 := by
    simpa [prefixWord, tailWord_1085332, baseEnd_1085332] using wordTrace_append hprefix tailTrace_1085332
  have hstable : (prefixWord ++ tailWord_1085332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085332).length < 2 ^ (prefixWord ++ tailWord_1085332).sum := by decide
  have hdescent : baseEnd_1085332 < baseStart_1085332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085338 : List Nat := [3, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_1085338 : Nat := 118140960795 + 1085338 * 2 ^ 59
def prefixEnd_1085338 : Nat := 4983230072969 + 3 ^ 40 * 1085338 * 2
def baseEnd_1085338 : Nat := 247688918484257708348279

theorem tailTrace_1085338 : CollatzResearch.WordTrace tailWord_1085338 prefixEnd_1085338 247688918484257708348279 := by
  unfold tailWord_1085338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896382235503315454542167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26390352628008841212112445 9896382235503315454542167)
  ·
    refine ⟨14844573353254973181813251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9896382235503315454542167 14844573353254973181813251)
    ·
      refine ⟨22266860029882459772719877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14844573353254973181813251 22266860029882459772719877)
      ·
        refine ⟨4175036255602961207384977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22266860029882459772719877 4175036255602961207384977)
        ·
          refine ⟨3131277191702220905538733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4175036255602961207384977 3131277191702220905538733)
          ·
            refine ⟨1174228946888332839577025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3131277191702220905538733 1174228946888332839577025)
            ·
              refine ⟨880671710166249629682769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174228946888332839577025 880671710166249629682769)
              ·
                refine ⟨660503782624687222262077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880671710166249629682769 660503782624687222262077)
                ·
                  refine ⟨247688918484257708348279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660503782624687222262077 247688918484257708348279)
                  ·
                    rfl

theorem cell21_1085338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_1085338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085338 prefixEnd_1085338 := by exact prefixLift 1085338
  have htrace : WordTrace (prefixWord ++ tailWord_1085338) baseStart_1085338 baseEnd_1085338 := by
    simpa [prefixWord, tailWord_1085338, baseEnd_1085338] using wordTrace_append hprefix tailTrace_1085338
  have hstable : (prefixWord ++ tailWord_1085338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085338).length < 2 ^ (prefixWord ++ tailWord_1085338).sum := by decide
  have hdescent : baseEnd_1085338 < baseStart_1085338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085391 : List Nat := [1, 1, 2, 1, 1, 5, 10]
def baseStart_1085391 : Nat := 118140960795 + 1085391 * 2 ^ 59
def prefixEnd_1085391 : Nat := 4983230072969 + 3 ^ 40 * 1085391 * 2
def baseEnd_1085391 : Nat := 27522334867371265996093

theorem tailTrace_1085391 : CollatzResearch.WordTrace tailWord_1085391 prefixEnd_1085391 27522334867371265996093 := by
  unfold tailWord_1085391
  simp only [CollatzResearch.WordTrace]
  refine ⟨39587462010821251869848027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26391641340547501246565351 39587462010821251869848027)
  ·
    refine ⟨59381193016231877804772041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39587462010821251869848027 59381193016231877804772041)
    ·
      refine ⟨44535894762173908353579031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59381193016231877804772041 44535894762173908353579031)
      ·
        refine ⟨66803842143260862530368547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44535894762173908353579031 66803842143260862530368547)
        ·
          refine ⟨100205763214891293795552821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66803842143260862530368547 100205763214891293795552821)
          ·
            refine ⟨9394290301396058793333077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100205763214891293795552821 9394290301396058793333077)
            ·
              refine ⟨27522334867371265996093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9394290301396058793333077 27522334867371265996093)
              ·
                rfl

theorem cell21_1085391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 10].length) (baseStart_1085391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085391 prefixEnd_1085391 := by exact prefixLift 1085391
  have htrace : WordTrace (prefixWord ++ tailWord_1085391) baseStart_1085391 baseEnd_1085391 := by
    simpa [prefixWord, tailWord_1085391, baseEnd_1085391] using wordTrace_append hprefix tailTrace_1085391
  have hstable : (prefixWord ++ tailWord_1085391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085391).length < 2 ^ (prefixWord ++ tailWord_1085391).sum := by decide
  have hdescent : baseEnd_1085391 < baseStart_1085391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085411 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 4]
def baseStart_1085411 : Nat := 118140960795 + 1085411 * 2 ^ 59
def prefixEnd_1085411 : Nat := 4983230072969 + 3 ^ 40 * 1085411 * 2
def baseEnd_1085411 : Nat := 247705578078825803631463

theorem tailTrace_1085411 : CollatzResearch.WordTrace tailWord_1085411 prefixEnd_1085411 247705578078825803631463 := by
  unfold tailWord_1085411
  simp only [CollatzResearch.WordTrace]
  refine ⟨39588191470748795285576087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26392127647165863523717391 39588191470748795285576087)
  ·
    refine ⟨59382287206123192928364131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39588191470748795285576087 59382287206123192928364131)
    ·
      refine ⟨89073430809184789392546197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59382287206123192928364131 89073430809184789392546197)
      ·
        refine ⟨4175317069180537002775603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89073430809184789392546197 4175317069180537002775603)
        ·
          refine ⟨6262975603770805504163405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175317069180537002775603 6262975603770805504163405)
          ·
            refine ⟨2348615851414052064061277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6262975603770805504163405 2348615851414052064061277)
            ·
              refine ⟨880730944280269524022979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2348615851414052064061277 880730944280269524022979)
              ·
                refine ⟨1321096416420404286034469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880730944280269524022979 1321096416420404286034469)
                ·
                  refine ⟨247705578078825803631463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321096416420404286034469 247705578078825803631463)
                  ·
                    rfl

theorem cell21_1085411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 4].length) (baseStart_1085411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085411 prefixEnd_1085411 := by exact prefixLift 1085411
  have htrace : WordTrace (prefixWord ++ tailWord_1085411) baseStart_1085411 baseEnd_1085411 := by
    simpa [prefixWord, tailWord_1085411, baseEnd_1085411] using wordTrace_append hprefix tailTrace_1085411
  have hstable : (prefixWord ++ tailWord_1085411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085411).length < 2 ^ (prefixWord ++ tailWord_1085411).sum := by decide
  have hdescent : baseEnd_1085411 < baseStart_1085411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085515 : List Nat := [1, 1, 1, 1, 3, 1, 2, 8, 3]
def baseStart_1085515 : Nat := 118140960795 + 1085515 * 2 ^ 59
def prefixEnd_1085515 : Nat := 4983230072969 + 3 ^ 40 * 1085515 * 2
def baseEnd_1085515 : Nat := 247729312295744733897917

theorem tailTrace_1085515 : CollatzResearch.WordTrace tailWord_1085515 prefixEnd_1085515 247729312295744733897917 := by
  unfold tailWord_1085515
  simp only [CollatzResearch.WordTrace]
  refine ⟨39591984662372021047361999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26394656441581347364907999 39591984662372021047361999)
  ·
    refine ⟨59387976993558031571042999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39591984662372021047361999 59387976993558031571042999)
    ·
      refine ⟨89081965490337047356564499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59387976993558031571042999 89081965490337047356564499)
      ·
        refine ⟨133622948235505571034846749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89081965490337047356564499 133622948235505571034846749)
        ·
          refine ⟨50108605588314589138067531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133622948235505571034846749 50108605588314589138067531)
          ·
            refine ⟨75162908382471883707101297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50108605588314589138067531 75162908382471883707101297)
            ·
              refine ⟨56372181286853912780325973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75162908382471883707101297 56372181286853912780325973)
              ·
                refine ⟨660611499455319290394445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 56372181286853912780325973 660611499455319290394445)
                ·
                  refine ⟨247729312295744733897917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660611499455319290394445 247729312295744733897917)
                  ·
                    rfl

theorem cell21_1085515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 3].length) (baseStart_1085515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085515 prefixEnd_1085515 := by exact prefixLift 1085515
  have htrace : WordTrace (prefixWord ++ tailWord_1085515) baseStart_1085515 baseEnd_1085515 := by
    simpa [prefixWord, tailWord_1085515, baseEnd_1085515] using wordTrace_append hprefix tailTrace_1085515
  have hstable : (prefixWord ++ tailWord_1085515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085515).length < 2 ^ (prefixWord ++ tailWord_1085515).sum := by decide
  have hdescent : baseEnd_1085515 < baseStart_1085515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085529 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 4]
def baseStart_1085529 : Nat := 118140960795 + 1085529 * 2 ^ 59
def prefixEnd_1085529 : Nat := 4983230072969 + 3 ^ 40 * 1085529 * 2
def baseEnd_1085529 : Nat := 247732507286483820664555

theorem tailTrace_1085529 : CollatzResearch.WordTrace tailWord_1085529 prefixEnd_1085529 247732507286483820664555 := by
  unfold tailWord_1085529
  simp only [CollatzResearch.WordTrace]
  refine ⟨39592495284321301438371641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26394996856214200958914427 39592495284321301438371641)
  ·
    refine ⟨29694371463240976078778731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39592495284321301438371641 29694371463240976078778731)
    ·
      refine ⟨44541557194861464118168097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29694371463240976078778731 44541557194861464118168097)
      ·
        refine ⟨33406167896146098088626073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44541557194861464118168097 33406167896146098088626073)
        ·
          refine ⟨25054625922109573566469555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33406167896146098088626073 25054625922109573566469555)
          ·
            refine ⟨37581938883164360349704333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25054625922109573566469555 37581938883164360349704333)
            ·
              refine ⟨14093227081186635131139125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37581938883164360349704333 14093227081186635131139125)
              ·
                refine ⟨1321240038861247043544293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14093227081186635131139125 1321240038861247043544293)
                ·
                  refine ⟨247732507286483820664555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321240038861247043544293 247732507286483820664555)
                  ·
                    rfl

theorem cell21_1085529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_1085529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085529 prefixEnd_1085529 := by exact prefixLift 1085529
  have htrace : WordTrace (prefixWord ++ tailWord_1085529) baseStart_1085529 baseEnd_1085529 := by
    simpa [prefixWord, tailWord_1085529, baseEnd_1085529] using wordTrace_append hprefix tailTrace_1085529
  have hstable : (prefixWord ++ tailWord_1085529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085529).length < 2 ^ (prefixWord ++ tailWord_1085529).sum := by decide
  have hdescent : baseEnd_1085529 < baseStart_1085529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085594 : List Nat := [3, 1, 1, 5, 2, 2, 2, 5]
def baseStart_1085594 : Nat := 118140960795 + 1085594 * 2 ^ 59
def prefixEnd_1085594 : Nat := 4983230072969 + 3 ^ 40 * 1085594 * 2
def baseEnd_1085594 : Nat := 82582447057352717360363

theorem tailTrace_1085594 : CollatzResearch.WordTrace tailWord_1085594 prefixEnd_1085594 82582447057352717360363 := by
  unfold tailWord_1085594
  simp only [CollatzResearch.WordTrace]
  refine ⟨9898716507271454384871959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26396577352723878359658557 9898716507271454384871959)
  ·
    refine ⟨14848074760907181577307939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9898716507271454384871959 14848074760907181577307939)
    ·
      refine ⟨22272112141360772365961909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14848074760907181577307939 22272112141360772365961909)
      ·
        refine ⟨2088010513252572409308929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22272112141360772365961909 2088010513252572409308929)
        ·
          refine ⟨1566007884939429306981697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088010513252572409308929 1566007884939429306981697)
          ·
            refine ⟨1174505913704571980236273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566007884939429306981697 1174505913704571980236273)
            ·
              refine ⟨880879435278428985177205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174505913704571980236273 880879435278428985177205)
              ·
                refine ⟨82582447057352717360363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 880879435278428985177205 82582447057352717360363)
                ·
                  rfl

theorem cell21_1085594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_1085594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085594 prefixEnd_1085594 := by exact prefixLift 1085594
  have htrace : WordTrace (prefixWord ++ tailWord_1085594) baseStart_1085594 baseEnd_1085594 := by
    simpa [prefixWord, tailWord_1085594, baseEnd_1085594] using wordTrace_append hprefix tailTrace_1085594
  have hstable : (prefixWord ++ tailWord_1085594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085594).length < 2 ^ (prefixWord ++ tailWord_1085594).sum := by decide
  have hdescent : baseEnd_1085594 < baseStart_1085594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085636 : List Nat := [2, 3, 3, 1, 2, 1, 1, 8]
def baseStart_1085636 : Nat := 118140960795 + 1085636 * 2 ^ 59
def prefixEnd_1085636 : Nat := 4983230072969 + 3 ^ 40 * 1085636 * 2
def baseEnd_1085636 : Nat := 82585642048091804127001

theorem tailTrace_1085636 : CollatzResearch.WordTrace tailWord_1085636 prefixEnd_1085636 82585642048091804127001 := by
  unfold tailWord_1085636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19798198947466829356258381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26397598596622439141677841 19798198947466829356258381)
  ·
    refine ⟨7424324605300061008596893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19798198947466829356258381 7424324605300061008596893)
    ·
      refine ⟨2784121726987522878223835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7424324605300061008596893 2784121726987522878223835)
      ·
        refine ⟨4176182590481284317335753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784121726987522878223835 4176182590481284317335753)
        ·
          refine ⟨3132136942860963238001815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4176182590481284317335753 3132136942860963238001815)
          ·
            refine ⟨4698205414291444857002723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132136942860963238001815 4698205414291444857002723)
            ·
              refine ⟨7047308121437167285504085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4698205414291444857002723 7047308121437167285504085)
              ·
                refine ⟨82585642048091804127001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7047308121437167285504085 82585642048091804127001)
                ·
                  rfl

theorem cell21_1085636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_1085636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085636 prefixEnd_1085636 := by exact prefixLift 1085636
  have htrace : WordTrace (prefixWord ++ tailWord_1085636) baseStart_1085636 baseEnd_1085636 := by
    simpa [prefixWord, tailWord_1085636, baseEnd_1085636] using wordTrace_append hprefix tailTrace_1085636
  have hstable : (prefixWord ++ tailWord_1085636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085636).length < 2 ^ (prefixWord ++ tailWord_1085636).sum := by decide
  have hdescent : baseEnd_1085636 < baseStart_1085636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085681 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 4]
def baseStart_1085681 : Nat := 118140960795 + 1085681 * 2 ^ 59
def prefixEnd_1085681 : Nat := 4983230072969 + 3 ^ 40 * 1085681 * 2
def baseEnd_1085681 : Nat := 247767195757365334130911

theorem tailTrace_1085681 : CollatzResearch.WordTrace tailWord_1085681 prefixEnd_1085681 247767195757365334130911 := by
  unfold tailWord_1085681
  simp only [CollatzResearch.WordTrace]
  refine ⟨39598039179770631397904897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26398692786513754265269931 39598039179770631397904897)
  ·
    refine ⟨29698529384827973548428673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39598039179770631397904897 29698529384827973548428673)
    ·
      refine ⟨22273897038620980161321505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29698529384827973548428673 22273897038620980161321505)
      ·
        refine ⟨16705422778965735120991129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22273897038620980161321505 16705422778965735120991129)
        ·
          refine ⟨12529067084224301340743347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16705422778965735120991129 12529067084224301340743347)
          ·
            refine ⟨18793600626336452011115021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12529067084224301340743347 18793600626336452011115021)
            ·
              refine ⟨7047600234876169504168133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18793600626336452011115021 7047600234876169504168133)
              ·
                refine ⟨1321425044039281782031525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7047600234876169504168133 1321425044039281782031525)
                ·
                  refine ⟨247767195757365334130911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321425044039281782031525 247767195757365334130911)
                  ·
                    rfl

theorem cell21_1085681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_1085681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085681 prefixEnd_1085681 := by exact prefixLift 1085681
  have htrace : WordTrace (prefixWord ++ tailWord_1085681) baseStart_1085681 baseEnd_1085681 := by
    simpa [prefixWord, tailWord_1085681, baseEnd_1085681] using wordTrace_append hprefix tailTrace_1085681
  have hstable : (prefixWord ++ tailWord_1085681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085681).length < 2 ^ (prefixWord ++ tailWord_1085681).sum := by decide
  have hdescent : baseEnd_1085681 < baseStart_1085681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085743 : List Nat := [1, 1, 2, 1, 2, 1, 6, 4, 3]
def baseStart_1085743 : Nat := 118140960795 + 1085743 * 2 ^ 59
def prefixEnd_1085743 : Nat := 4983230072969 + 3 ^ 40 * 1085743 * 2
def baseEnd_1085743 : Nat := 247781345002067004097451

theorem tailTrace_1085743 : CollatzResearch.WordTrace tailWord_1085743 prefixEnd_1085743 247781345002067004097451 := by
  unfold tailWord_1085743
  simp only [CollatzResearch.WordTrace]
  refine ⟨39600300505546015986661883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26400200337030677324441255 39600300505546015986661883)
  ·
    refine ⟨59400450758319023979992825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39600300505546015986661883 59400450758319023979992825)
    ·
      refine ⟨44550338068739267984994619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59400450758319023979992825 44550338068739267984994619)
      ·
        refine ⟨66825507103108901977491929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44550338068739267984994619 66825507103108901977491929)
        ·
          refine ⟨50119130327331676483118947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66825507103108901977491929 50119130327331676483118947)
          ·
            refine ⟨75178695490997514724678421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50119130327331676483118947 75178695490997514724678421)
            ·
              refine ⟨3524001351140508502719301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75178695490997514724678421 3524001351140508502719301)
              ·
                refine ⟨660750253338845344259869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3524001351140508502719301 660750253338845344259869)
                ·
                  refine ⟨247781345002067004097451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660750253338845344259869 247781345002067004097451)
                  ·
                    rfl

theorem cell21_1085743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 3].length) (baseStart_1085743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085743 prefixEnd_1085743 := by exact prefixLift 1085743
  have htrace : WordTrace (prefixWord ++ tailWord_1085743) baseStart_1085743 baseEnd_1085743 := by
    simpa [prefixWord, tailWord_1085743, baseEnd_1085743] using wordTrace_append hprefix tailTrace_1085743
  have hstable : (prefixWord ++ tailWord_1085743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085743).length < 2 ^ (prefixWord ++ tailWord_1085743).sum := by decide
  have hdescent : baseEnd_1085743 < baseStart_1085743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085850 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_1085850 : Nat := 118140960795 + 1085850 * 2 ^ 59
def prefixEnd_1085850 : Nat := 4983230072969 + 3 ^ 40 * 1085850 * 2
def baseEnd_1085850 : Nat := 247805763859858595813899

theorem tailTrace_1085850 : CollatzResearch.WordTrace tailWord_1085850 prefixEnd_1085850 247805763859858595813899 := by
  unfold tailWord_1085850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9901050779039593315201751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26402802077438915507204669 9901050779039593315201751)
  ·
    refine ⟨14851576168559389972802627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9901050779039593315201751 14851576168559389972802627)
    ·
      refine ⟨22277364252839084959203941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14851576168559389972802627 22277364252839084959203941)
      ·
        refine ⟨4177005797407328429850739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22277364252839084959203941 4177005797407328429850739)
        ·
          refine ⟨6265508696110992644776109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177005797407328429850739 6265508696110992644776109)
          ·
            refine ⟨2349565761041622241791041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6265508696110992644776109 2349565761041622241791041)
            ·
              refine ⟨1762174320781216681343281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349565761041622241791041 1762174320781216681343281)
              ·
                refine ⟨1321630740585912511007461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762174320781216681343281 1321630740585912511007461)
                ·
                  refine ⟨247805763859858595813899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321630740585912511007461 247805763859858595813899)
                  ·
                    rfl

theorem cell21_1085850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_1085850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085850 prefixEnd_1085850 := by exact prefixLift 1085850
  have htrace : WordTrace (prefixWord ++ tailWord_1085850) baseStart_1085850 baseEnd_1085850 := by
    simpa [prefixWord, tailWord_1085850, baseEnd_1085850] using wordTrace_append hprefix tailTrace_1085850
  have hstable : (prefixWord ++ tailWord_1085850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085850).length < 2 ^ (prefixWord ++ tailWord_1085850).sum := by decide
  have hdescent : baseEnd_1085850 < baseStart_1085850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085895 : List Nat := [1, 1, 4, 1, 1, 4, 1, 5, 3]
def baseStart_1085895 : Nat := 118140960795 + 1085895 * 2 ^ 59
def prefixEnd_1085895 : Nat := 4983230072969 + 3 ^ 40 * 1085895 * 2
def baseEnd_1085895 : Nat := 247816033472948517563807

theorem tailTrace_1085895 : CollatzResearch.WordTrace tailWord_1085895 prefixEnd_1085895 247816033472948517563807 := by
  unfold tailWord_1085895
  simp only [CollatzResearch.WordTrace]
  refine ⟨39605844400995345946195139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26403896267330230630796759 39605844400995345946195139)
  ·
    refine ⟨59408766601493018919292709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39605844400995345946195139 59408766601493018919292709)
    ·
      refine ⟨11139143737779941047367383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59408766601493018919292709 11139143737779941047367383)
      ·
        refine ⟨16708715606669911571051075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11139143737779941047367383 16708715606669911571051075)
        ·
          refine ⟨25063073410004867356576613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16708715606669911571051075 25063073410004867356576613)
          ·
            refine ⟨4699326264375912629358115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25063073410004867356576613 4699326264375912629358115)
            ·
              refine ⟨7048989396563868944037173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699326264375912629358115 7048989396563868944037173)
              ·
                refine ⟨660842755927862713503485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7048989396563868944037173 660842755927862713503485)
                ·
                  refine ⟨247816033472948517563807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660842755927862713503485 247816033472948517563807)
                  ·
                    rfl

theorem cell21_1085895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 3].length) (baseStart_1085895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085895 prefixEnd_1085895 := by exact prefixLift 1085895
  have htrace : WordTrace (prefixWord ++ tailWord_1085895) baseStart_1085895 baseEnd_1085895 := by
    simpa [prefixWord, tailWord_1085895, baseEnd_1085895] using wordTrace_append hprefix tailTrace_1085895
  have hstable : (prefixWord ++ tailWord_1085895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085895).length < 2 ^ (prefixWord ++ tailWord_1085895).sum := by decide
  have hdescent : baseEnd_1085895 < baseStart_1085895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085909 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 6]
def baseStart_1085909 : Nat := 118140960795 + 1085909 * 2 ^ 59
def prefixEnd_1085909 : Nat := 4983230072969 + 3 ^ 40 * 1085909 * 2
def baseEnd_1085909 : Nat := 247819228463687604330445

theorem tailTrace_1085909 : CollatzResearch.WordTrace tailWord_1085909 prefixEnd_1085909 247819228463687604330445 := by
  unfold tailWord_1085909
  simp only [CollatzResearch.WordTrace]
  refine ⟨39606355022944626337204781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26404236681963084224803187 39606355022944626337204781)
  ·
    refine ⟨14852383133604234876451793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39606355022944626337204781 14852383133604234876451793)
    ·
      refine ⟨11139287350203176157338845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14852383133604234876451793 11139287350203176157338845)
      ·
        refine ⟨4177232756326191059002067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11139287350203176157338845 4177232756326191059002067)
        ·
          refine ⟨6265849134489286588503101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177232756326191059002067 6265849134489286588503101)
          ·
            refine ⟨2349693425433482470688663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6265849134489286588503101 2349693425433482470688663)
            ·
              refine ⟨3524540138150223706032995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349693425433482470688663 3524540138150223706032995)
              ·
                refine ⟨5286810207225335559049493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524540138150223706032995 5286810207225335559049493)
                ·
                  refine ⟨247819228463687604330445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5286810207225335559049493 247819228463687604330445)
                  ·
                    rfl

theorem cell21_1085909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_1085909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085909 prefixEnd_1085909 := by exact prefixLift 1085909
  have htrace : WordTrace (prefixWord ++ tailWord_1085909) baseStart_1085909 baseEnd_1085909 := by
    simpa [prefixWord, tailWord_1085909, baseEnd_1085909] using wordTrace_append hprefix tailTrace_1085909
  have hstable : (prefixWord ++ tailWord_1085909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085909).length < 2 ^ (prefixWord ++ tailWord_1085909).sum := by decide
  have hdescent : baseEnd_1085909 < baseStart_1085909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085985 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 4]
def baseStart_1085985 : Nat := 118140960795 + 1085985 * 2 ^ 59
def prefixEnd_1085985 : Nat := 4983230072969 + 3 ^ 40 * 1085985 * 2
def baseEnd_1085985 : Nat := 247836572699128361063623

theorem tailTrace_1085985 : CollatzResearch.WordTrace tailWord_1085985 prefixEnd_1085985 247836572699128361063623 := by
  unfold tailWord_1085985
  simp only [CollatzResearch.WordTrace]
  refine ⟨39609126970669291316971409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26406084647112860877980939 39609126970669291316971409)
  ·
    refine ⟨29706845228001968487728557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39609126970669291316971409 29706845228001968487728557)
    ·
      refine ⟨11140066960500738182898209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29706845228001968487728557 11140066960500738182898209)
      ·
        refine ⟨8355050220375553637173657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11140066960500738182898209 8355050220375553637173657)
        ·
          refine ⟨6266287665281665227880243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8355050220375553637173657 6266287665281665227880243)
          ·
            refine ⟨9399431497922497841820365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266287665281665227880243 9399431497922497841820365)
            ·
              refine ⟨3524786811720936690682637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9399431497922497841820365 3524786811720936690682637)
              ·
                refine ⟨1321795054395351259005989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3524786811720936690682637 1321795054395351259005989)
                ·
                  refine ⟨247836572699128361063623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321795054395351259005989 247836572699128361063623)
                  ·
                    rfl

theorem cell21_1085985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_1085985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1085985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1085985 prefixEnd_1085985 := by exact prefixLift 1085985
  have htrace : WordTrace (prefixWord ++ tailWord_1085985) baseStart_1085985 baseEnd_1085985 := by
    simpa [prefixWord, tailWord_1085985, baseEnd_1085985] using wordTrace_append hprefix tailTrace_1085985
  have hstable : (prefixWord ++ tailWord_1085985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085985).length < 2 ^ (prefixWord ++ tailWord_1085985).sum := by decide
  have hdescent : baseEnd_1085985 < baseStart_1085985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086022 : List Nat := [6, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1086022 : Nat := 118140960795 + 1086022 * 2 ^ 59
def prefixEnd_1086022 : Nat := 4983230072969 + 3 ^ 40 * 1086022 * 2
def baseEnd_1086022 : Nat := 247845016603224518946881

theorem tailTrace_1086022 : CollatzResearch.WordTrace tailWord_1086022 prefixEnd_1086022 247845016603224518946881 := by
  unfold tailWord_1086022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237827389735476457377135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26406984314356831090712213 1237827389735476457377135)
  ·
    refine ⟨1856741084603214686065703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1237827389735476457377135 1856741084603214686065703)
    ·
      refine ⟨2785111626904822029098555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856741084603214686065703 2785111626904822029098555)
      ·
        refine ⟨4177667440357233043647833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785111626904822029098555 4177667440357233043647833)
        ·
          refine ⟨3133250580267924782735875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4177667440357233043647833 3133250580267924782735875)
          ·
            refine ⟨4699875870401887174103813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133250580267924782735875 4699875870401887174103813)
            ·
              refine ⟨881226725700353845144465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4699875870401887174103813 881226725700353845144465)
              ·
                refine ⟨660920044275265383858349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881226725700353845144465 660920044275265383858349)
                ·
                  refine ⟨247845016603224518946881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660920044275265383858349 247845016603224518946881)
                  ·
                    rfl

theorem cell21_1086022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1086022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086022 prefixEnd_1086022 := by exact prefixLift 1086022
  have htrace : WordTrace (prefixWord ++ tailWord_1086022) baseStart_1086022 baseEnd_1086022 := by
    simpa [prefixWord, tailWord_1086022, baseEnd_1086022] using wordTrace_append hprefix tailTrace_1086022
  have hstable : (prefixWord ++ tailWord_1086022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086022).length < 2 ^ (prefixWord ++ tailWord_1086022).sum := by decide
  have hdescent : baseEnd_1086022 < baseStart_1086022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086050 : List Nat := [3, 3, 2, 3, 1, 1, 3, 5]
def baseStart_1086050 : Nat := 118140960795 + 1086050 * 2 ^ 59
def prefixEnd_1086050 : Nat := 4983230072969 + 3 ^ 40 * 1086050 * 2
def baseEnd_1086050 : Nat := 82617135528234230826719

theorem tailTrace_1086050 : CollatzResearch.WordTrace tailWord_1086050 prefixEnd_1086050 82617135528234230826719 := by
  unfold tailWord_1086050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9902874428858451854521901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26407665143622538278725069 9902874428858451854521901)
  ·
    refine ⟨3713577910821919445445713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9902874428858451854521901 3713577910821919445445713)
    ·
      refine ⟨2785183433116439584084285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3713577910821919445445713 2785183433116439584084285)
      ·
        refine ⟨1044443787418664844031607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2785183433116439584084285 1044443787418664844031607)
        ·
          refine ⟨1566665681127997266047411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044443787418664844031607 1566665681127997266047411)
          ·
            refine ⟨2349998521691995899071117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566665681127997266047411 2349998521691995899071117)
            ·
              refine ⟨881249445634498462151669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2349998521691995899071117 881249445634498462151669)
              ·
                refine ⟨82617135528234230826719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 881249445634498462151669 82617135528234230826719)
                ·
                  rfl

theorem cell21_1086050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_1086050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086050 prefixEnd_1086050 := by exact prefixLift 1086050
  have htrace : WordTrace (prefixWord ++ tailWord_1086050) baseStart_1086050 baseEnd_1086050 := by
    simpa [prefixWord, tailWord_1086050, baseEnd_1086050] using wordTrace_append hprefix tailTrace_1086050
  have hstable : (prefixWord ++ tailWord_1086050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086050).length < 2 ^ (prefixWord ++ tailWord_1086050).sum := by decide
  have hdescent : baseEnd_1086050 < baseStart_1086050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086064 : List Nat := [2, 1, 1, 1, 7, 1, 2, 3, 3]
def baseStart_1086064 : Nat := 118140960795 + 1086064 * 2 ^ 59
def prefixEnd_1086064 : Nat := 4983230072969 + 3 ^ 40 * 1086064 * 2
def baseEnd_1086064 : Nat := 247854601575441779246795

theorem tailTrace_1086064 : CollatzResearch.WordTrace tailWord_1086064 prefixEnd_1086064 247854601575441779246795 := by
  unfold tailWord_1086064
  simp only [CollatzResearch.WordTrace]
  refine ⟨19806004168691543904548623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26408005558255391872731497 19806004168691543904548623)
  ·
    refine ⟨29709006253037315856822935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19806004168691543904548623 29709006253037315856822935)
    ·
      refine ⟨44563509379555973785234403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29709006253037315856822935 44563509379555973785234403)
      ·
        refine ⟨66845264069333960677851605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44563509379555973785234403 66845264069333960677851605)
        ·
          refine ⟨1566685876625014703387147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66845264069333960677851605 1566685876625014703387147)
          ·
            refine ⟨2350028814937522055080721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566685876625014703387147 2350028814937522055080721)
            ·
              refine ⟨1762521611203141541310541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350028814937522055080721 1762521611203141541310541)
              ·
                refine ⟨660945604201178077991453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1762521611203141541310541 660945604201178077991453)
                ·
                  refine ⟨247854601575441779246795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660945604201178077991453 247854601575441779246795)
                  ·
                    rfl

theorem cell21_1086064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_1086064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086064 prefixEnd_1086064 := by exact prefixLift 1086064
  have htrace : WordTrace (prefixWord ++ tailWord_1086064) baseStart_1086064 baseEnd_1086064 := by
    simpa [prefixWord, tailWord_1086064, baseEnd_1086064] using wordTrace_append hprefix tailTrace_1086064
  have hstable : (prefixWord ++ tailWord_1086064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086064).length < 2 ^ (prefixWord ++ tailWord_1086064).sum := by decide
  have hdescent : baseEnd_1086064 < baseStart_1086064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086140 : List Nat := [2, 2, 2, 3, 1, 1, 5, 2, 3]
def baseStart_1086140 : Nat := 118140960795 + 1086140 * 2 ^ 59
def prefixEnd_1086140 : Nat := 4983230072969 + 3 ^ 40 * 1086140 * 2
def baseEnd_1086140 : Nat := 247871945810882535979973

theorem tailTrace_1086140 : CollatzResearch.WordTrace tailWord_1086140 prefixEnd_1086140 247871945810882535979973 := by
  unfold tailWord_1086140
  simp only [CollatzResearch.WordTrace]
  refine ⟨19807390142553876394431937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26409853523405168525909249 19807390142553876394431937)
  ·
    refine ⟨14855542606915407295823953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19807390142553876394431937 14855542606915407295823953)
    ·
      refine ⟨11141656955186555471867965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14855542606915407295823953 11141656955186555471867965)
      ·
        refine ⟨4178121358194958301950487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11141656955186555471867965 4178121358194958301950487)
        ·
          refine ⟨6267182037292437452925731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178121358194958301950487 6267182037292437452925731)
          ·
            refine ⟨9400773055938656179388597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267182037292437452925731 9400773055938656179388597)
            ·
              refine ⟨881322473994249016817681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9400773055938656179388597 881322473994249016817681)
              ·
                refine ⟨660991855495686762613261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881322473994249016817681 660991855495686762613261)
                ·
                  refine ⟨247871945810882535979973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660991855495686762613261 247871945810882535979973)
                  ·
                    rfl

theorem cell21_1086140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_1086140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086140 prefixEnd_1086140 := by exact prefixLift 1086140
  have htrace : WordTrace (prefixWord ++ tailWord_1086140) baseStart_1086140 baseEnd_1086140 := by
    simpa [prefixWord, tailWord_1086140, baseEnd_1086140] using wordTrace_append hprefix tailTrace_1086140
  have hstable : (prefixWord ++ tailWord_1086140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086140).length < 2 ^ (prefixWord ++ tailWord_1086140).sum := by decide
  have hdescent : baseEnd_1086140 < baseStart_1086140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086154 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_1086154 : Nat := 118140960795 + 1086154 * 2 ^ 59
def prefixEnd_1086154 : Nat := 4983230072969 + 3 ^ 40 * 1086154 * 2
def baseEnd_1086154 : Nat := 247875140801621622746611

theorem tailTrace_1086154 : CollatzResearch.WordTrace tailWord_1086154 prefixEnd_1086154 247875140801621622746611 := by
  unfold tailWord_1086154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903822726764258294968379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26410193938038022119915677 9903822726764258294968379)
  ·
    refine ⟨14855734090146387442452569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903822726764258294968379 14855734090146387442452569)
    ·
      refine ⟨11141800567609790581839427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14855734090146387442452569 11141800567609790581839427)
      ·
        refine ⟨16712700851414685872759141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11141800567609790581839427 16712700851414685872759141)
        ·
          refine ⟨3133631409640253601142339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16712700851414685872759141 3133631409640253601142339)
          ·
            refine ⟨4700447114460380401713509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133631409640253601142339 4700447114460380401713509)
            ·
              refine ⟨881333833961321325321283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4700447114460380401713509 881333833961321325321283)
              ·
                refine ⟨1322000750941981987981925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881333833961321325321283 1322000750941981987981925)
                ·
                  refine ⟨247875140801621622746611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322000750941981987981925 247875140801621622746611)
                  ·
                    rfl

theorem cell21_1086154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_1086154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086154 prefixEnd_1086154 := by exact prefixLift 1086154
  have htrace : WordTrace (prefixWord ++ tailWord_1086154) baseStart_1086154 baseEnd_1086154 := by
    simpa [prefixWord, tailWord_1086154, baseEnd_1086154] using wordTrace_append hprefix tailTrace_1086154
  have hstable : (prefixWord ++ tailWord_1086154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086154).length < 2 ^ (prefixWord ++ tailWord_1086154).sum := by decide
  have hdescent : baseEnd_1086154 < baseStart_1086154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086227 : List Nat := [1, 1, 1, 2, 1, 3, 7, 5]
def baseStart_1086227 : Nat := 118140960795 + 1086227 * 2 ^ 59
def prefixEnd_1086227 : Nat := 4983230072969 + 3 ^ 40 * 1086227 * 2
def baseEnd_1086227 : Nat := 82630600132063239343265

theorem tailTrace_1086227 : CollatzResearch.WordTrace tailWord_1086227 prefixEnd_1086227 82630600132063239343265 := by
  unfold tailWord_1086227
  simp only [CollatzResearch.WordTrace]
  refine ⟨39617953435792566647280935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26411968957195044431520623 39617953435792566647280935)
  ·
    refine ⟨59426930153688849970921403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39617953435792566647280935 59426930153688849970921403)
    ·
      refine ⟨89140395230533274956382105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59426930153688849970921403 89140395230533274956382105)
      ·
        refine ⟨66855296422899956217286579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89140395230533274956382105 66855296422899956217286579)
        ·
          refine ⟨100282944634349934325929869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66855296422899956217286579 100282944634349934325929869)
          ·
            refine ⟨37606104237881225372223701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100282944634349934325929869 37606104237881225372223701)
            ·
              refine ⟨881393068075341219661493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37606104237881225372223701 881393068075341219661493)
              ·
                refine ⟨82630600132063239343265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 881393068075341219661493 82630600132063239343265)
                ·
                  rfl

theorem cell21_1086227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 5].length) (baseStart_1086227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086227 prefixEnd_1086227 := by exact prefixLift 1086227
  have htrace : WordTrace (prefixWord ++ tailWord_1086227) baseStart_1086227 baseEnd_1086227 := by
    simpa [prefixWord, tailWord_1086227, baseEnd_1086227] using wordTrace_append hprefix tailTrace_1086227
  have hstable : (prefixWord ++ tailWord_1086227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086227).length < 2 ^ (prefixWord ++ tailWord_1086227).sum := by decide
  have hdescent : baseEnd_1086227 < baseStart_1086227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086241 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 7]
def baseStart_1086241 : Nat := 118140960795 + 1086241 * 2 ^ 59
def prefixEnd_1086241 : Nat := 4983230072969 + 3 ^ 40 * 1086241 * 2
def baseEnd_1086241 : Nat := 247894995386928804796433

theorem tailTrace_1086241 : CollatzResearch.WordTrace tailWord_1086241 prefixEnd_1086241 247894995386928804796433 := by
  unfold tailWord_1086241
  simp only [CollatzResearch.WordTrace]
  refine ⟨39618464057741847038290577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26412309371827898025527051 39618464057741847038290577)
  ·
    refine ⟨29713848043306385278717933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39618464057741847038290577 29713848043306385278717933)
    ·
      refine ⟨11142693016239894479519225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29713848043306385278717933 11142693016239894479519225)
      ·
        refine ⟨8357019762179920859639419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11142693016239894479519225 8357019762179920859639419)
        ·
          refine ⟨12535529643269881289459129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8357019762179920859639419 12535529643269881289459129)
          ·
            refine ⟨9401647232452410967094347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12535529643269881289459129 9401647232452410967094347)
            ·
              refine ⟨14102470848678616450641521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9401647232452410967094347 14102470848678616450641521)
              ·
                refine ⟨10576853136508962337981141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14102470848678616450641521 10576853136508962337981141)
                ·
                  refine ⟨247894995386928804796433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10576853136508962337981141 247894995386928804796433)
                  ·
                    rfl

theorem cell21_1086241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_1086241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086241 prefixEnd_1086241 := by exact prefixLift 1086241
  have htrace : WordTrace (prefixWord ++ tailWord_1086241) baseStart_1086241 baseEnd_1086241 := by
    simpa [prefixWord, tailWord_1086241, baseEnd_1086241] using wordTrace_append hprefix tailTrace_1086241
  have hstable : (prefixWord ++ tailWord_1086241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086241).length < 2 ^ (prefixWord ++ tailWord_1086241).sum := by decide
  have hdescent : baseEnd_1086241 < baseStart_1086241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086258 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1086258 : Nat := 118140960795 + 1086258 * 2 ^ 59
def prefixEnd_1086258 : Nat := 4983230072969 + 3 ^ 40 * 1086258 * 2
def baseEnd_1086258 : Nat := 247898875018540553013065

theorem tailTrace_1086258 : CollatzResearch.WordTrace tailWord_1086258 prefixEnd_1086258 247898875018540553013065 := by
  unfold tailWord_1086258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9904771024670064735414857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26412722732453505961106285 9904771024670064735414857)
  ·
    refine ⟨7428578268502548551561143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9904771024670064735414857 7428578268502548551561143)
    ·
      refine ⟨11142867402753822827341715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7428578268502548551561143 11142867402753822827341715)
      ·
        refine ⟨16714301104130734241012573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11142867402753822827341715 16714301104130734241012573)
        ·
          refine ⟨6267862914049025340379715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16714301104130734241012573 6267862914049025340379715)
          ·
            refine ⟨9401794371073538010569573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267862914049025340379715 9401794371073538010569573)
            ·
              refine ⟨1762836444576288376981795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9401794371073538010569573 1762836444576288376981795)
              ·
                refine ⟨2644254666864432565472693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762836444576288376981795 2644254666864432565472693)
                ·
                  refine ⟨247898875018540553013065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2644254666864432565472693 247898875018540553013065)
                  ·
                    rfl

theorem cell21_1086258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1086258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086258 prefixEnd_1086258 := by exact prefixLift 1086258
  have htrace : WordTrace (prefixWord ++ tailWord_1086258) baseStart_1086258 baseEnd_1086258 := by
    simpa [prefixWord, tailWord_1086258, baseEnd_1086258] using wordTrace_append hprefix tailTrace_1086258
  have hstable : (prefixWord ++ tailWord_1086258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086258).length < 2 ^ (prefixWord ++ tailWord_1086258).sum := by decide
  have hdescent : baseEnd_1086258 < baseStart_1086258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086272 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_1086272 : Nat := 118140960795 + 1086272 * 2 ^ 59
def prefixEnd_1086272 : Nat := 4983230072969 + 3 ^ 40 * 1086272 * 2
def baseEnd_1086272 : Nat := 247902070009279639779703

theorem tailTrace_1086272 : CollatzResearch.WordTrace tailWord_1086272 prefixEnd_1086272 247902070009279639779703 := by
  unfold tailWord_1086272
  simp only [CollatzResearch.WordTrace]
  refine ⟨19809797360314769666334535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26413063147086359555112713 19809797360314769666334535)
  ·
    refine ⟨29714696040472154499501803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19809797360314769666334535 29714696040472154499501803)
    ·
      refine ⟨44572044060708231749252705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29714696040472154499501803 44572044060708231749252705)
      ·
        refine ⟨33429033045531173811939529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44572044060708231749252705 33429033045531173811939529)
        ·
          refine ⟨25071774784148380358954647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33429033045531173811939529 25071774784148380358954647)
          ·
            refine ⟨37607662176222570538431971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25071774784148380358954647 37607662176222570538431971)
            ·
              refine ⟨56411493264333855807647957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37607662176222570538431971 56411493264333855807647957)
              ·
                refine ⟨1322144373382824745491749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56411493264333855807647957 1322144373382824745491749)
                ·
                  refine ⟨247902070009279639779703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322144373382824745491749 247902070009279639779703)
                  ·
                    rfl

theorem cell21_1086272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_1086272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086272 prefixEnd_1086272 := by exact prefixLift 1086272
  have htrace : WordTrace (prefixWord ++ tailWord_1086272) baseStart_1086272 baseEnd_1086272 := by
    simpa [prefixWord, tailWord_1086272, baseEnd_1086272] using wordTrace_append hprefix tailTrace_1086272
  have hstable : (prefixWord ++ tailWord_1086272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086272).length < 2 ^ (prefixWord ++ tailWord_1086272).sum := by decide
  have hdescent : baseEnd_1086272 < baseStart_1086272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086362 : List Nat := [3, 1, 1, 4, 12]
def baseStart_1086362 : Nat := 118140960795 + 1086362 * 2 ^ 59
def prefixEnd_1086362 : Nat := 4983230072969 + 3 ^ 40 * 1086362 * 2
def baseEnd_1086362 : Nat := 3060772953524191151599

theorem tailTrace_1086362 : CollatzResearch.WordTrace tailWord_1086362 prefixEnd_1086362 3060772953524191151599 := by
  unfold tailWord_1086362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905719322575871175861335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26415251526868989802296893 9905719322575871175861335)
  ·
    refine ⟨14858578983863806763792003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9905719322575871175861335 14858578983863806763792003)
    ·
      refine ⟨22287868475795710145688005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14858578983863806763792003 22287868475795710145688005)
      ·
        refine ⟨4178975339211695652316501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22287868475795710145688005 4178975339211695652316501)
        ·
          refine ⟨3060772953524191151599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4178975339211695652316501 3060772953524191151599)
          ·
            rfl

theorem cell21_1086362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 12].length) (baseStart_1086362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086362 prefixEnd_1086362 := by exact prefixLift 1086362
  have htrace : WordTrace (prefixWord ++ tailWord_1086362) baseStart_1086362 baseEnd_1086362 := by
    simpa [prefixWord, tailWord_1086362, baseEnd_1086362] using wordTrace_append hprefix tailTrace_1086362
  have hstable : (prefixWord ++ tailWord_1086362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086362).length < 2 ^ (prefixWord ++ tailWord_1086362).sum := by decide
  have hdescent : baseEnd_1086362 < baseStart_1086362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086365 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1086365 : Nat := 118140960795 + 1086365 * 2 ^ 59
def prefixEnd_1086365 : Nat := 4983230072969 + 3 ^ 40 * 1086365 * 2
def baseEnd_1086365 : Nat := 247923293876332144729513

theorem tailTrace_1086365 : CollatzResearch.WordTrace tailWord_1086365 prefixEnd_1086365 247923293876332144729513 := by
  unfold tailWord_1086365
  simp only [CollatzResearch.WordTrace]
  refine ⟨39622986709292616215804549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26415324472861744143869699 39622986709292616215804549)
  ·
    refine ⟨7429310007992365540463353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39622986709292616215804549 7429310007992365540463353)
    ·
      refine ⟨5571982505994274155347515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7429310007992365540463353 5571982505994274155347515)
      ·
        refine ⟨8357973758991411233021273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5571982505994274155347515 8357973758991411233021273)
        ·
          refine ⟨6268480319243558424765955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8357973758991411233021273 6268480319243558424765955)
          ·
            refine ⟨9402720478865337637148933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6268480319243558424765955 9402720478865337637148933)
            ·
              refine ⟨1763010089787250806965425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9402720478865337637148933 1763010089787250806965425)
              ·
                refine ⟨1322257567340438105224069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763010089787250806965425 1322257567340438105224069)
                ·
                  refine ⟨247923293876332144729513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322257567340438105224069 247923293876332144729513)
                  ·
                    rfl

theorem cell21_1086365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1086365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086365 prefixEnd_1086365 := by exact prefixLift 1086365
  have htrace : WordTrace (prefixWord ++ tailWord_1086365) baseStart_1086365 baseEnd_1086365 := by
    simpa [prefixWord, tailWord_1086365, baseEnd_1086365] using wordTrace_append hprefix tailTrace_1086365
  have hstable : (prefixWord ++ tailWord_1086365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086365).length < 2 ^ (prefixWord ++ tailWord_1086365).sum := by decide
  have hdescent : baseEnd_1086365 < baseStart_1086365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086393 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 7]
def baseStart_1086393 : Nat := 118140960795 + 1086393 * 2 ^ 59
def prefixEnd_1086393 : Nat := 4983230072969 + 3 ^ 40 * 1086393 * 2
def baseEnd_1086393 : Nat := 247929683857810318262789

theorem tailTrace_1086393 : CollatzResearch.WordTrace tailWord_1086393 prefixEnd_1086393 247929683857810318262789 := by
  unfold tailWord_1086393
  simp only [CollatzResearch.WordTrace]
  refine ⟨39624007953191176997823833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26416005302127451331882555 39624007953191176997823833)
  ·
    refine ⟨29718005964893382748367875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39624007953191176997823833 29718005964893382748367875)
    ·
      refine ⟨44577008947340074122551813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29718005964893382748367875 44577008947340074122551813)
      ·
        refine ⟨8358189177626263897978465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44577008947340074122551813 8358189177626263897978465)
        ·
          refine ⟨6268641883219697923483849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8358189177626263897978465 6268641883219697923483849)
          ·
            refine ⟨4701481412414773442612887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6268641883219697923483849 4701481412414773442612887)
            ·
              refine ⟨7052222118622160163919331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701481412414773442612887 7052222118622160163919331)
              ·
                refine ⟨10578333177933240245878997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7052222118622160163919331 10578333177933240245878997)
                ·
                  refine ⟨247929683857810318262789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10578333177933240245878997 247929683857810318262789)
                  ·
                    rfl

theorem cell21_1086393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_1086393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086393 prefixEnd_1086393 := by exact prefixLift 1086393
  have htrace : WordTrace (prefixWord ++ tailWord_1086393) baseStart_1086393 baseEnd_1086393 := by
    simpa [prefixWord, tailWord_1086393, baseEnd_1086393] using wordTrace_append hprefix tailTrace_1086393
  have hstable : (prefixWord ++ tailWord_1086393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086393).length < 2 ^ (prefixWord ++ tailWord_1086393).sum := by decide
  have hdescent : baseEnd_1086393 < baseStart_1086393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086424 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_1086424 : Nat := 118140960795 + 1086424 * 2 ^ 59
def prefixEnd_1086424 : Nat := 4983230072969 + 3 ^ 40 * 1086424 * 2
def baseEnd_1086424 : Nat := 247936758480161153246059

theorem tailTrace_1086424 : CollatzResearch.WordTrace tailWord_1086424 prefixEnd_1086424 247936758480161153246059 := by
  unfold tailWord_1086424
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812569308039434646101163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26416759077385912861468217 19812569308039434646101163)
  ·
    refine ⟨29718853962059151969151745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19812569308039434646101163 29718853962059151969151745)
    ·
      refine ⟨22289140471544363976863809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29718853962059151969151745 22289140471544363976863809)
      ·
        refine ⟨16716855353658272982647857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22289140471544363976863809 16716855353658272982647857)
        ·
          refine ⟨12537641515243704736985893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16716855353658272982647857 12537641515243704736985893)
          ·
            refine ⟨2350807784108194638184855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12537641515243704736985893 2350807784108194638184855)
            ·
              refine ⟨3526211676162291957277283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350807784108194638184855 3526211676162291957277283)
              ·
                refine ⟨5289317514243437935915925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526211676162291957277283 5289317514243437935915925)
                ·
                  refine ⟨247936758480161153246059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5289317514243437935915925 247936758480161153246059)
                  ·
                    rfl

theorem cell21_1086424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_1086424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086424 prefixEnd_1086424 := by exact prefixLift 1086424
  have htrace : WordTrace (prefixWord ++ tailWord_1086424) baseStart_1086424 baseEnd_1086424 := by
    simpa [prefixWord, tailWord_1086424, baseEnd_1086424] using wordTrace_append hprefix tailTrace_1086424
  have hstable : (prefixWord ++ tailWord_1086424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086424).length < 2 ^ (prefixWord ++ tailWord_1086424).sum := by decide
  have hdescent : baseEnd_1086424 < baseStart_1086424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086514 : List Nat := [3, 2, 1, 1, 2, 2, 1, 9]
def baseStart_1086514 : Nat := 118140960795 + 1086514 * 2 ^ 59
def prefixEnd_1086514 : Nat := 4983230072969 + 3 ^ 40 * 1086514 * 2
def baseEnd_1086514 : Nat := 82652432568780332248625

theorem tailTrace_1086514 : CollatzResearch.WordTrace tailWord_1086514 prefixEnd_1086514 82652432568780332248625 := by
  unfold tailWord_1086514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907105296438203665744649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26418947457168543108652397 9907105296438203665744649)
  ·
    refine ⟨7430328972328652749308487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9907105296438203665744649 7430328972328652749308487)
    ·
      refine ⟨11145493458492979123962731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7430328972328652749308487 11145493458492979123962731)
      ·
        refine ⟨16718240187739468685944097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11145493458492979123962731 16718240187739468685944097)
        ·
          refine ⟨12538680140804601514458073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16718240187739468685944097 12538680140804601514458073)
          ·
            refine ⟨9404010105603451135843555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12538680140804601514458073 9404010105603451135843555)
            ·
              refine ⟨14106015158405176703765333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9404010105603451135843555 14106015158405176703765333)
              ·
                refine ⟨82652432568780332248625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14106015158405176703765333 82652432568780332248625)
                ·
                  rfl

theorem cell21_1086514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_1086514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086514 prefixEnd_1086514 := by exact prefixLift 1086514
  have htrace : WordTrace (prefixWord ++ tailWord_1086514) baseStart_1086514 baseEnd_1086514 := by
    simpa [prefixWord, tailWord_1086514, baseEnd_1086514] using wordTrace_append hprefix tailTrace_1086514
  have hstable : (prefixWord ++ tailWord_1086514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086514).length < 2 ^ (prefixWord ++ tailWord_1086514).sum := by decide
  have hdescent : baseEnd_1086514 < baseStart_1086514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086534 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1086534 : Nat := 118140960795 + 1086534 * 2 ^ 59
def prefixEnd_1086534 : Nat := 4983230072969 + 3 ^ 40 * 1086534 * 2
def baseEnd_1086534 : Nat := 247961861978825406412501

theorem tailTrace_1086534 : CollatzResearch.WordTrace tailWord_1086534 prefixEnd_1086534 247961861978825406412501 := by
  unfold tailWord_1086534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238410957677511189959583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26419433763786905385804437 1238410957677511189959583)
  ·
    refine ⟨1857616436516266784939375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1238410957677511189959583 1857616436516266784939375)
    ·
      refine ⟨2786424654774400177409063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1857616436516266784939375 2786424654774400177409063)
      ·
        refine ⟨4179636982161600266113595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786424654774400177409063 4179636982161600266113595)
        ·
          refine ⟨6269455473242400399170393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179636982161600266113595 6269455473242400399170393)
          ·
            refine ⟨4702091604931800299377795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269455473242400399170393 4702091604931800299377795)
            ·
              refine ⟨7053137407397700449066693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702091604931800299377795 7053137407397700449066693)
              ·
                refine ⟨1322463263887068834200005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7053137407397700449066693 1322463263887068834200005)
                ·
                  refine ⟨247961861978825406412501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322463263887068834200005 247961861978825406412501)
                  ·
                    rfl

theorem cell21_1086534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1086534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086534 prefixEnd_1086534 := by exact prefixLift 1086534
  have htrace : WordTrace (prefixWord ++ tailWord_1086534) baseStart_1086534 baseEnd_1086534 := by
    simpa [prefixWord, tailWord_1086534, baseEnd_1086534] using wordTrace_append hprefix tailTrace_1086534
  have hstable : (prefixWord ++ tailWord_1086534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086534).length < 2 ^ (prefixWord ++ tailWord_1086534).sum := by decide
  have hdescent : baseEnd_1086534 < baseStart_1086534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086562 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1086562 : Nat := 118140960795 + 1086562 * 2 ^ 59
def prefixEnd_1086562 : Nat := 4983230072969 + 3 ^ 40 * 1086562 * 2
def baseEnd_1086562 : Nat := 247968251960303579945777

theorem tailTrace_1086562 : CollatzResearch.WordTrace tailWord_1086562 prefixEnd_1086562 247968251960303579945777 := by
  unfold tailWord_1086562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907542972394729715181485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26420114593052612573817293 9907542972394729715181485)
  ·
    refine ⟨3715328614648023643193057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9907542972394729715181485 3715328614648023643193057)
    ·
      refine ⟨2786496460986017732394793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3715328614648023643193057 2786496460986017732394793)
      ·
        refine ⟨2089872345739513299296095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2786496460986017732394793 2089872345739513299296095)
        ·
          refine ⟨3134808518609269948944143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089872345739513299296095 3134808518609269948944143)
          ·
            refine ⟨4702212777913904923416215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134808518609269948944143 4702212777913904923416215)
            ·
              refine ⟨7053319166870857385124323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702212777913904923416215 7053319166870857385124323)
              ·
                refine ⟨10579978750306286077686485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053319166870857385124323 10579978750306286077686485)
                ·
                  refine ⟨247968251960303579945777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10579978750306286077686485 247968251960303579945777)
                  ·
                    rfl

theorem cell21_1086562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1086562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086562 prefixEnd_1086562 := by exact prefixLift 1086562
  have htrace : WordTrace (prefixWord ++ tailWord_1086562) baseStart_1086562 baseEnd_1086562 := by
    simpa [prefixWord, tailWord_1086562, baseEnd_1086562] using wordTrace_append hprefix tailTrace_1086562
  have hstable : (prefixWord ++ tailWord_1086562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086562).length < 2 ^ (prefixWord ++ tailWord_1086562).sum := by decide
  have hdescent : baseEnd_1086562 < baseStart_1086562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086593 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 4]
def baseStart_1086593 : Nat := 118140960795 + 1086593 * 2 ^ 59
def prefixEnd_1086593 : Nat := 4983230072969 + 3 ^ 40 * 1086593 * 2
def baseEnd_1086593 : Nat := 247975326582654414929047

theorem tailTrace_1086593 : CollatzResearch.WordTrace tailWord_1086593 prefixEnd_1086593 247975326582654414929047 := by
  unfold tailWord_1086593
  simp only [CollatzResearch.WordTrace]
  refine ⟨39631302552466611155104433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26420868368311074103402955 39631302552466611155104433)
  ·
    refine ⟨29723476914349958366328325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39631302552466611155104433 29723476914349958366328325)
    ·
      refine ⟨5573151921440617193686561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29723476914349958366328325 5573151921440617193686561)
      ·
        refine ⟨4179863941080462895264921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5573151921440617193686561 4179863941080462895264921)
        ·
          refine ⟨3134897955810347171448691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4179863941080462895264921 3134897955810347171448691)
          ·
            refine ⟨4702346933715520757173037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134897955810347171448691 4702346933715520757173037)
            ·
              refine ⟨1763380100143320283939889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4702346933715520757173037 1763380100143320283939889)
              ·
                refine ⟨1322535075107490212954917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763380100143320283939889 1322535075107490212954917)
                ·
                  refine ⟨247975326582654414929047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322535075107490212954917 247975326582654414929047)
                  ·
                    rfl

theorem cell21_1086593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_1086593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086593 prefixEnd_1086593 := by exact prefixLift 1086593
  have htrace : WordTrace (prefixWord ++ tailWord_1086593) baseStart_1086593 baseEnd_1086593 := by
    simpa [prefixWord, tailWord_1086593, baseEnd_1086593] using wordTrace_append hprefix tailTrace_1086593
  have hstable : (prefixWord ++ tailWord_1086593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086593).length < 2 ^ (prefixWord ++ tailWord_1086593).sum := by decide
  have hdescent : baseEnd_1086593 < baseStart_1086593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086610 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1086610 : Nat := 118140960795 + 1086610 * 2 ^ 59
def prefixEnd_1086610 : Nat := 4983230072969 + 3 ^ 40 * 1086610 * 2
def baseEnd_1086610 : Nat := 247979206214266163145679

theorem tailTrace_1086610 : CollatzResearch.WordTrace tailWord_1086610 prefixEnd_1086610 247979206214266163145679 := by
  unfold tailWord_1086610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907980648351255764618321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26421281728936682038982189 9907980648351255764618321)
  ·
    refine ⟨7430985486263441823463741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9907980648351255764618321 7430985486263441823463741)
    ·
      refine ⟨2786619557348790683798903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7430985486263441823463741 2786619557348790683798903)
      ·
        refine ⟨4179929336023186025698355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786619557348790683798903 4179929336023186025698355)
        ·
          refine ⟨6269894004034779038547533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179929336023186025698355 6269894004034779038547533)
          ·
            refine ⟨2351210251513042139455325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6269894004034779038547533 2351210251513042139455325)
            ·
              refine ⟨881703844317390802295747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2351210251513042139455325 881703844317390802295747)
              ·
                refine ⟨1322555766476086203443621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881703844317390802295747 1322555766476086203443621)
                ·
                  refine ⟨247979206214266163145679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322555766476086203443621 247979206214266163145679)
                  ·
                    rfl

theorem cell21_1086610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1086610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086610 prefixEnd_1086610 := by exact prefixLift 1086610
  have htrace : WordTrace (prefixWord ++ tailWord_1086610) baseStart_1086610 baseEnd_1086610 := by
    simpa [prefixWord, tailWord_1086610, baseEnd_1086610] using wordTrace_append hprefix tailTrace_1086610
  have hstable : (prefixWord ++ tailWord_1086610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086610).length < 2 ^ (prefixWord ++ tailWord_1086610).sum := by decide
  have hdescent : baseEnd_1086610 < baseStart_1086610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086621 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1086621 : Nat := 118140960795 + 1086621 * 2 ^ 59
def prefixEnd_1086621 : Nat := 4983230072969 + 3 ^ 40 * 1086621 * 2
def baseEnd_1086621 : Nat := 247981716564132588462323

theorem tailTrace_1086621 : CollatzResearch.WordTrace tailWord_1086621 prefixEnd_1086621 247981716564132588462323 := by
  unfold tailWord_1086621
  simp only [CollatzResearch.WordTrace]
  refine ⟨39632323796365171937123717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26421549197576781291415811 39632323796365171937123717)
  ·
    refine ⟨7431060711818469738210697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39632323796365171937123717 7431060711818469738210697)
    ·
      refine ⟨5573295533863852303658023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7431060711818469738210697 5573295533863852303658023)
      ·
        refine ⟨8359943300795778455487035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573295533863852303658023 8359943300795778455487035)
        ·
          refine ⟨12539914951193667683230553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8359943300795778455487035 12539914951193667683230553)
          ·
            refine ⟨9404936213395250762422915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12539914951193667683230553 9404936213395250762422915)
            ·
              refine ⟨14107404320092876143634373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9404936213395250762422915 14107404320092876143634373)
              ·
                refine ⟨2645138310017414276931445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14107404320092876143634373 2645138310017414276931445)
                ·
                  refine ⟨247981716564132588462323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2645138310017414276931445 247981716564132588462323)
                  ·
                    rfl

theorem cell21_1086621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1086621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086621 prefixEnd_1086621 := by exact prefixLift 1086621
  have htrace : WordTrace (prefixWord ++ tailWord_1086621) baseStart_1086621 baseEnd_1086621 := by
    simpa [prefixWord, tailWord_1086621, baseEnd_1086621] using wordTrace_append hprefix tailTrace_1086621
  have hstable : (prefixWord ++ tailWord_1086621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086621).length < 2 ^ (prefixWord ++ tailWord_1086621).sum := by decide
  have hdescent : baseEnd_1086621 < baseStart_1086621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086652 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1086652 : Nat := 118140960795 + 1086652 * 2 ^ 59
def prefixEnd_1086652 : Nat := 4983230072969 + 3 ^ 40 * 1086652 * 2
def baseEnd_1086652 : Nat := 247988791186483423445593

theorem tailTrace_1086652 : CollatzResearch.WordTrace tailWord_1086652 prefixEnd_1086652 247988791186483423445593 := by
  unfold tailWord_1086652
  simp only [CollatzResearch.WordTrace]
  refine ⟨19816727229626432115751105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26422302972835242821001473 19816727229626432115751105)
  ·
    refine ⟨14862545422219824086813329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19816727229626432115751105 14862545422219824086813329)
    ·
      refine ⟨11146909066664868065109997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14862545422219824086813329 11146909066664868065109997)
      ·
        refine ⟨4180090899999325524416249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11146909066664868065109997 4180090899999325524416249)
        ·
          refine ⟨3135068174999494143312187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4180090899999325524416249 3135068174999494143312187)
          ·
            refine ⟨4702602262499241214968281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135068174999494143312187 4702602262499241214968281)
            ·
              refine ⟨3526951696874430911226211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4702602262499241214968281 3526951696874430911226211)
              ·
                refine ⟨5290427545311646366839317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526951696874430911226211 5290427545311646366839317)
                ·
                  refine ⟨247988791186483423445593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5290427545311646366839317 247988791186483423445593)
                  ·
                    rfl

theorem cell21_1086652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1086652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086652 prefixEnd_1086652 := by exact prefixLift 1086652
  have htrace : WordTrace (prefixWord ++ tailWord_1086652) baseStart_1086652 baseEnd_1086652 := by
    simpa [prefixWord, tailWord_1086652, baseEnd_1086652] using wordTrace_append hprefix tailTrace_1086652
  have hstable : (prefixWord ++ tailWord_1086652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086652).length < 2 ^ (prefixWord ++ tailWord_1086652).sum := by decide
  have hdescent : baseEnd_1086652 < baseStart_1086652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086666 : List Nat := [3, 1, 2, 1, 3, 2, 1, 8]
def baseStart_1086666 : Nat := 118140960795 + 1086666 * 2 ^ 59
def prefixEnd_1086666 : Nat := 4983230072969 + 3 ^ 40 * 1086666 * 2
def baseEnd_1086666 : Nat := 82663995392407503404077

theorem tailTrace_1086666 : CollatzResearch.WordTrace tailWord_1086666 prefixEnd_1086666 82663995392407503404077 := by
  unfold tailWord_1086666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908491270300536155627963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26422643387468096415007901 9908491270300536155627963)
  ·
    refine ⟨14862736905450804233441945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9908491270300536155627963 14862736905450804233441945)
    ·
      refine ⟨11147052679088103175081459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14862736905450804233441945 11147052679088103175081459)
      ·
        refine ⟨16720579018632154762622189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11147052679088103175081459 16720579018632154762622189)
        ·
          refine ⟨6270217131987058035983321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16720579018632154762622189 6270217131987058035983321)
          ·
            refine ⟨4702662848990293526987491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6270217131987058035983321 4702662848990293526987491)
            ·
              refine ⟨7053994273485440290481237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702662848990293526987491 7053994273485440290481237)
              ·
                refine ⟨82663995392407503404077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7053994273485440290481237 82663995392407503404077)
                ·
                  rfl

theorem cell21_1086666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_1086666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086666 prefixEnd_1086666 := by exact prefixLift 1086666
  have htrace : WordTrace (prefixWord ++ tailWord_1086666) baseStart_1086666 baseEnd_1086666 := by
    simpa [prefixWord, tailWord_1086666, baseEnd_1086666] using wordTrace_append hprefix tailTrace_1086666
  have hstable : (prefixWord ++ tailWord_1086666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086666).length < 2 ^ (prefixWord ++ tailWord_1086666).sum := by decide
  have hdescent : baseEnd_1086666 < baseStart_1086666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086714 : List Nat := [3, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_1086714 : Nat := 118140960795 + 1086714 * 2 ^ 59
def prefixEnd_1086714 : Nat := 4983230072969 + 3 ^ 40 * 1086714 * 2
def baseEnd_1086714 : Nat := 248002940431185093412133

theorem tailTrace_1086714 : CollatzResearch.WordTrace tailWord_1086714 prefixEnd_1086714 248002940431185093412133 := by
  unfold tailWord_1086714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908928946257062205064799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26423810523352165880172797 9908928946257062205064799)
  ·
    refine ⟨14863393419385593307597199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9908928946257062205064799 14863393419385593307597199)
    ·
      refine ⟨22295090129078389961395799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14863393419385593307597199 22295090129078389961395799)
      ·
        refine ⟨33442635193617584942093699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22295090129078389961395799 33442635193617584942093699)
        ·
          refine ⟨50163952790426377413140549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33442635193617584942093699 50163952790426377413140549)
          ·
            refine ⟨9405741148204945764963853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50163952790426377413140549 9405741148204945764963853)
            ·
              refine ⟨3527152930576854661861445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9405741148204945764963853 3527152930576854661861445)
              ·
                refine ⟨661341174483160249099021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3527152930576854661861445 661341174483160249099021)
                ·
                  refine ⟨248002940431185093412133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661341174483160249099021 248002940431185093412133)
                  ·
                    rfl

theorem cell21_1086714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_1086714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086714 prefixEnd_1086714 := by exact prefixLift 1086714
  have htrace : WordTrace (prefixWord ++ tailWord_1086714) baseStart_1086714 baseEnd_1086714 := by
    simpa [prefixWord, tailWord_1086714, baseEnd_1086714] using wordTrace_append hprefix tailTrace_1086714
  have hstable : (prefixWord ++ tailWord_1086714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086714).length < 2 ^ (prefixWord ++ tailWord_1086714).sum := by decide
  have hdescent : baseEnd_1086714 < baseStart_1086714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086762 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_1086762 : Nat := 118140960795 + 1086762 * 2 ^ 59
def prefixEnd_1086762 : Nat := 4983230072969 + 3 ^ 40 * 1086762 * 2
def baseEnd_1086762 : Nat := 248013894685147676612035

theorem tailTrace_1086762 : CollatzResearch.WordTrace tailWord_1086762 prefixEnd_1086762 248013894685147676612035 := by
  unfold tailWord_1086762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909366622213588254501635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26424977659236235345337693 9909366622213588254501635)
  ·
    refine ⟨14864049933320382381752453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9909366622213588254501635 14864049933320382381752453)
    ·
      refine ⟨2787009362497571696578585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14864049933320382381752453 2787009362497571696578585)
      ·
        refine ⟨2090257021873178772433939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2787009362497571696578585 2090257021873178772433939)
        ·
          refine ⟨3135385532809768158650909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090257021873178772433939 3135385532809768158650909)
          ·
            refine ⟨1175769574803663059494091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3135385532809768158650909 1175769574803663059494091)
            ·
              refine ⟨1763654362205494589241137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175769574803663059494091 1763654362205494589241137)
              ·
                refine ⟨1322740771654120941930853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763654362205494589241137 1322740771654120941930853)
                ·
                  refine ⟨248013894685147676612035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322740771654120941930853 248013894685147676612035)
                  ·
                    rfl

theorem cell21_1086762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_1086762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086762 prefixEnd_1086762 := by exact prefixLift 1086762
  have htrace : WordTrace (prefixWord ++ tailWord_1086762) baseStart_1086762 baseEnd_1086762 := by
    simpa [prefixWord, tailWord_1086762, baseEnd_1086762] using wordTrace_append hprefix tailTrace_1086762
  have hstable : (prefixWord ++ tailWord_1086762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086762).length < 2 ^ (prefixWord ++ tailWord_1086762).sum := by decide
  have hdescent : baseEnd_1086762 < baseStart_1086762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086773 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 5]
def baseStart_1086773 : Nat := 118140960795 + 1086773 * 2 ^ 59
def prefixEnd_1086773 : Nat := 4983230072969 + 3 ^ 40 * 1086773 * 2
def baseEnd_1086773 : Nat := 248016405035014101928679

theorem tailTrace_1086773 : CollatzResearch.WordTrace tailWord_1086773 prefixEnd_1086773 248016405035014101928679 := by
  unfold tailWord_1086773
  simp only [CollatzResearch.WordTrace]
  refine ⟨39637867691814501896656973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26425245127876334597771315 39637867691814501896656973)
  ·
    refine ⟨14864200384430438211246365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39637867691814501896656973 14864200384430438211246365)
    ·
      refine ⟨5574075144161414329217387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14864200384430438211246365 5574075144161414329217387)
      ·
        refine ⟨8361112716242121493826081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5574075144161414329217387 8361112716242121493826081)
        ·
          refine ⟨6270834537181591120369561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8361112716242121493826081 6270834537181591120369561)
          ·
            refine ⟨4703125902886193340277171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6270834537181591120369561 4703125902886193340277171)
            ·
              refine ⟨7054688854329290010415757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703125902886193340277171 7054688854329290010415757)
              ·
                refine ⟨2645508320373483753905909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7054688854329290010415757 2645508320373483753905909)
                ·
                  refine ⟨248016405035014101928679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2645508320373483753905909 248016405035014101928679)
                  ·
                    rfl

theorem cell21_1086773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_1086773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086773 prefixEnd_1086773 := by exact prefixLift 1086773
  have htrace : WordTrace (prefixWord ++ tailWord_1086773) baseStart_1086773 baseEnd_1086773 := by
    simpa [prefixWord, tailWord_1086773, baseEnd_1086773] using wordTrace_append hprefix tailTrace_1086773
  have hstable : (prefixWord ++ tailWord_1086773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086773).length < 2 ^ (prefixWord ++ tailWord_1086773).sum := by decide
  have hdescent : baseEnd_1086773 < baseStart_1086773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086807 : List Nat := [1, 1, 3, 2, 3, 4, 1, 3, 3]
def baseStart_1086807 : Nat := 118140960795 + 1086807 * 2 ^ 59
def prefixEnd_1086807 : Nat := 4983230072969 + 3 ^ 40 * 1086807 * 2
def baseEnd_1086807 : Nat := 248024164298237598361943

theorem tailTrace_1086807 : CollatzResearch.WordTrace tailWord_1086807 prefixEnd_1086807 248024164298237598361943 := by
  unfold tailWord_1086807
  simp only [CollatzResearch.WordTrace]
  refine ⟨39639107773691325703394675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26426071849127550468929783 39639107773691325703394675)
  ·
    refine ⟨59458661660536988555092013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39639107773691325703394675 59458661660536988555092013)
    ·
      refine ⟨22296998122701370708159505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59458661660536988555092013 22296998122701370708159505)
      ·
        refine ⟨16722748592026028031119629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22296998122701370708159505 16722748592026028031119629)
        ·
          refine ⟨6271030722009760511669861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16722748592026028031119629 6271030722009760511669861)
          ·
            refine ⟨1175818260376830095938099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6271030722009760511669861 1175818260376830095938099)
            ·
              refine ⟨1763727390565245143907149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175818260376830095938099 1763727390565245143907149)
              ·
                refine ⟨661397771461966928965181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763727390565245143907149 661397771461966928965181)
                ·
                  refine ⟨248024164298237598361943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661397771461966928965181 248024164298237598361943)
                  ·
                    rfl

theorem cell21_1086807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 3].length) (baseStart_1086807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086807 prefixEnd_1086807 := by exact prefixLift 1086807
  have htrace : WordTrace (prefixWord ++ tailWord_1086807) baseStart_1086807 baseEnd_1086807 := by
    simpa [prefixWord, tailWord_1086807, baseEnd_1086807] using wordTrace_append hprefix tailTrace_1086807
  have hstable : (prefixWord ++ tailWord_1086807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086807).length < 2 ^ (prefixWord ++ tailWord_1086807).sum := by decide
  have hdescent : baseEnd_1086807 < baseStart_1086807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086824 : List Nat := [2, 1, 4, 2, 3, 1, 3, 2, 3]
def baseStart_1086824 : Nat := 118140960795 + 1086824 * 2 ^ 59
def prefixEnd_1086824 : Nat := 4983230072969 + 3 ^ 40 * 1086824 * 2
def baseEnd_1086824 : Nat := 248028043929849346578575

theorem tailTrace_1086824 : CollatzResearch.WordTrace tailWord_1086824 prefixEnd_1086824 248028043929849346578575 := by
  unfold tailWord_1086824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19819863907314868803381763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26426485209753158404509017 19819863907314868803381763)
  ·
    refine ⟨29729795860972303205072645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19819863907314868803381763 29729795860972303205072645)
    ·
      refine ⟨5574336723932306850951121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29729795860972303205072645 5574336723932306850951121)
      ·
        refine ⟨4180752542949230138213341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5574336723932306850951121 4180752542949230138213341)
        ·
          refine ⟨1567782203605961301830003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4180752542949230138213341 1567782203605961301830003)
          ·
            refine ⟨2351673305408941952745005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567782203605961301830003 2351673305408941952745005)
            ·
              refine ⟨881877489528353232279377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2351673305408941952745005 881877489528353232279377)
              ·
                refine ⟨661408117146264924209533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881877489528353232279377 661408117146264924209533)
                ·
                  refine ⟨248028043929849346578575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661408117146264924209533 248028043929849346578575)
                  ·
                    rfl

theorem cell21_1086824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_1086824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086824 prefixEnd_1086824 := by exact prefixLift 1086824
  have htrace : WordTrace (prefixWord ++ tailWord_1086824) baseStart_1086824 baseEnd_1086824 := by
    simpa [prefixWord, tailWord_1086824, baseEnd_1086824] using wordTrace_append hprefix tailTrace_1086824
  have hstable : (prefixWord ++ tailWord_1086824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086824).length < 2 ^ (prefixWord ++ tailWord_1086824).sum := by decide
  have hdescent : baseEnd_1086824 < baseStart_1086824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086880 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_1086880 : Nat := 118140960795 + 1086880 * 2 ^ 59
def prefixEnd_1086880 : Nat := 4983230072969 + 3 ^ 40 * 1086880 * 2
def baseEnd_1086880 : Nat := 248040823892805693645127

theorem tailTrace_1086880 : CollatzResearch.WordTrace tailWord_1086880 prefixEnd_1086880 248040823892805693645127 := by
  unfold tailWord_1086880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19820885151213429585401047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26427846868284572780534729 19820885151213429585401047)
  ·
    refine ⟨29731327726820144378101571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19820885151213429585401047 29731327726820144378101571)
    ·
      refine ⟨44596991590230216567152357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29731327726820144378101571 44596991590230216567152357)
      ·
        refine ⟨8361935923168165606341067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44596991590230216567152357 8361935923168165606341067)
        ·
          refine ⟨12542903884752248409511601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8361935923168165606341067 12542903884752248409511601)
          ·
            refine ⟨9407177913564186307133701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12542903884752248409511601 9407177913564186307133701)
            ·
              refine ⟨1763845858793284932587569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9407177913564186307133701 1763845858793284932587569)
              ·
                refine ⟨1322884394094963699440677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763845858793284932587569 1322884394094963699440677)
                ·
                  refine ⟨248040823892805693645127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322884394094963699440677 248040823892805693645127)
                  ·
                    rfl

theorem cell21_1086880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_1086880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086880 prefixEnd_1086880 := by exact prefixLift 1086880
  have htrace : WordTrace (prefixWord ++ tailWord_1086880) baseStart_1086880 baseEnd_1086880 := by
    simpa [prefixWord, tailWord_1086880, baseEnd_1086880] using wordTrace_append hprefix tailTrace_1086880
  have hstable : (prefixWord ++ tailWord_1086880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086880).length < 2 ^ (prefixWord ++ tailWord_1086880).sum := by decide
  have hdescent : baseEnd_1086880 < baseStart_1086880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086984 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_1086984 : Nat := 118140960795 + 1086984 * 2 ^ 59
def prefixEnd_1086984 : Nat := 4983230072969 + 3 ^ 40 * 1086984 * 2
def baseEnd_1086984 : Nat := 248064558109724623911581

theorem tailTrace_1086984 : CollatzResearch.WordTrace tailWord_1086984 prefixEnd_1086984 248064558109724623911581 := by
  unfold tailWord_1086984
  simp only [CollatzResearch.WordTrace]
  refine ⟨19822781747025042466294003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26430375662700056621725337 19822781747025042466294003)
  ·
    refine ⟨29734172620537563699441005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19822781747025042466294003 29734172620537563699441005)
    ·
      refine ⟨11150314732701586387290377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29734172620537563699441005 11150314732701586387290377)
      ·
        refine ⟨8362736049526189790467783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11150314732701586387290377 8362736049526189790467783)
        ·
          refine ⟨12544104074289284685701675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8362736049526189790467783 12544104074289284685701675)
          ·
            refine ⟨18816156111433927028552513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12544104074289284685701675 18816156111433927028552513)
            ·
              refine ⟨14112117083575445271414385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18816156111433927028552513 14112117083575445271414385)
              ·
                refine ⟨10584087812681583953560789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14112117083575445271414385 10584087812681583953560789)
                ·
                  refine ⟨248064558109724623911581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10584087812681583953560789 248064558109724623911581)
                  ·
                    rfl

theorem cell21_1086984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_1086984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086984 prefixEnd_1086984 := by exact prefixLift 1086984
  have htrace : WordTrace (prefixWord ++ tailWord_1086984) baseStart_1086984 baseEnd_1086984 := by
    simpa [prefixWord, tailWord_1086984, baseEnd_1086984] using wordTrace_append hprefix tailTrace_1086984
  have hstable : (prefixWord ++ tailWord_1086984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086984).length < 2 ^ (prefixWord ++ tailWord_1086984).sum := by decide
  have hdescent : baseEnd_1086984 < baseStart_1086984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086987 : List Nat := [1, 1, 1, 1, 9, 1, 7]
def baseStart_1086987 : Nat := 118140960795 + 1086987 * 2 ^ 59
def prefixEnd_1086987 : Nat := 4983230072969 + 3 ^ 40 * 1086987 * 2
def baseEnd_1086987 : Nat := 27562804750066365040175

theorem tailTrace_1086987 : CollatzResearch.WordTrace tailWord_1086987 prefixEnd_1086987 27562804750066365040175 := by
  unfold tailWord_1086987
  simp only [CollatzResearch.WordTrace]
  refine ⟨39645672913039216444947215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26430448608692810963298143 39645672913039216444947215)
  ·
    refine ⟨59468509369558824667420823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39645672913039216444947215 59468509369558824667420823)
    ·
      refine ⟨89202764054338237001131235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59468509369558824667420823 89202764054338237001131235)
      ·
        refine ⟨133804146081507355501696853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89202764054338237001131235 133804146081507355501696853)
        ·
          refine ⟨784008668446332161142755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 133804146081507355501696853 784008668446332161142755)
          ·
            refine ⟨1176013002669498241714133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784008668446332161142755 1176013002669498241714133)
            ·
              refine ⟨27562804750066365040175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1176013002669498241714133 27562804750066365040175)
              ·
                rfl

theorem cell21_1086987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 7].length) (baseStart_1086987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1086987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1086987 prefixEnd_1086987 := by exact prefixLift 1086987
  have htrace : WordTrace (prefixWord ++ tailWord_1086987) baseStart_1086987 baseEnd_1086987 := by
    simpa [prefixWord, tailWord_1086987, baseEnd_1086987] using wordTrace_append hprefix tailTrace_1086987
  have hstable : (prefixWord ++ tailWord_1086987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086987).length < 2 ^ (prefixWord ++ tailWord_1086987).sum := by decide
  have hdescent : baseEnd_1086987 < baseStart_1086987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087077 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1087077 : Nat := 118140960795 + 1087077 * 2 ^ 59
def prefixEnd_1087077 : Nat := 4983230072969 + 3 ^ 40 * 1087077 * 2
def baseEnd_1087077 : Nat := 248085781976777128861391

theorem tailTrace_1087077 : CollatzResearch.WordTrace tailWord_1087077 prefixEnd_1087077 248085781976777128861391 := by
  unfold tailWord_1087077
  simp only [CollatzResearch.WordTrace]
  refine ⟨39648955482713161815723485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26432636988475441210482323 39648955482713161815723485)
  ·
    refine ⟨14868358306017435680896307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39648955482713161815723485 14868358306017435680896307)
    ·
      refine ⟨22302537459026153521344461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14868358306017435680896307 22302537459026153521344461)
      ·
        refine ⟨8363451547134807570504173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22302537459026153521344461 8363451547134807570504173)
        ·
          refine ⟨3136294330175552838939065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8363451547134807570504173 3136294330175552838939065)
          ·
            refine ⟨2352220747631664629204299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3136294330175552838939065 2352220747631664629204299)
            ·
              refine ⟨3528331121447496943806449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352220747631664629204299 3528331121447496943806449)
              ·
                refine ⟨2646248341085622707854837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3528331121447496943806449 2646248341085622707854837)
                ·
                  refine ⟨248085781976777128861391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2646248341085622707854837 248085781976777128861391)
                  ·
                    rfl

theorem cell21_1087077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1087077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087077 prefixEnd_1087077 := by exact prefixLift 1087077
  have htrace : WordTrace (prefixWord ++ tailWord_1087077) baseStart_1087077 baseEnd_1087077 := by
    simpa [prefixWord, tailWord_1087077, baseEnd_1087077] using wordTrace_append hprefix tailTrace_1087077
  have hstable : (prefixWord ++ tailWord_1087077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087077).length < 2 ^ (prefixWord ++ tailWord_1087077).sum := by decide
  have hdescent : baseEnd_1087077 < baseStart_1087077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087108 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1087108 : Nat := 118140960795 + 1087108 * 2 ^ 59
def prefixEnd_1087108 : Nat := 4983230072969 + 3 ^ 40 * 1087108 * 2
def baseEnd_1087108 : Nat := 248092856599127963844661

theorem tailTrace_1087108 : CollatzResearch.WordTrace tailWord_1087108 prefixEnd_1087108 248092856599127963844661 := by
  unfold tailWord_1087108
  simp only [CollatzResearch.WordTrace]
  refine ⟨19825043072800427055050989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26433390763733902740067985 19825043072800427055050989)
  ·
    refine ⟨7434391152300160145644121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19825043072800427055050989 7434391152300160145644121)
    ·
      refine ⟨5575793364225120109233091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7434391152300160145644121 5575793364225120109233091)
      ·
        refine ⟨8363690046337680163849637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5575793364225120109233091 8363690046337680163849637)
        ·
          refine ⟨1568191883688315030721807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8363690046337680163849637 1568191883688315030721807)
          ·
            refine ⟨2352287825532472546082711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568191883688315030721807 2352287825532472546082711)
            ·
              refine ⟨3528431738298708819124067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352287825532472546082711 3528431738298708819124067)
              ·
                refine ⟨5292647607448063228686101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528431738298708819124067 5292647607448063228686101)
                ·
                  refine ⟨248092856599127963844661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5292647607448063228686101 248092856599127963844661)
                  ·
                    rfl

theorem cell21_1087108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1087108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087108 prefixEnd_1087108 := by exact prefixLift 1087108
  have htrace : WordTrace (prefixWord ++ tailWord_1087108) baseStart_1087108 baseEnd_1087108 := by
    simpa [prefixWord, tailWord_1087108, baseEnd_1087108] using wordTrace_append hprefix tailTrace_1087108
  have hstable : (prefixWord ++ tailWord_1087108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087108).length < 2 ^ (prefixWord ++ tailWord_1087108).sum := by decide
  have hdescent : baseEnd_1087108 < baseStart_1087108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087167 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 4]
def baseStart_1087167 : Nat := 118140960795 + 1087167 * 2 ^ 59
def prefixEnd_1087167 : Nat := 4983230072969 + 3 ^ 40 * 1087167 * 2
def baseEnd_1087167 : Nat := 248106321202956972361207

theorem tailTrace_1087167 : CollatzResearch.WordTrace tailWord_1087167 prefixEnd_1087167 248106321202956972361207 := by
  unfold tailWord_1087167
  simp only [CollatzResearch.WordTrace]
  refine ⟨39652238052387107186499755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26434825368258071457666503 39652238052387107186499755)
  ·
    refine ⟨59478357078580660779749633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39652238052387107186499755 59478357078580660779749633)
    ·
      refine ⟨44608767808935495584812225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59478357078580660779749633 44608767808935495584812225)
      ·
        refine ⟨33456575856701621688609169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44608767808935495584812225 33456575856701621688609169)
        ·
          refine ⟨25092431892526216266456877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33456575856701621688609169 25092431892526216266456877)
          ·
            refine ⟨9409661959697331099921329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25092431892526216266456877 9409661959697331099921329)
            ·
              refine ⟨7057246469772998324940997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9409661959697331099921329 7057246469772998324940997)
              ·
                refine ⟨1323233713082437185926437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7057246469772998324940997 1323233713082437185926437)
                ·
                  refine ⟨248106321202956972361207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323233713082437185926437 248106321202956972361207)
                  ·
                    rfl

theorem cell21_1087167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_1087167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087167 prefixEnd_1087167 := by exact prefixLift 1087167
  have htrace : WordTrace (prefixWord ++ tailWord_1087167) baseStart_1087167 baseEnd_1087167 := by
    simpa [prefixWord, tailWord_1087167, baseEnd_1087167] using wordTrace_append hprefix tailTrace_1087167
  have hstable : (prefixWord ++ tailWord_1087167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087167).length < 2 ^ (prefixWord ++ tailWord_1087167).sum := by decide
  have hdescent : baseEnd_1087167 < baseStart_1087167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087243 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 4]
def baseStart_1087243 : Nat := 118140960795 + 1087243 * 2 ^ 59
def prefixEnd_1087243 : Nat := 4983230072969 + 3 ^ 40 * 1087243 * 2
def baseEnd_1087243 : Nat := 248123665438397729094385

theorem tailTrace_1087243 : CollatzResearch.WordTrace tailWord_1087243 prefixEnd_1087243 248123665438397729094385 := by
  unfold tailWord_1087243
  simp only [CollatzResearch.WordTrace]
  refine ⟨39655010000111772166266383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26436673333407848110844255 39655010000111772166266383)
  ·
    refine ⟨59482515000167658249399575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39655010000111772166266383 59482515000167658249399575)
    ·
      refine ⟨89223772500251487374099363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59482515000167658249399575 89223772500251487374099363)
      ·
        refine ⟨133835658750377231061149045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89223772500251487374099363 133835658750377231061149045)
        ·
          refine ⟨12547093007847865411982723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133835658750377231061149045 12547093007847865411982723)
          ·
            refine ⟨18820639511771798117974085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12547093007847865411982723 18820639511771798117974085)
            ·
              refine ⟨3528869908457212147120141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18820639511771798117974085 3528869908457212147120141)
              ·
                refine ⟨1323326215671454555170053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3528869908457212147120141 1323326215671454555170053)
                ·
                  refine ⟨248123665438397729094385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323326215671454555170053 248123665438397729094385)
                  ·
                    rfl

theorem cell21_1087243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_1087243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087243 prefixEnd_1087243 := by exact prefixLift 1087243
  have htrace : WordTrace (prefixWord ++ tailWord_1087243) baseStart_1087243 baseEnd_1087243 := by
    simpa [prefixWord, tailWord_1087243, baseEnd_1087243] using wordTrace_append hprefix tailTrace_1087243
  have hstable : (prefixWord ++ tailWord_1087243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087243).length < 2 ^ (prefixWord ++ tailWord_1087243).sum := by decide
  have hdescent : baseEnd_1087243 < baseStart_1087243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087288 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_1087288 : Nat := 118140960795 + 1087288 * 2 ^ 59
def prefixEnd_1087288 : Nat := 4983230072969 + 3 ^ 40 * 1087288 * 2
def baseEnd_1087288 : Nat := 248133935051487650844293

theorem tailTrace_1087288 : CollatzResearch.WordTrace tailWord_1087288 prefixEnd_1087288 248133935051487650844293 := by
  unfold tailWord_1087288
  simp only [CollatzResearch.WordTrace]
  refine ⟨19828325642474372425827259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26437767523299163234436345 19828325642474372425827259)
  ·
    refine ⟨29742488463711558638740889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19828325642474372425827259 29742488463711558638740889)
    ·
      refine ⟨22306866347783668979055667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29742488463711558638740889 22306866347783668979055667)
      ·
        refine ⟨33460299521675503468583501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22306866347783668979055667 33460299521675503468583501)
        ·
          refine ⟨12547612320628313800718813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33460299521675503468583501 12547612320628313800718813)
          ·
            refine ⟨4705354620235617675269555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12547612320628313800718813 4705354620235617675269555)
            ·
              refine ⟨7058031930353426512904333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705354620235617675269555 7058031930353426512904333)
              ·
                refine ⟨2646761973882534942339125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7058031930353426512904333 2646761973882534942339125)
                ·
                  refine ⟨248133935051487650844293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2646761973882534942339125 248133935051487650844293)
                  ·
                    rfl

theorem cell21_1087288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_1087288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087288 prefixEnd_1087288 := by exact prefixLift 1087288
  have htrace : WordTrace (prefixWord ++ tailWord_1087288) baseStart_1087288 baseEnd_1087288 := by
    simpa [prefixWord, tailWord_1087288, baseEnd_1087288] using wordTrace_append hprefix tailTrace_1087288
  have hstable : (prefixWord ++ tailWord_1087288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087288).length < 2 ^ (prefixWord ++ tailWord_1087288).sum := by decide
  have hdescent : baseEnd_1087288 < baseStart_1087288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087308 : List Nat := [2, 2, 1, 3, 5, 1, 2, 5]
def baseStart_1087308 : Nat := 118140960795 + 1087308 * 2 ^ 59
def prefixEnd_1087308 : Nat := 4983230072969 + 3 ^ 40 * 1087308 * 2
def baseEnd_1087308 : Nat := 82712833107990686836973

theorem tailTrace_1087308 : CollatzResearch.WordTrace tailWord_1087308 prefixEnd_1087308 82712833107990686836973 := by
  unfold tailWord_1087308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19828690372438144133691289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26438253829917525511588385 19828690372438144133691289)
  ·
    refine ⟨14871517779328608100268467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19828690372438144133691289 14871517779328608100268467)
    ·
      refine ⟨22307276668992912150402701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14871517779328608100268467 22307276668992912150402701)
      ·
        refine ⟨8365228750872342056401013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22307276668992912150402701 8365228750872342056401013)
        ·
          refine ⟨784240195394282067787595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8365228750872342056401013 784240195394282067787595)
          ·
            refine ⟨1176360293091423101681393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784240195394282067787595 1176360293091423101681393)
            ·
              refine ⟨882270219818567326261045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176360293091423101681393 882270219818567326261045)
              ·
                refine ⟨82712833107990686836973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 882270219818567326261045 82712833107990686836973)
                ·
                  rfl

theorem cell21_1087308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_1087308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087308 prefixEnd_1087308 := by exact prefixLift 1087308
  have htrace : WordTrace (prefixWord ++ tailWord_1087308) baseStart_1087308 baseEnd_1087308 := by
    simpa [prefixWord, tailWord_1087308, baseEnd_1087308] using wordTrace_append hprefix tailTrace_1087308
  have hstable : (prefixWord ++ tailWord_1087308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087308).length < 2 ^ (prefixWord ++ tailWord_1087308).sum := by decide
  have hdescent : baseEnd_1087308 < baseStart_1087308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087364 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1087364 : Nat := 118140960795 + 1087364 * 2 ^ 59
def prefixEnd_1087364 : Nat := 4983230072969 + 3 ^ 40 * 1087364 * 2
def baseEnd_1087364 : Nat := 248151279286928407577471

theorem tailTrace_1087364 : CollatzResearch.WordTrace tailWord_1087364 prefixEnd_1087364 248151279286928407577471 := by
  unfold tailWord_1087364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19829711616336704915710573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26439615488448939887614097 19829711616336704915710573)
  ·
    refine ⟨7436141856126264343391465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19829711616336704915710573 7436141856126264343391465)
    ·
      refine ⟨5577106392094698257543599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7436141856126264343391465 5577106392094698257543599)
      ·
        refine ⟨8365659588142047386315399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577106392094698257543599 8365659588142047386315399)
        ·
          refine ⟨12548489382213071079473099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8365659588142047386315399 12548489382213071079473099)
          ·
            refine ⟨18822734073319606619209649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12548489382213071079473099 18822734073319606619209649)
            ·
              refine ⟨14117050554989704964407237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18822734073319606619209649 14117050554989704964407237)
              ·
                refine ⟨2646946979060569680826357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14117050554989704964407237 2646946979060569680826357)
                ·
                  refine ⟨248151279286928407577471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2646946979060569680826357 248151279286928407577471)
                  ·
                    rfl

theorem cell21_1087364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1087364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087364 prefixEnd_1087364 := by exact prefixLift 1087364
  have htrace : WordTrace (prefixWord ++ tailWord_1087364) baseStart_1087364 baseEnd_1087364 := by
    simpa [prefixWord, tailWord_1087364, baseEnd_1087364] using wordTrace_append hprefix tailTrace_1087364
  have hstable : (prefixWord ++ tailWord_1087364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087364).length < 2 ^ (prefixWord ++ tailWord_1087364).sum := by decide
  have hdescent : baseEnd_1087364 < baseStart_1087364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087381 : List Nat := [1, 3, 2, 1, 1, 3, 2, 5, 3]
def baseStart_1087381 : Nat := 118140960795 + 1087381 * 2 ^ 59
def prefixEnd_1087381 : Nat := 4983230072969 + 3 ^ 40 * 1087381 * 2
def baseEnd_1087381 : Nat := 248155158918540155794103

theorem tailTrace_1087381 : CollatzResearch.WordTrace tailWord_1087381 prefixEnd_1087381 248155158918540155794103 := by
  unfold tailWord_1087381
  simp only [CollatzResearch.WordTrace]
  refine ⟨39660043273611821734789997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26440028849074547823193331 39660043273611821734789997)
  ·
    refine ⟨14872516227604433150546249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39660043273611821734789997 14872516227604433150546249)
    ·
      refine ⟨11154387170703324862909687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14872516227604433150546249 11154387170703324862909687)
      ·
        refine ⟨16731580756054987294364531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11154387170703324862909687 16731580756054987294364531)
        ·
          refine ⟨25097371134082480941546797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16731580756054987294364531 25097371134082480941546797)
          ·
            refine ⟨9411514175280930353080049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25097371134082480941546797 9411514175280930353080049)
            ·
              refine ⟨7058635631460697764810037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9411514175280930353080049 7058635631460697764810037)
              ·
                refine ⟨661747090449440415450941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7058635631460697764810037 661747090449440415450941)
                ·
                  refine ⟨248155158918540155794103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661747090449440415450941 248155158918540155794103)
                  ·
                    rfl

theorem cell21_1087381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_1087381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087381 prefixEnd_1087381 := by exact prefixLift 1087381
  have htrace : WordTrace (prefixWord ++ tailWord_1087381) baseStart_1087381 baseEnd_1087381 := by
    simpa [prefixWord, tailWord_1087381, baseEnd_1087381] using wordTrace_append hprefix tailTrace_1087381
  have hstable : (prefixWord ++ tailWord_1087381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087381).length < 2 ^ (prefixWord ++ tailWord_1087381).sum := by decide
  have hdescent : baseEnd_1087381 < baseStart_1087381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087390 : List Nat := [4, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1087390 : Nat := 118140960795 + 1087390 * 2 ^ 59
def prefixEnd_1087390 : Nat := 4983230072969 + 3 ^ 40 * 1087390 * 2
def baseEnd_1087390 : Nat := 248157212841158140144085

theorem tailTrace_1087390 : CollatzResearch.WordTrace tailWord_1087390 prefixEnd_1087390 248157212841158140144085 := by
  unfold tailWord_1087390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4957546441322402033983453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26440247687052810847911749 4957546441322402033983453)
  ·
    refine ⟨1859079915495900762743795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4957546441322402033983453 1859079915495900762743795)
    ·
      refine ⟨2788619873243851144115693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859079915495900762743795 2788619873243851144115693)
      ·
        refine ⟨1045732452466444179043385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2788619873243851144115693 1045732452466444179043385)
        ·
          refine ⟨784299339349833134282539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045732452466444179043385 784299339349833134282539)
          ·
            refine ⟨1176449009024749701423809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784299339349833134282539 1176449009024749701423809)
            ·
              refine ⟨882336756768562276067857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176449009024749701423809 882336756768562276067857)
              ·
                refine ⟨661752567576421707050893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882336756768562276067857 661752567576421707050893)
                ·
                  refine ⟨248157212841158140144085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661752567576421707050893 248157212841158140144085)
                  ·
                    rfl

theorem cell21_1087390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1087390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087390 prefixEnd_1087390 := by exact prefixLift 1087390
  have htrace : WordTrace (prefixWord ++ tailWord_1087390) baseStart_1087390 baseEnd_1087390 := by
    simpa [prefixWord, tailWord_1087390, baseEnd_1087390] using wordTrace_append hprefix tailTrace_1087390
  have hstable : (prefixWord ++ tailWord_1087390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087390).length < 2 ^ (prefixWord ++ tailWord_1087390).sum := by decide
  have hdescent : baseEnd_1087390 < baseStart_1087390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087446 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1087446 : Nat := 118140960795 + 1087446 * 2 ^ 59
def prefixEnd_1087446 : Nat := 4983230072969 + 3 ^ 40 * 1087446 * 2
def baseEnd_1087446 : Nat := 248169992804114487210637

theorem tailTrace_1087446 : CollatzResearch.WordTrace tailWord_1087446 prefixEnd_1087446 248169992804114487210637 := by
  unfold tailWord_1087446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478900876148521114744137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26441609345584225223937461 2478900876148521114744137)
  ·
    refine ⟨1859175657111390836058103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2478900876148521114744137 1859175657111390836058103)
    ·
      refine ⟨2788763485667086254087155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859175657111390836058103 2788763485667086254087155)
      ·
        refine ⟨4183145228500629381130733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2788763485667086254087155 4183145228500629381130733)
        ·
          refine ⟨1568679460687736017924025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4183145228500629381130733 1568679460687736017924025)
          ·
            refine ⟨1176509595515802013443019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568679460687736017924025 1176509595515802013443019)
            ·
              refine ⟨1764764393273703020164529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176509595515802013443019 1764764393273703020164529)
              ·
                refine ⟨1323573294955277265123397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764764393273703020164529 1323573294955277265123397)
                ·
                  refine ⟨248169992804114487210637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323573294955277265123397 248169992804114487210637)
                  ·
                    rfl

theorem cell21_1087446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1087446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087446 prefixEnd_1087446 := by exact prefixLift 1087446
  have htrace : WordTrace (prefixWord ++ tailWord_1087446) baseStart_1087446 baseEnd_1087446 := by
    simpa [prefixWord, tailWord_1087446, baseEnd_1087446] using wordTrace_append hprefix tailTrace_1087446
  have hstable : (prefixWord ++ tailWord_1087446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087446).length < 2 ^ (prefixWord ++ tailWord_1087446).sum := by decide
  have hdescent : baseEnd_1087446 < baseStart_1087446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087457 : List Nat := [1, 2, 3, 1, 2, 1, 4, 4, 3]
def baseStart_1087457 : Nat := 118140960795 + 1087457 * 2 ^ 59
def prefixEnd_1087457 : Nat := 4983230072969 + 3 ^ 40 * 1087457 * 2
def baseEnd_1087457 : Nat := 248172503153980912527281

theorem tailTrace_1087457 : CollatzResearch.WordTrace tailWord_1087457 prefixEnd_1087457 248172503153980912527281 := by
  unfold tailWord_1087457
  simp only [CollatzResearch.WordTrace]
  refine ⟨39662815221336486714556625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26441876814224324476371083 39662815221336486714556625)
  ·
    refine ⟨29747111416002365035917469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39662815221336486714556625 29747111416002365035917469)
    ·
      refine ⟨11155166781000886888469051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29747111416002365035917469 11155166781000886888469051)
      ·
        refine ⟨16732750171501330332703577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11155166781000886888469051 16732750171501330332703577)
        ·
          refine ⟨12549562628625997749527683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16732750171501330332703577 12549562628625997749527683)
          ·
            refine ⟨18824343942938996624291525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12549562628625997749527683 18824343942938996624291525)
            ·
              refine ⟨3529564489301061867054661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18824343942938996624291525 3529564489301061867054661)
              ·
                refine ⟨661793341743949100072749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3529564489301061867054661 661793341743949100072749)
                ·
                  refine ⟨248172503153980912527281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661793341743949100072749 248172503153980912527281)
                  ·
                    rfl

theorem cell21_1087457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_1087457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087457 prefixEnd_1087457 := by exact prefixLift 1087457
  have htrace : WordTrace (prefixWord ++ tailWord_1087457) baseStart_1087457 baseEnd_1087457 := by
    simpa [prefixWord, tailWord_1087457, baseEnd_1087457] using wordTrace_append hprefix tailTrace_1087457
  have hstable : (prefixWord ++ tailWord_1087457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087457).length < 2 ^ (prefixWord ++ tailWord_1087457).sum := by decide
  have hdescent : baseEnd_1087457 < baseStart_1087457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087494 : List Nat := [6, 2, 1, 2, 2, 1, 7]
def baseStart_1087494 : Nat := 118140960795 + 1087494 * 2 ^ 59
def prefixEnd_1087494 : Nat := 4983230072969 + 3 ^ 40 * 1087494 * 2
def baseEnd_1087494 : Nat := 27575660784230785601171

theorem tailTrace_1087494 : CollatzResearch.WordTrace tailWord_1087494 prefixEnd_1087494 27575660784230785601171 := by
  unfold tailWord_1087494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239505147568826313551673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26442776481468294689102357 1239505147568826313551673)
  ·
    refine ⟨929628860676619735163755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1239505147568826313551673 929628860676619735163755)
    ·
      refine ⟨1394443291014929602745633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929628860676619735163755 1394443291014929602745633)
      ·
        refine ⟨1045832468261197202059225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394443291014929602745633 1045832468261197202059225)
        ·
          refine ⟨784374351195897901544419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045832468261197202059225 784374351195897901544419)
          ·
            refine ⟨1176561526793846852316629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784374351195897901544419 1176561526793846852316629)
            ·
              refine ⟨27575660784230785601171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1176561526793846852316629 27575660784230785601171)
              ·
                rfl

theorem cell21_1087494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 7].length) (baseStart_1087494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087494 prefixEnd_1087494 := by exact prefixLift 1087494
  have htrace : WordTrace (prefixWord ++ tailWord_1087494) baseStart_1087494 baseEnd_1087494 := by
    simpa [prefixWord, tailWord_1087494, baseEnd_1087494] using wordTrace_append hprefix tailTrace_1087494
  have hstable : (prefixWord ++ tailWord_1087494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087494).length < 2 ^ (prefixWord ++ tailWord_1087494).sum := by decide
  have hdescent : baseEnd_1087494 < baseStart_1087494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087508 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 5]
def baseStart_1087508 : Nat := 118140960795 + 1087508 * 2 ^ 59
def prefixEnd_1087508 : Nat := 4983230072969 + 3 ^ 40 * 1087508 * 2
def baseEnd_1087508 : Nat := 248184142048816157177177

theorem tailTrace_1087508 : CollatzResearch.WordTrace tailWord_1087508 prefixEnd_1087508 248184142048816157177177 := by
  unfold tailWord_1087508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19832337672075861212331589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26443116896101148283108785 19832337672075861212331589)
  ·
    refine ⟨3718563313514223977312173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19832337672075861212331589 3718563313514223977312173)
    ·
      refine ⟨1394461242567833991492065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3718563313514223977312173 1394461242567833991492065)
      ·
        refine ⟨1045845931925875493619049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394461242567833991492065 1045845931925875493619049)
        ·
          refine ⟨784384448944406620214287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045845931925875493619049 784384448944406620214287)
          ·
            refine ⟨1176576673416609930321431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784384448944406620214287 1176576673416609930321431)
            ·
              refine ⟨1764865010124914895482147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176576673416609930321431 1764865010124914895482147)
              ·
                refine ⟨2647297515187372343223221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764865010124914895482147 2647297515187372343223221)
                ·
                  refine ⟨248184142048816157177177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2647297515187372343223221 248184142048816157177177)
                  ·
                    rfl

theorem cell21_1087508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_1087508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087508 prefixEnd_1087508 := by exact prefixLift 1087508
  have htrace : WordTrace (prefixWord ++ tailWord_1087508) baseStart_1087508 baseEnd_1087508 := by
    simpa [prefixWord, tailWord_1087508, baseEnd_1087508] using wordTrace_append hprefix tailTrace_1087508
  have hstable : (prefixWord ++ tailWord_1087508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087508).length < 2 ^ (prefixWord ++ tailWord_1087508).sum := by decide
  have hdescent : baseEnd_1087508 < baseStart_1087508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087609 : List Nat := [1, 2, 1, 3, 4, 1, 1, 5, 3]
def baseStart_1087609 : Nat := 118140960795 + 1087609 * 2 ^ 59
def prefixEnd_1087609 : Nat := 4983230072969 + 3 ^ 40 * 1087609 * 2
def baseEnd_1087609 : Nat := 248207191624862425993637

theorem tailTrace_1087609 : CollatzResearch.WordTrace tailWord_1087609 prefixEnd_1087609 248207191624862425993637 := by
  unfold tailWord_1087609
  simp only [CollatzResearch.WordTrace]
  refine ⟨39668359116785816674089881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26445572744523877782726587 39668359116785816674089881)
  ·
    refine ⟨29751269337589362505567411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39668359116785816674089881 29751269337589362505567411)
    ·
      refine ⟨44626904006384043758351117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29751269337589362505567411 44626904006384043758351117)
      ·
        refine ⟨16735089002394016409381669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44626904006384043758351117 16735089002394016409381669)
        ·
          refine ⟨3137829187948878076759063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16735089002394016409381669 3137829187948878076759063)
          ·
            refine ⟨4706743781923317115138595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137829187948878076759063 4706743781923317115138595)
            ·
              refine ⟨7060115672884975672707893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4706743781923317115138595 7060115672884975672707893)
              ·
                refine ⟨661885844332966469316365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7060115672884975672707893 661885844332966469316365)
                ·
                  refine ⟨248207191624862425993637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661885844332966469316365 248207191624862425993637)
                  ·
                    rfl

theorem cell21_1087609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_1087609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087609 prefixEnd_1087609 := by exact prefixLift 1087609
  have htrace : WordTrace (prefixWord ++ tailWord_1087609) baseStart_1087609 baseEnd_1087609 := by
    simpa [prefixWord, tailWord_1087609, baseEnd_1087609] using wordTrace_append hprefix tailTrace_1087609
  have hstable : (prefixWord ++ tailWord_1087609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087609).length < 2 ^ (prefixWord ++ tailWord_1087609).sum := by decide
  have hdescent : baseEnd_1087609 < baseStart_1087609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087623 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 4]
def baseStart_1087623 : Nat := 118140960795 + 1087623 * 2 ^ 59
def prefixEnd_1087623 : Nat := 4983230072969 + 3 ^ 40 * 1087623 * 2
def baseEnd_1087623 : Nat := 248210386615601512760275

theorem tailTrace_1087623 : CollatzResearch.WordTrace tailWord_1087623 prefixEnd_1087623 248210386615601512760275 := by
  unfold tailWord_1087623
  simp only [CollatzResearch.WordTrace]
  refine ⟨39668869738735097065099523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26445913159156731376733015 39668869738735097065099523)
  ·
    refine ⟨59503304608102645597649285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39668869738735097065099523 59503304608102645597649285)
    ·
      refine ⟨11156869614019246049559241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59503304608102645597649285 11156869614019246049559241)
      ·
        refine ⟨8367652210514434537169431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11156869614019246049559241 8367652210514434537169431)
        ·
          refine ⟨12551478315771651805754147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367652210514434537169431 12551478315771651805754147)
          ·
            refine ⟨18827217473657477708631221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12551478315771651805754147 18827217473657477708631221)
            ·
              refine ⟨1765051638155388535184177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18827217473657477708631221 1765051638155388535184177)
              ·
                refine ⟨1323788728616541401388133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1765051638155388535184177 1323788728616541401388133)
                ·
                  refine ⟨248210386615601512760275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323788728616541401388133 248210386615601512760275)
                  ·
                    rfl

theorem cell21_1087623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_1087623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087623 prefixEnd_1087623 := by exact prefixLift 1087623
  have htrace : WordTrace (prefixWord ++ tailWord_1087623) baseStart_1087623 baseEnd_1087623 := by
    simpa [prefixWord, tailWord_1087623, baseEnd_1087623] using wordTrace_append hprefix tailTrace_1087623
  have hstable : (prefixWord ++ tailWord_1087623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087623).length < 2 ^ (prefixWord ++ tailWord_1087623).sum := by decide
  have hdescent : baseEnd_1087623 < baseStart_1087623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087778 : List Nat := [3, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_1087778 : Nat := 118140960795 + 1087778 * 2 ^ 59
def prefixEnd_1087778 : Nat := 4983230072969 + 3 ^ 40 * 1087778 * 2
def baseEnd_1087778 : Nat := 248245759727355687676625

theorem tailTrace_1087778 : CollatzResearch.WordTrace tailWord_1087778 prefixEnd_1087778 248245759727355687676625 := by
  unfold tailWord_1087778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918630763293389634247997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26449682035449039024661325 9918630763293389634247997)
  ·
    refine ⟨3719486536235021112842999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9918630763293389634247997 3719486536235021112842999)
    ·
      refine ⟨5579229804352531669264499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3719486536235021112842999 5579229804352531669264499)
      ·
        refine ⟨8368844706528797503896749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5579229804352531669264499 8368844706528797503896749)
        ·
          refine ⟨3138316764948299063961281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8368844706528797503896749 3138316764948299063961281)
          ·
            refine ⟨2353737573711224297970961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3138316764948299063961281 2353737573711224297970961)
            ·
              refine ⟨1765303180283418223478221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2353737573711224297970961 1765303180283418223478221)
              ·
                refine ⟨661988692606281833804333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1765303180283418223478221 661988692606281833804333)
                ·
                  refine ⟨248245759727355687676625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661988692606281833804333 248245759727355687676625)
                  ·
                    rfl

theorem cell21_1087778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_1087778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087778 prefixEnd_1087778 := by exact prefixLift 1087778
  have htrace : WordTrace (prefixWord ++ tailWord_1087778) baseStart_1087778 baseEnd_1087778 := by
    simpa [prefixWord, tailWord_1087778, baseEnd_1087778] using wordTrace_append hprefix tailTrace_1087778
  have hstable : (prefixWord ++ tailWord_1087778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087778).length < 2 ^ (prefixWord ++ tailWord_1087778).sum := by decide
  have hdescent : baseEnd_1087778 < baseStart_1087778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087809 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 4]
def baseStart_1087809 : Nat := 118140960795 + 1087809 * 2 ^ 59
def prefixEnd_1087809 : Nat := 4983230072969 + 3 ^ 40 * 1087809 * 2
def baseEnd_1087809 : Nat := 248252834349706522659895

theorem tailTrace_1087809 : CollatzResearch.WordTrace tailWord_1087809 prefixEnd_1087809 248252834349706522659895 := by
  unfold tailWord_1087809
  simp only [CollatzResearch.WordTrace]
  refine ⟨39675653716061250831370481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26450435810707500554246987 39675653716061250831370481)
  ·
    refine ⟨29756740287045938123527861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39675653716061250831370481 29756740287045938123527861)
    ·
      refine ⟨2789694401910556699080737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29756740287045938123527861 2789694401910556699080737)
      ·
        refine ⟨2092270801432917524310553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2789694401910556699080737 2092270801432917524310553)
        ·
          refine ⟨1569203101074688143232915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2092270801432917524310553 1569203101074688143232915)
          ·
            refine ⟨2353804651612032214849373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569203101074688143232915 2353804651612032214849373)
            ·
              refine ⟨882676744354512080568515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2353804651612032214849373 882676744354512080568515)
              ·
                refine ⟨1324015116531768120852773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882676744354512080568515 1324015116531768120852773)
                ·
                  refine ⟨248252834349706522659895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324015116531768120852773 248252834349706522659895)
                  ·
                    rfl

theorem cell21_1087809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_1087809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087809 prefixEnd_1087809 := by exact prefixLift 1087809
  have htrace : WordTrace (prefixWord ++ tailWord_1087809) baseStart_1087809 baseEnd_1087809 := by
    simpa [prefixWord, tailWord_1087809, baseEnd_1087809] using wordTrace_append hprefix tailTrace_1087809
  have hstable : (prefixWord ++ tailWord_1087809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087809).length < 2 ^ (prefixWord ++ tailWord_1087809).sum := by decide
  have hdescent : baseEnd_1087809 < baseStart_1087809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087879 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 7]
def baseStart_1087879 : Nat := 118140960795 + 1087879 * 2 ^ 59
def prefixEnd_1087879 : Nat := 4983230072969 + 3 ^ 40 * 1087879 * 2
def baseEnd_1087879 : Nat := 248268809303401956493085

theorem tailTrace_1087879 : CollatzResearch.WordTrace tailWord_1087879 prefixEnd_1087879 248268809303401956493085 := by
  unfold tailWord_1087879
  simp only [CollatzResearch.WordTrace]
  refine ⟨39678206825807652786418691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26452137883871768524279127 39678206825807652786418691)
  ·
    refine ⟨59517310238711479179628037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39678206825807652786418691 59517310238711479179628037)
    ·
      refine ⟨11159495669758402346180257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59517310238711479179628037 11159495669758402346180257)
      ·
        refine ⟨8369621752318801759635193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11159495669758402346180257 8369621752318801759635193)
        ·
          refine ⟨6277216314239101319726395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8369621752318801759635193 6277216314239101319726395)
          ·
            refine ⟨9415824471358651979589593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277216314239101319726395 9415824471358651979589593)
            ·
              refine ⟨7061868353518988984692195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9415824471358651979589593 7061868353518988984692195)
              ·
                refine ⟨10592802530278483477038293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7061868353518988984692195 10592802530278483477038293)
                ·
                  refine ⟨248268809303401956493085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10592802530278483477038293 248268809303401956493085)
                  ·
                    rfl

theorem cell21_1087879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_1087879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1087879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1087879 prefixEnd_1087879 := by exact prefixLift 1087879
  have htrace : WordTrace (prefixWord ++ tailWord_1087879) baseStart_1087879 baseEnd_1087879 := by
    simpa [prefixWord, tailWord_1087879, baseEnd_1087879] using wordTrace_append hprefix tailTrace_1087879
  have hstable : (prefixWord ++ tailWord_1087879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087879).length < 2 ^ (prefixWord ++ tailWord_1087879).sum := by decide
  have hdescent : baseEnd_1087879 < baseStart_1087879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088023 : List Nat := [1, 1, 3, 6, 1, 1, 3, 2, 3]
def baseStart_1088023 : Nat := 118140960795 + 1088023 * 2 ^ 59
def prefixEnd_1088023 : Nat := 4983230072969 + 3 ^ 40 * 1088023 * 2
def baseEnd_1088023 : Nat := 248301672065289706092791

theorem tailTrace_1088023 : CollatzResearch.WordTrace tailWord_1088023 prefixEnd_1088023 248301672065289706092791 := by
  unfold tailWord_1088023
  simp only [CollatzResearch.WordTrace]
  refine ⟨39683458937285965379660723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26455639291523976919773815 39683458937285965379660723)
  ·
    refine ⟨59525188405928948069491085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39683458937285965379660723 59525188405928948069491085)
    ·
      refine ⟨22321945652223355526059157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59525188405928948069491085 22321945652223355526059157)
      ·
        refine ⟨1046341202447969790284023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22321945652223355526059157 1046341202447969790284023)
        ·
          refine ⟨1569511803671954685426035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046341202447969790284023 1569511803671954685426035)
          ·
            refine ⟨2354267705507932028139053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569511803671954685426035 2354267705507932028139053)
            ·
              refine ⟨882850389565474510552145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2354267705507932028139053 882850389565474510552145)
              ·
                refine ⟨662137792174105882914109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882850389565474510552145 662137792174105882914109)
                ·
                  refine ⟨248301672065289706092791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662137792174105882914109 248301672065289706092791)
                  ·
                    rfl

theorem cell21_1088023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 3].length) (baseStart_1088023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088023 prefixEnd_1088023 := by exact prefixLift 1088023
  have htrace : WordTrace (prefixWord ++ tailWord_1088023) baseStart_1088023 baseEnd_1088023 := by
    simpa [prefixWord, tailWord_1088023, baseEnd_1088023] using wordTrace_append hprefix tailTrace_1088023
  have hstable : (prefixWord ++ tailWord_1088023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088023).length < 2 ^ (prefixWord ++ tailWord_1088023).sum := by decide
  have hdescent : baseEnd_1088023 < baseStart_1088023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088110 : List Nat := [4, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1088110 : Nat := 118140960795 + 1088110 * 2 ^ 59
def prefixEnd_1088110 : Nat := 4983230072969 + 3 ^ 40 * 1088110 * 2
def baseEnd_1088110 : Nat := 82773842216865629380871

theorem tailTrace_1088110 : CollatzResearch.WordTrace tailWord_1088110 prefixEnd_1088110 82773842216865629380871 := by
  unfold tailWord_1088110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960829010996347404759723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26457754725313852825385189 4960829010996347404759723)
  ·
    refine ⟨7441243516494521107139585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4960829010996347404759723 7441243516494521107139585)
    ·
      refine ⟨5580932637370890830354689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7441243516494521107139585 5580932637370890830354689)
      ·
        refine ⟨4185699478028168122766017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5580932637370890830354689 4185699478028168122766017)
        ·
          refine ⟨3139274608521126092074513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4185699478028168122766017 3139274608521126092074513)
          ·
            refine ⟨2354455956390844569055885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3139274608521126092074513 2354455956390844569055885)
            ·
              refine ⟨882920983646566713395957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2354455956390844569055885 882920983646566713395957)
              ·
                refine ⟨82773842216865629380871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 882920983646566713395957 82773842216865629380871)
                ·
                  rfl

theorem cell21_1088110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1088110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088110 prefixEnd_1088110 := by exact prefixLift 1088110
  have htrace : WordTrace (prefixWord ++ tailWord_1088110) baseStart_1088110 baseEnd_1088110 := by
    simpa [prefixWord, tailWord_1088110, baseEnd_1088110] using wordTrace_append hprefix tailTrace_1088110
  have hstable : (prefixWord ++ tailWord_1088110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088110).length < 2 ^ (prefixWord ++ tailWord_1088110).sum := by decide
  have hdescent : baseEnd_1088110 < baseStart_1088110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088124 : List Nat := [2, 2, 2, 1, 1, 2, 3, 5, 3]
def baseStart_1088124 : Nat := 118140960795 + 1088124 * 2 ^ 59
def prefixEnd_1088124 : Nat := 4983230072969 + 3 ^ 40 * 1088124 * 2
def baseEnd_1088124 : Nat := 248324721641335974909251

theorem tailTrace_1088124 : CollatzResearch.WordTrace tailWord_1088124 prefixEnd_1088124 248324721641335974909251 := by
  unfold tailWord_1088124
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843571354960029814543713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26458095139946706419391617 19843571354960029814543713)
  ·
    refine ⟨14882678516220022360907785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19843571354960029814543713 14882678516220022360907785)
    ·
      refine ⟨11162008887165016770680839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14882678516220022360907785 11162008887165016770680839)
      ·
        refine ⟨16743013330747525156021259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11162008887165016770680839 16743013330747525156021259)
        ·
          refine ⟨25114519996121287734031889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16743013330747525156021259 25114519996121287734031889)
          ·
            refine ⟨18835889997090965800523917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25114519996121287734031889 18835889997090965800523917)
            ·
              refine ⟨7063458748909112175196469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18835889997090965800523917 7063458748909112175196469)
              ·
                refine ⟨662199257710229266424669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7063458748909112175196469 662199257710229266424669)
                ·
                  refine ⟨248324721641335974909251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662199257710229266424669 248324721641335974909251)
                  ·
                    rfl

theorem cell21_1088124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_1088124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088124 prefixEnd_1088124 := by exact prefixLift 1088124
  have htrace : WordTrace (prefixWord ++ tailWord_1088124) baseStart_1088124 baseEnd_1088124 := by
    simpa [prefixWord, tailWord_1088124, baseEnd_1088124] using wordTrace_append hprefix tailTrace_1088124
  have hstable : (prefixWord ++ tailWord_1088124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088124).length < 2 ^ (prefixWord ++ tailWord_1088124).sum := by decide
  have hdescent : baseEnd_1088124 < baseStart_1088124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088152 : List Nat := [2, 1, 2, 4, 1, 1, 2, 8]
def baseStart_1088152 : Nat := 118140960795 + 1088152 * 2 ^ 59
def prefixEnd_1088152 : Nat := 4983230072969 + 3 ^ 40 * 1088152 * 2
def baseEnd_1088152 : Nat := 82777037207604716147509

theorem tailTrace_1088152 : CollatzResearch.WordTrace tailWord_1088152 prefixEnd_1088152 82777037207604716147509 := by
  unfold tailWord_1088152
  simp only [CollatzResearch.WordTrace]
  refine ⟨19844081976909310205553355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26458775969212413607404473 19844081976909310205553355)
  ·
    refine ⟨29766122965363965308330033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19844081976909310205553355 29766122965363965308330033)
    ·
      refine ⟨22324592224022973981247525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29766122965363965308330033 22324592224022973981247525)
      ·
        refine ⟨4185861042004307621483911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22324592224022973981247525 4185861042004307621483911)
        ·
          refine ⟨6278791563006461432225867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185861042004307621483911 6278791563006461432225867)
          ·
            refine ⟨9418187344509692148338801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6278791563006461432225867 9418187344509692148338801)
            ·
              refine ⟨7063640508382269111254101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9418187344509692148338801 7063640508382269111254101)
              ·
                refine ⟨82777037207604716147509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7063640508382269111254101 82777037207604716147509)
                ·
                  rfl

theorem cell21_1088152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_1088152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088152 prefixEnd_1088152 := by exact prefixLift 1088152
  have htrace : WordTrace (prefixWord ++ tailWord_1088152) baseStart_1088152 baseEnd_1088152 := by
    simpa [prefixWord, tailWord_1088152, baseEnd_1088152] using wordTrace_append hprefix tailTrace_1088152
  have hstable : (prefixWord ++ tailWord_1088152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088152).length < 2 ^ (prefixWord ++ tailWord_1088152).sum := by decide
  have hdescent : baseEnd_1088152 < baseStart_1088152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088200 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_1088200 : Nat := 118140960795 + 1088200 * 2 ^ 59
def prefixEnd_1088200 : Nat := 4983230072969 + 3 ^ 40 * 1088200 * 2
def baseEnd_1088200 : Nat := 248342065876776731642429

theorem tailTrace_1088200 : CollatzResearch.WordTrace tailWord_1088200 prefixEnd_1088200 248342065876776731642429 := by
  unfold tailWord_1088200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19844957328822362304427027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26459943105096483072569369 19844957328822362304427027)
  ·
    refine ⟨29767435993233543456640541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19844957328822362304427027 29767435993233543456640541)
    ·
      refine ⟨11162788497462578796240203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29767435993233543456640541 11162788497462578796240203)
      ·
        refine ⟨16744182746193868194360305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11162788497462578796240203 16744182746193868194360305)
        ·
          refine ⟨12558137059645401145770229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16744182746193868194360305 12558137059645401145770229)
          ·
            refine ⟨1177325349341756357415959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12558137059645401145770229 1177325349341756357415959)
            ·
              refine ⟨1765988024012634536123939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177325349341756357415959 1765988024012634536123939)
              ·
                refine ⟨2648982036018951804185909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765988024012634536123939 2648982036018951804185909)
                ·
                  refine ⟨248342065876776731642429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2648982036018951804185909 248342065876776731642429)
                  ·
                    rfl

theorem cell21_1088200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_1088200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088200 prefixEnd_1088200 := by exact prefixLift 1088200
  have htrace : WordTrace (prefixWord ++ tailWord_1088200) baseStart_1088200 baseEnd_1088200 := by
    simpa [prefixWord, tailWord_1088200, baseEnd_1088200] using wordTrace_append hprefix tailTrace_1088200
  have hstable : (prefixWord ++ tailWord_1088200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088200).length < 2 ^ (prefixWord ++ tailWord_1088200).sum := by decide
  have hdescent : baseEnd_1088200 < baseStart_1088200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088228 : List Nat := [2, 3, 1, 1, 1, 4, 2, 7]
def baseStart_1088228 : Nat := 118140960795 + 1088228 * 2 ^ 59
def prefixEnd_1088228 : Nat := 4983230072969 + 3 ^ 40 * 1088228 * 2
def baseEnd_1088228 : Nat := 82782818619418301725235

theorem tailTrace_1088228 : CollatzResearch.WordTrace tailWord_1088228 prefixEnd_1088228 82782818619418301725235 := by
  unfold tailWord_1088228
  simp only [CollatzResearch.WordTrace]
  refine ⟨19845467950771642695436669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26460623934362190260582225 19845467950771642695436669)
  ·
    refine ⟨7442050481539366010788751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19845467950771642695436669 7442050481539366010788751)
    ·
      refine ⟨11163075722309049016183127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7442050481539366010788751 11163075722309049016183127)
      ·
        refine ⟨16744613583463573524274691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11163075722309049016183127 16744613583463573524274691)
        ·
          refine ⟨25116920375195360286412037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16744613583463573524274691 25116920375195360286412037)
          ·
            refine ⟨4709422570349130053702257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25116920375195360286412037 4709422570349130053702257)
            ·
              refine ⟨3532066927761847540276693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4709422570349130053702257 3532066927761847540276693)
              ·
                refine ⟨82782818619418301725235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3532066927761847540276693 82782818619418301725235)
                ·
                  rfl

theorem cell21_1088228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_1088228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088228 prefixEnd_1088228 := by exact prefixLift 1088228
  have htrace : WordTrace (prefixWord ++ tailWord_1088228) baseStart_1088228 baseEnd_1088228 := by
    simpa [prefixWord, tailWord_1088228, baseEnd_1088228] using wordTrace_append hprefix tailTrace_1088228
  have hstable : (prefixWord ++ tailWord_1088228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088228).length < 2 ^ (prefixWord ++ tailWord_1088228).sum := by decide
  have hdescent : baseEnd_1088228 < baseStart_1088228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088307 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 4]
def baseStart_1088307 : Nat := 118140960795 + 1088307 * 2 ^ 59
def prefixEnd_1088307 : Nat := 4983230072969 + 3 ^ 40 * 1088307 * 2
def baseEnd_1088307 : Nat := 248366484734568323358877

theorem tailTrace_1088307 : CollatzResearch.WordTrace tailWord_1088307 prefixEnd_1088307 248366484734568323358877 := by
  unfold tailWord_1088307
  simp only [CollatzResearch.WordTrace]
  refine ⟨39693817268257081882999175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26462544845504721255332783 39693817268257081882999175)
  ·
    refine ⟨59540725902385622824498763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39693817268257081882999175 59540725902385622824498763)
    ·
      refine ⟨89311088853578434236748145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59540725902385622824498763 89311088853578434236748145)
      ·
        refine ⟨66983316640183825677561109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89311088853578434236748145 66983316640183825677561109)
        ·
          refine ⟨3139842967508616828635677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66983316640183825677561109 3139842967508616828635677)
          ·
            refine ⟨1177441112815731310738379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3139842967508616828635677 1177441112815731310738379)
            ·
              refine ⟨1766161669223596966107569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177441112815731310738379 1766161669223596966107569)
              ·
                refine ⟨1324621251917697724580677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766161669223596966107569 1324621251917697724580677)
                ·
                  refine ⟨248366484734568323358877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324621251917697724580677 248366484734568323358877)
                  ·
                    rfl

theorem cell21_1088307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4].length) (baseStart_1088307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088307 prefixEnd_1088307 := by exact prefixLift 1088307
  have htrace : WordTrace (prefixWord ++ tailWord_1088307) baseStart_1088307 baseEnd_1088307 := by
    simpa [prefixWord, tailWord_1088307, baseEnd_1088307] using wordTrace_append hprefix tailTrace_1088307
  have hstable : (prefixWord ++ tailWord_1088307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088307).length < 2 ^ (prefixWord ++ tailWord_1088307).sum := by decide
  have hdescent : baseEnd_1088307 < baseStart_1088307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088363 : List Nat := [1, 1, 1, 1, 2, 2, 13]
def baseStart_1088363 : Nat := 118140960795 + 1088363 * 2 ^ 59
def prefixEnd_1088363 : Nat := 4983230072969 + 3 ^ 40 * 1088363 * 2
def baseEnd_1088363 : Nat := 27597696077502741158381

theorem tailTrace_1088363 : CollatzResearch.WordTrace tailWord_1088363 prefixEnd_1088363 27597696077502741158381 := by
  unfold tailWord_1088363
  simp only [CollatzResearch.WordTrace]
  refine ⟨39695859756054203447037743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26463906504036135631358495 39695859756054203447037743)
  ·
    refine ⟨59543789634081305170556615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39695859756054203447037743 59543789634081305170556615)
    ·
      refine ⟨89315684451121957755834923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59543789634081305170556615 89315684451121957755834923)
      ·
        refine ⟨133973526676682936633752385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89315684451121957755834923 133973526676682936633752385)
        ·
          refine ⟨100480145007512202475314289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133973526676682936633752385 100480145007512202475314289)
          ·
            refine ⟨75360108755634151856485717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100480145007512202475314289 75360108755634151856485717)
            ·
              refine ⟨27597696077502741158381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 75360108755634151856485717 27597696077502741158381)
              ·
                rfl

theorem cell21_1088363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 13].length) (baseStart_1088363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088363 prefixEnd_1088363 := by exact prefixLift 1088363
  have htrace : WordTrace (prefixWord ++ tailWord_1088363) baseStart_1088363 baseEnd_1088363 := by
    simpa [prefixWord, tailWord_1088363, baseEnd_1088363] using wordTrace_append hprefix tailTrace_1088363
  have hstable : (prefixWord ++ tailWord_1088363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088363).length < 2 ^ (prefixWord ++ tailWord_1088363).sum := by decide
  have hdescent : baseEnd_1088363 < baseStart_1088363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088369 : List Nat := [1, 2, 2, 2, 1, 5, 3, 2, 3]
def baseStart_1088369 : Nat := 118140960795 + 1088369 * 2 ^ 59
def prefixEnd_1088369 : Nat := 4983230072969 + 3 ^ 40 * 1088369 * 2
def baseEnd_1088369 : Nat := 248380633979269993325417

theorem tailTrace_1088369 : CollatzResearch.WordTrace tailWord_1088369 prefixEnd_1088369 248380633979269993325417 := by
  unfold tailWord_1088369
  simp only [CollatzResearch.WordTrace]
  refine ⟨39696078594032466471756161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26464052396021644314504107 39696078594032466471756161)
  ·
    refine ⟨29772058945524349853817121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39696078594032466471756161 29772058945524349853817121)
    ·
      refine ⟨22329044209143262390362841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29772058945524349853817121 22329044209143262390362841)
      ·
        refine ⟨16746783156857446792772131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22329044209143262390362841 16746783156857446792772131)
        ·
          refine ⟨25120174735286170189158197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16746783156857446792772131 25120174735286170189158197)
          ·
            refine ⟨2355016381433078455233581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25120174735286170189158197 2355016381433078455233581)
            ·
              refine ⟨883131143037404420712593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355016381433078455233581 883131143037404420712593)
              ·
                refine ⟨662348357278053315534445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883131143037404420712593 662348357278053315534445)
                ·
                  refine ⟨248380633979269993325417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662348357278053315534445 248380633979269993325417)
                  ·
                    rfl

theorem cell21_1088369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_1088369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088369 prefixEnd_1088369 := by exact prefixLift 1088369
  have htrace : WordTrace (prefixWord ++ tailWord_1088369) baseStart_1088369 baseEnd_1088369 := by
    simpa [prefixWord, tailWord_1088369, baseEnd_1088369] using wordTrace_append hprefix tailTrace_1088369
  have hstable : (prefixWord ++ tailWord_1088369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088369).length < 2 ^ (prefixWord ++ tailWord_1088369).sum := by decide
  have hdescent : baseEnd_1088369 < baseStart_1088369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088487 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 5]
def baseStart_1088487 : Nat := 118140960795 + 1088487 * 2 ^ 59
def prefixEnd_1088487 : Nat := 4983230072969 + 3 ^ 40 * 1088487 * 2
def baseEnd_1088487 : Nat := 248407563186928010358509

theorem tailTrace_1088487 : CollatzResearch.WordTrace tailWord_1088487 prefixEnd_1088487 248407563186928010358509 := by
  unfold tailWord_1088487
  simp only [CollatzResearch.WordTrace]
  refine ⟨39700382407604972624551715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26466921605069981749701143 39700382407604972624551715)
  ·
    refine ⟨59550573611407458936827573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39700382407604972624551715 59550573611407458936827573)
    ·
      refine ⟨5582866276069449275327585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59550573611407458936827573 5582866276069449275327585)
      ·
        refine ⟨4187149707052086956495689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5582866276069449275327585 4187149707052086956495689)
        ·
          refine ⟨3140362280289065217371767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4187149707052086956495689 3140362280289065217371767)
          ·
            refine ⟨4710543420433597826057651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140362280289065217371767 4710543420433597826057651)
            ·
              refine ⟨7065815130650396739086477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4710543420433597826057651 7065815130650396739086477)
              ·
                refine ⟨2649680673993898777157429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7065815130650396739086477 2649680673993898777157429)
                ·
                  refine ⟨248407563186928010358509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2649680673993898777157429 248407563186928010358509)
                  ·
                    rfl

theorem cell21_1088487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_1088487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088487 prefixEnd_1088487 := by exact prefixLift 1088487
  have htrace : WordTrace (prefixWord ++ tailWord_1088487) baseStart_1088487 baseEnd_1088487 := by
    simpa [prefixWord, tailWord_1088487, baseEnd_1088487] using wordTrace_append hprefix tailTrace_1088487
  have hstable : (prefixWord ++ tailWord_1088487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088487).length < 2 ^ (prefixWord ++ tailWord_1088487).sum := by decide
  have hdescent : baseEnd_1088487 < baseStart_1088487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088594 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_1088594 : Nat := 118140960795 + 1088594 * 2 ^ 59
def prefixEnd_1088594 : Nat := 4983230072969 + 3 ^ 40 * 1088594 * 2
def baseEnd_1088594 : Nat := 248431982044719602074957

theorem tailTrace_1088594 : CollatzResearch.WordTrace tailWord_1088594 prefixEnd_1088594 248431982044719602074957 := by
  unfold tailWord_1088594
  simp only [CollatzResearch.WordTrace]
  refine ⟨9926071254554332474674209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26469523345478219932464557 9926071254554332474674209)
  ·
    refine ⟨7444553440915749356005657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9926071254554332474674209 7444553440915749356005657)
    ·
      refine ⟨5583415080686812017004243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7444553440915749356005657 5583415080686812017004243)
      ·
        refine ⟨8375122621030218025506365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5583415080686812017004243 8375122621030218025506365)
        ·
          refine ⟨3140670982886331759564887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8375122621030218025506365 3140670982886331759564887)
          ·
            refine ⟨4711006474329497639347331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140670982886331759564887 4711006474329497639347331)
            ·
              refine ⟨7066509711494246459020997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711006474329497639347331 7066509711494246459020997)
              ·
                refine ⟨1324970570905171211066437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7066509711494246459020997 1324970570905171211066437)
                ·
                  refine ⟨248431982044719602074957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324970570905171211066437 248431982044719602074957)
                  ·
                    rfl

theorem cell21_1088594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_1088594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088594 prefixEnd_1088594 := by exact prefixLift 1088594
  have htrace : WordTrace (prefixWord ++ tailWord_1088594) baseStart_1088594 baseEnd_1088594 := by
    simpa [prefixWord, tailWord_1088594, baseEnd_1088594] using wordTrace_append hprefix tailTrace_1088594
  have hstable : (prefixWord ++ tailWord_1088594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088594).length < 2 ^ (prefixWord ++ tailWord_1088594).sum := by decide
  have hdescent : baseEnd_1088594 < baseStart_1088594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088766 : List Nat := [4, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1088766 : Nat := 118140960795 + 1088766 * 2 ^ 59
def prefixEnd_1088766 : Nat := 4983230072969 + 3 ^ 40 * 1088766 * 2
def baseEnd_1088766 : Nat := 248471234788085525207939

theorem tailTrace_1088766 : CollatzResearch.WordTrace tailWord_1088766 prefixEnd_1088766 248471234788085525207939 := by
  unfold tailWord_1088766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4963819796699275409244769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26473705582396135515972101 4963819796699275409244769)
  ·
    refine ⟨3722864847524456556933577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4963819796699275409244769 3722864847524456556933577)
    ·
      refine ⟨2792148635643342417700183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3722864847524456556933577 2792148635643342417700183)
      ·
        refine ⟨4188222953465013626550275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2792148635643342417700183 4188222953465013626550275)
        ·
          refine ⟨6282334430197520439825413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4188222953465013626550275 6282334430197520439825413)
          ·
            refine ⟨1177937705662035082467265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6282334430197520439825413 1177937705662035082467265)
            ·
              refine ⟨883453279246526311850449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177937705662035082467265 883453279246526311850449)
              ·
                refine ⟨662589959434894733887837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883453279246526311850449 662589959434894733887837)
                ·
                  refine ⟨248471234788085525207939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662589959434894733887837 248471234788085525207939)
                  ·
                    rfl

theorem cell21_1088766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1088766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088766 prefixEnd_1088766 := by exact prefixLift 1088766
  have htrace : WordTrace (prefixWord ++ tailWord_1088766) baseStart_1088766 baseEnd_1088766 := by
    simpa [prefixWord, tailWord_1088766, baseEnd_1088766] using wordTrace_append hprefix tailTrace_1088766
  have hstable : (prefixWord ++ tailWord_1088766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088766).length < 2 ^ (prefixWord ++ tailWord_1088766).sum := by decide
  have hdescent : baseEnd_1088766 < baseStart_1088766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088808 : List Nat := [2, 1, 5, 1, 2, 1, 1, 5, 3]
def baseStart_1088808 : Nat := 118140960795 + 1088808 * 2 ^ 59
def prefixEnd_1088808 : Nat := 4983230072969 + 3 ^ 40 * 1088808 * 2
def baseEnd_1088808 : Nat := 248480819760302785507853

theorem tailTrace_1088808 : CollatzResearch.WordTrace tailWord_1088808 prefixEnd_1088808 248480819760302785507853 := by
  unfold tailWord_1088808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19856045119721022223493539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26474726826294696297991385 19856045119721022223493539)
  ·
    refine ⟨29784067679581533335240309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19856045119721022223493539 29784067679581533335240309)
    ·
      refine ⟨2792256344960768750178779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29784067679581533335240309 2792256344960768750178779)
      ·
        refine ⟨4188384517441153125268169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2792256344960768750178779 4188384517441153125268169)
        ·
          refine ⟨3141288388080864843951127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4188384517441153125268169 3141288388080864843951127)
          ·
            refine ⟨4711932582121297265926691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141288388080864843951127 4711932582121297265926691)
            ·
              refine ⟨7067898873181945898890037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711932582121297265926691 7067898873181945898890037)
              ·
                refine ⟨662615519360807428020941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7067898873181945898890037 662615519360807428020941)
                ·
                  refine ⟨248480819760302785507853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662615519360807428020941 248480819760302785507853)
                  ·
                    rfl

theorem cell21_1088808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_1088808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088808 prefixEnd_1088808 := by exact prefixLift 1088808
  have htrace : WordTrace (prefixWord ++ tailWord_1088808) baseStart_1088808 baseEnd_1088808 := by
    simpa [prefixWord, tailWord_1088808, baseEnd_1088808] using wordTrace_append hprefix tailTrace_1088808
  have hstable : (prefixWord ++ tailWord_1088808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088808).length < 2 ^ (prefixWord ++ tailWord_1088808).sum := by decide
  have hdescent : baseEnd_1088808 < baseStart_1088808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088819 : List Nat := [1, 1, 1, 2, 5, 3, 8]
def baseStart_1088819 : Nat := 118140960795 + 1088819 * 2 ^ 59
def prefixEnd_1088819 : Nat := 4983230072969 + 3 ^ 40 * 1088819 * 2
def baseEnd_1088819 : Nat := 27609258901129912313833

theorem tailTrace_1088819 : CollatzResearch.WordTrace tailWord_1088819 prefixEnd_1088819 27609258901129912313833 := by
  unfold tailWord_1088819
  simp only [CollatzResearch.WordTrace]
  refine ⟨39712491442402193325637511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26474994294934795550425007 39712491442402193325637511)
  ·
    refine ⟨59568737163603289988456267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39712491442402193325637511 59568737163603289988456267)
    ·
      refine ⟨89353105745404934982684401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59568737163603289988456267 89353105745404934982684401)
      ·
        refine ⟨67014829309053701237013301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89353105745404934982684401 67014829309053701237013301)
        ·
          refine ⟨6282640247723784490969997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67014829309053701237013301 6282640247723784490969997)
          ·
            refine ⟨2355990092896419184113749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6282640247723784490969997 2355990092896419184113749)
            ·
              refine ⟨27609258901129912313833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2355990092896419184113749 27609258901129912313833)
              ·
                rfl

theorem cell21_1088819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 8].length) (baseStart_1088819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088819 prefixEnd_1088819 := by exact prefixLift 1088819
  have htrace : WordTrace (prefixWord ++ tailWord_1088819) baseStart_1088819 baseEnd_1088819 := by
    simpa [prefixWord, tailWord_1088819, baseEnd_1088819] using wordTrace_append hprefix tailTrace_1088819
  have hstable : (prefixWord ++ tailWord_1088819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088819).length < 2 ^ (prefixWord ++ tailWord_1088819).sum := by decide
  have hdescent : baseEnd_1088819 < baseStart_1088819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088853 : List Nat := [1, 3, 2, 2, 3, 3, 2, 5]
def baseStart_1088853 : Nat := 118140960795 + 1088853 * 2 ^ 59
def prefixEnd_1088853 : Nat := 4983230072969 + 3 ^ 40 * 1088853 * 2
def baseEnd_1088853 : Nat := 82830363124464235752587

theorem tailTrace_1088853 : CollatzResearch.WordTrace tailWord_1088853 prefixEnd_1088853 82830363124464235752587 := by
  unfold tailWord_1088853
  simp only [CollatzResearch.WordTrace]
  refine ⟨39713731524279017132375213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26475821016186011421583475 39713731524279017132375213)
  ·
    refine ⟨14892649321604631424640705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39713731524279017132375213 14892649321604631424640705)
    ·
      refine ⟨11169486991203473568480529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14892649321604631424640705 11169486991203473568480529)
      ·
        refine ⟨8377115243402605176360397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11169486991203473568480529 8377115243402605176360397)
        ·
          refine ⟨3141418216275976941135149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8377115243402605176360397 3141418216275976941135149)
          ·
            refine ⟨1178031831103491352925681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3141418216275976941135149 1178031831103491352925681)
            ·
              refine ⟨883523873327618514694261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178031831103491352925681 883523873327618514694261)
              ·
                refine ⟨82830363124464235752587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883523873327618514694261 82830363124464235752587)
                ·
                  rfl

theorem cell21_1088853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 5].length) (baseStart_1088853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088853 prefixEnd_1088853 := by exact prefixLift 1088853
  have htrace : WordTrace (prefixWord ++ tailWord_1088853) baseStart_1088853 baseEnd_1088853 := by
    simpa [prefixWord, tailWord_1088853, baseEnd_1088853] using wordTrace_append hprefix tailTrace_1088853
  have hstable : (prefixWord ++ tailWord_1088853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088853).length < 2 ^ (prefixWord ++ tailWord_1088853).sum := by decide
  have hdescent : baseEnd_1088853 < baseStart_1088853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088940 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1088940 : Nat := 118140960795 + 1088940 * 2 ^ 59
def prefixEnd_1088940 : Nat := 4983230072969 + 3 ^ 40 * 1088940 * 2
def baseEnd_1088940 : Nat := 248510943958699889307583

theorem tailTrace_1088940 : CollatzResearch.WordTrace tailWord_1088940 prefixEnd_1088940 248510943958699889307583 := by
  unfold tailWord_1088940
  simp only [CollatzResearch.WordTrace]
  refine ⟨19858452337481915495396137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26477936449975887327194849 19858452337481915495396137)
  ·
    refine ⟨14893839253111436621547103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19858452337481915495396137 14893839253111436621547103)
    ·
      refine ⟨22340758879667154932320655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14893839253111436621547103 22340758879667154932320655)
      ·
        refine ⟨33511138319500732398480983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22340758879667154932320655 33511138319500732398480983)
        ·
          refine ⟨50266707479251098597721475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33511138319500732398480983 50266707479251098597721475)
          ·
            refine ⟨75400061218876647896582213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50266707479251098597721475 75400061218876647896582213)
            ·
              refine ⟨14137511478539371480609165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75400061218876647896582213 14137511478539371480609165)
              ·
                refine ⟨5301566804452264305228437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14137511478539371480609165 5301566804452264305228437)
                ·
                  refine ⟨248510943958699889307583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5301566804452264305228437 248510943958699889307583)
                  ·
                    rfl

theorem cell21_1088940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1088940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088940 prefixEnd_1088940 := by exact prefixLift 1088940
  have htrace : WordTrace (prefixWord ++ tailWord_1088940) baseStart_1088940 baseEnd_1088940 := by
    simpa [prefixWord, tailWord_1088940, baseEnd_1088940] using wordTrace_append hprefix tailTrace_1088940
  have hstable : (prefixWord ++ tailWord_1088940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088940).length < 2 ^ (prefixWord ++ tailWord_1088940).sum := by decide
  have hdescent : baseEnd_1088940 < baseStart_1088940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088957 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1088957 : Nat := 118140960795 + 1088957 * 2 ^ 59
def prefixEnd_1088957 : Nat := 4983230072969 + 3 ^ 40 * 1088957 * 2
def baseEnd_1088957 : Nat := 248514823590311637524215

theorem tailTrace_1088957 : CollatzResearch.WordTrace tailWord_1088957 prefixEnd_1088957 248514823590311637524215 := by
  unfold tailWord_1088957
  simp only [CollatzResearch.WordTrace]
  refine ⟨39717524715902242894161125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26478349810601495262774083 39717524715902242894161125)
  ·
    refine ⟨7447035884231670542655211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39717524715902242894161125 7447035884231670542655211)
    ·
      refine ⟨11170553826347505813982817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7447035884231670542655211 11170553826347505813982817)
      ·
        refine ⟨8377915369760629360487113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11170553826347505813982817 8377915369760629360487113)
        ·
          refine ⟨6283436527320472020365335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8377915369760629360487113 6283436527320472020365335)
          ·
            refine ⟨9425154790980708030548003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6283436527320472020365335 9425154790980708030548003)
            ·
              refine ⟨14137732186471062045822005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9425154790980708030548003 14137732186471062045822005)
              ·
                refine ⟨1325412392481662066795813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14137732186471062045822005 1325412392481662066795813)
                ·
                  refine ⟨248514823590311637524215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1325412392481662066795813 248514823590311637524215)
                  ·
                    rfl

theorem cell21_1088957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1088957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1088957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1088957 prefixEnd_1088957 := by exact prefixLift 1088957
  have htrace : WordTrace (prefixWord ++ tailWord_1088957) baseStart_1088957 baseEnd_1088957 := by
    simpa [prefixWord, tailWord_1088957, baseEnd_1088957] using wordTrace_append hprefix tailTrace_1088957
  have hstable : (prefixWord ++ tailWord_1088957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088957).length < 2 ^ (prefixWord ++ tailWord_1088957).sum := by decide
  have hdescent : baseEnd_1088957 < baseStart_1088957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089123 : List Nat := [1, 1, 1, 5, 1, 3, 3, 6]
def baseStart_1089123 : Nat := 118140960795 + 1089123 * 2 ^ 59
def prefixEnd_1089123 : Nat := 4983230072969 + 3 ^ 40 * 1089123 * 2
def baseEnd_1089123 : Nat := 82850902350644079252403

theorem tailTrace_1089123 : CollatzResearch.WordTrace tailWord_1089123 prefixEnd_1089123 82850902350644079252403 := by
  unfold tailWord_1089123
  simp only [CollatzResearch.WordTrace]
  refine ⟨39723579233300853244704023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26482386155533902163136015 39723579233300853244704023)
  ·
    refine ⟨59585368849951279867056035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39723579233300853244704023 59585368849951279867056035)
    ·
      refine ⟨89378053274926919800584053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59585368849951279867056035 89378053274926919800584053)
      ·
        refine ⟨8379192494524398731304755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89378053274926919800584053 8379192494524398731304755)
        ·
          refine ⟨12568788741786598096957133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379192494524398731304755 12568788741786598096957133)
          ·
            refine ⟨4713295778169974286358925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12568788741786598096957133 4713295778169974286358925)
            ·
              refine ⟨1767485916813740357384597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4713295778169974286358925 1767485916813740357384597)
              ·
                refine ⟨82850902350644079252403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1767485916813740357384597 82850902350644079252403)
                ·
                  rfl

theorem cell21_1089123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 6].length) (baseStart_1089123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089123 prefixEnd_1089123 := by exact prefixLift 1089123
  have htrace : WordTrace (prefixWord ++ tailWord_1089123) baseStart_1089123 baseEnd_1089123 := by
    simpa [prefixWord, tailWord_1089123, baseEnd_1089123] using wordTrace_append hprefix tailTrace_1089123
  have hstable : (prefixWord ++ tailWord_1089123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089123).length < 2 ^ (prefixWord ++ tailWord_1089123).sum := by decide
  have hdescent : baseEnd_1089123 < baseStart_1089123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089160 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 4]
def baseStart_1089160 : Nat := 118140960795 + 1089160 * 2 ^ 59
def prefixEnd_1089160 : Nat := 4983230072969 + 3 ^ 40 * 1089160 * 2
def baseEnd_1089160 : Nat := 248561150956028395640467

theorem tailTrace_1089160 : CollatzResearch.WordTrace tailWord_1089160 prefixEnd_1089160 248561150956028395640467 := by
  unfold tailWord_1089160
  simp only [CollatzResearch.WordTrace]
  refine ⟨19862464367083404281900467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26483285822777872375867289 19862464367083404281900467)
  ·
    refine ⟨29793696550625106422850701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19862464367083404281900467 29793696550625106422850701)
    ·
      refine ⟨11172636206484414908569013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29793696550625106422850701 11172636206484414908569013)
      ·
        refine ⟨1047434644357913897678345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11172636206484414908569013 1047434644357913897678345)
        ·
          refine ⟨785575983268435423258759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1047434644357913897678345 785575983268435423258759)
          ·
            refine ⟨1178363974902653134888139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785575983268435423258759 1178363974902653134888139)
            ·
              refine ⟨1767545962353979702332209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178363974902653134888139 1767545962353979702332209)
              ·
                refine ⟨1325659471765484776749157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767545962353979702332209 1325659471765484776749157)
                ·
                  refine ⟨248561150956028395640467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1325659471765484776749157 248561150956028395640467)
                  ·
                    rfl

theorem cell21_1089160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_1089160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089160 prefixEnd_1089160 := by exact prefixLift 1089160
  have htrace : WordTrace (prefixWord ++ tailWord_1089160) baseStart_1089160 baseEnd_1089160 := by
    simpa [prefixWord, tailWord_1089160, baseEnd_1089160] using wordTrace_append hprefix tailTrace_1089160
  have hstable : (prefixWord ++ tailWord_1089160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089160).length < 2 ^ (prefixWord ++ tailWord_1089160).sum := by decide
  have hdescent : baseEnd_1089160 < baseStart_1089160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089205 : List Nat := [1, 3, 3, 3, 2, 2, 1, 3, 3]
def baseStart_1089205 : Nat := 118140960795 + 1089205 * 2 ^ 59
def prefixEnd_1089205 : Nat := 4983230072969 + 3 ^ 40 * 1089205 * 2
def baseEnd_1089205 : Nat := 248571420569118317390375

theorem tailTrace_1089205 : CollatzResearch.WordTrace tailWord_1089205 prefixEnd_1089205 248571420569118317390375 := by
  unfold tailWord_1089205
  simp only [CollatzResearch.WordTrace]
  refine ⟨39726570019003781249189069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26484380012669187499459379 39726570019003781249189069)
  ·
    refine ⟨14897463757126417968445901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39726570019003781249189069 14897463757126417968445901)
    ·
      refine ⟨5586548908922406738167213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14897463757126417968445901 5586548908922406738167213)
      ·
        refine ⟨2094955840845902526812705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5586548908922406738167213 2094955840845902526812705)
        ·
          refine ⟨1571216880634426895109529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2094955840845902526812705 1571216880634426895109529)
          ·
            refine ⟨1178412660475820171332147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1571216880634426895109529 1178412660475820171332147)
            ·
              refine ⟨1767618990713730256998221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178412660475820171332147 1767618990713730256998221)
              ·
                refine ⟨662857121517648846374333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1767618990713730256998221 662857121517648846374333)
                ·
                  refine ⟨248571420569118317390375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 662857121517648846374333 248571420569118317390375)
                  ·
                    rfl

theorem cell21_1089205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_1089205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089205 prefixEnd_1089205 := by exact prefixLift 1089205
  have htrace : WordTrace (prefixWord ++ tailWord_1089205) baseStart_1089205 baseEnd_1089205 := by
    simpa [prefixWord, tailWord_1089205, baseEnd_1089205] using wordTrace_append hprefix tailTrace_1089205
  have hstable : (prefixWord ++ tailWord_1089205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089205).length < 2 ^ (prefixWord ++ tailWord_1089205).sum := by decide
  have hdescent : baseEnd_1089205 < baseStart_1089205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089289 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 5]
def baseStart_1089289 : Nat := 118140960795 + 1089289 * 2 ^ 59
def prefixEnd_1089289 : Nat := 4983230072969 + 3 ^ 40 * 1089289 * 2
def baseEnd_1089289 : Nat := 248590590513552837990203

theorem tailTrace_1089289 : CollatzResearch.WordTrace tailWord_1089289 prefixEnd_1089289 248590590513552837990203 := by
  unfold tailWord_1089289
  simp only [CollatzResearch.WordTrace]
  refine ⟨39729633750699463595246921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26486422500466309063497947 39729633750699463595246921)
  ·
    refine ⟨29797225313024597696435191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39729633750699463595246921 29797225313024597696435191)
    ·
      refine ⟨44695837969536896544652787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29797225313024597696435191 44695837969536896544652787)
      ·
        refine ⟨67043756954305344816979181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44695837969536896544652787 67043756954305344816979181)
        ·
          refine ⟨25141408857864504306367193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67043756954305344816979181 25141408857864504306367193)
          ·
            refine ⟨18856056643398378229775395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25141408857864504306367193 18856056643398378229775395)
            ·
              refine ⟨28284084965097567344663093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18856056643398378229775395 28284084965097567344663093)
              ·
                refine ⟨2651632965477896938562165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28284084965097567344663093 2651632965477896938562165)
                ·
                  refine ⟨248590590513552837990203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2651632965477896938562165 248590590513552837990203)
                  ·
                    rfl

theorem cell21_1089289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_1089289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089289 prefixEnd_1089289 := by exact prefixLift 1089289
  have htrace : WordTrace (prefixWord ++ tailWord_1089289) baseStart_1089289 baseEnd_1089289 := by
    simpa [prefixWord, tailWord_1089289, baseEnd_1089289] using wordTrace_append hprefix tailTrace_1089289
  have hstable : (prefixWord ++ tailWord_1089289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089289).length < 2 ^ (prefixWord ++ tailWord_1089289).sum := by decide
  have hdescent : baseEnd_1089289 < baseStart_1089289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089306 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_1089306 : Nat := 118140960795 + 1089306 * 2 ^ 59
def prefixEnd_1089306 : Nat := 4983230072969 + 3 ^ 40 * 1089306 * 2
def baseEnd_1089306 : Nat := 248594470145164586206835

theorem tailTrace_1089306 : CollatzResearch.WordTrace tailWord_1089306 prefixEnd_1089306 248594470145164586206835 := by
  unfold tailWord_1089306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9932563447909468874653943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26486835861091916999077181 9932563447909468874653943)
  ·
    refine ⟨14898845171864203311980915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9932563447909468874653943 14898845171864203311980915)
    ·
      refine ⟨22348267757796304967971373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14898845171864203311980915 22348267757796304967971373)
      ·
        refine ⟨8380600409173614362989265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22348267757796304967971373 8380600409173614362989265)
        ·
          refine ⟨6285450306880210772241949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8380600409173614362989265 6285450306880210772241949)
          ·
            refine ⟨2357043865080079039590731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6285450306880210772241949 2357043865080079039590731)
            ·
              refine ⟨3535565797620118559386097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357043865080079039590731 3535565797620118559386097)
              ·
                refine ⟨2651674348215088919539573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535565797620118559386097 2651674348215088919539573)
                ·
                  refine ⟨248594470145164586206835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2651674348215088919539573 248594470145164586206835)
                  ·
                    rfl

theorem cell21_1089306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_1089306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089306 prefixEnd_1089306 := by exact prefixLift 1089306
  have htrace : WordTrace (prefixWord ++ tailWord_1089306) baseStart_1089306 baseEnd_1089306 := by
    simpa [prefixWord, tailWord_1089306, baseEnd_1089306] using wordTrace_append hprefix tailTrace_1089306
  have hstable : (prefixWord ++ tailWord_1089306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089306).length < 2 ^ (prefixWord ++ tailWord_1089306).sum := by decide
  have hdescent : baseEnd_1089306 < baseStart_1089306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089472 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_1089472 : Nat := 118140960795 + 1089472 * 2 ^ 59
def prefixEnd_1089472 : Nat := 4983230072969 + 3 ^ 40 * 1089472 * 2
def baseEnd_1089472 : Nat := 248632353606785186439829

theorem tailTrace_1089472 : CollatzResearch.WordTrace tailWord_1089472 prefixEnd_1089472 248632353606785186439829 := by
  unfold tailWord_1089472
  simp only [CollatzResearch.WordTrace]
  refine ⟨19868154154518242924579335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26490872206024323899439113 19868154154518242924579335)
  ·
    refine ⟨29802231231777364386869003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19868154154518242924579335 29802231231777364386869003)
    ·
      refine ⟨44703346847666046580303505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29802231231777364386869003 44703346847666046580303505)
      ·
        refine ⟨33527510135749534935227629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44703346847666046580303505 33527510135749534935227629)
        ·
          refine ⟨12572816300906075600710361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33527510135749534935227629 12572816300906075600710361)
          ·
            refine ⟨9429612225679556700532771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12572816300906075600710361 9429612225679556700532771)
            ·
              refine ⟨14144418338519335050799157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9429612225679556700532771 14144418338519335050799157)
              ·
                refine ⟨1326039219236187661012421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14144418338519335050799157 1326039219236187661012421)
                ·
                  refine ⟨248632353606785186439829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1326039219236187661012421 248632353606785186439829)
                  ·
                    rfl

theorem cell21_1089472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_1089472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089472 prefixEnd_1089472 := by exact prefixLift 1089472
  have htrace : WordTrace (prefixWord ++ tailWord_1089472) baseStart_1089472 baseEnd_1089472 := by
    simpa [prefixWord, tailWord_1089472, baseEnd_1089472] using wordTrace_append hprefix tailTrace_1089472
  have hstable : (prefixWord ++ tailWord_1089472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089472).length < 2 ^ (prefixWord ++ tailWord_1089472).sum := by decide
  have hdescent : baseEnd_1089472 < baseStart_1089472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089506 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1089506 : Nat := 118140960795 + 1089506 * 2 ^ 59
def prefixEnd_1089506 : Nat := 4983230072969 + 3 ^ 40 * 1089506 * 2
def baseEnd_1089506 : Nat := 248640112870008682873093

theorem tailTrace_1089506 : CollatzResearch.WordTrace tailWord_1089506 prefixEnd_1089506 248640112870008682873093 := by
  unfold tailWord_1089506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9934387097728327413974093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26491698927275539770597581 9934387097728327413974093)
  ·
    refine ⟨3725395161648122780240285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9934387097728327413974093 3725395161648122780240285)
    ·
      refine ⟨1397023185618046042590107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3725395161648122780240285 1397023185618046042590107)
      ·
        refine ⟨2095534778427069063885161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397023185618046042590107 2095534778427069063885161)
        ·
          refine ⟨1571651083820301797913871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095534778427069063885161 1571651083820301797913871)
          ·
            refine ⟨2357476625730452696870807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571651083820301797913871 2357476625730452696870807)
            ·
              refine ⟨3536214938595679045306211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357476625730452696870807 3536214938595679045306211)
              ·
                refine ⟨5304322407893518567959317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3536214938595679045306211 5304322407893518567959317)
                ·
                  refine ⟨248640112870008682873093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5304322407893518567959317 248640112870008682873093)
                  ·
                    rfl

theorem cell21_1089506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1089506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089506 prefixEnd_1089506 := by exact prefixLift 1089506
  have htrace : WordTrace (prefixWord ++ tailWord_1089506) baseStart_1089506 baseEnd_1089506 := by
    simpa [prefixWord, tailWord_1089506, baseEnd_1089506] using wordTrace_append hprefix tailTrace_1089506
  have hstable : (prefixWord ++ tailWord_1089506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089506).length < 2 ^ (prefixWord ++ tailWord_1089506).sum := by decide
  have hdescent : baseEnd_1089506 < baseStart_1089506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089562 : List Nat := [3, 1, 1, 3, 1, 3, 9]
def baseStart_1089562 : Nat := 118140960795 + 1089562 * 2 ^ 59
def prefixEnd_1089562 : Nat := 4983230072969 + 3 ^ 40 * 1089562 * 2
def baseEnd_1089562 : Nat := 27628099203662781104405

theorem tailTrace_1089562 : CollatzResearch.WordTrace tailWord_1089562 prefixEnd_1089562 27628099203662781104405 := by
  unfold tailWord_1089562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9934897719677607804983735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26493060585806954146623293 9934897719677607804983735)
  ·
    refine ⟨14902346579516411707475603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9934897719677607804983735 14902346579516411707475603)
    ·
      refine ⟨22353519869274617561213405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14902346579516411707475603 22353519869274617561213405)
      ·
        refine ⟨8382569950977981585455027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22353519869274617561213405 8382569950977981585455027)
        ·
          refine ⟨12573854926466972378182541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8382569950977981585455027 12573854926466972378182541)
          ·
            refine ⟨4715195597425114641818453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12573854926466972378182541 4715195597425114641818453)
            ·
              refine ⟨27628099203662781104405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4715195597425114641818453 27628099203662781104405)
              ·
                rfl

theorem cell21_1089562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 9].length) (baseStart_1089562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089562 prefixEnd_1089562 := by exact prefixLift 1089562
  have htrace : WordTrace (prefixWord ++ tailWord_1089562) baseStart_1089562 baseEnd_1089562 := by
    simpa [prefixWord, tailWord_1089562, baseEnd_1089562] using wordTrace_append hprefix tailTrace_1089562
  have hstable : (prefixWord ++ tailWord_1089562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089562).length < 2 ^ (prefixWord ++ tailWord_1089562).sum := by decide
  have hdescent : baseEnd_1089562 < baseStart_1089562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089582 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1089582 : Nat := 118140960795 + 1089582 * 2 ^ 59
def prefixEnd_1089582 : Nat := 4983230072969 + 3 ^ 40 * 1089582 * 2
def baseEnd_1089582 : Nat := 248657457105449439606271

theorem tailTrace_1089582 : CollatzResearch.WordTrace tailWord_1089582 prefixEnd_1089582 248657457105449439606271 := by
  unfold tailWord_1089582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4967540042329746829457875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26493546892425316423775333 4967540042329746829457875)
  ·
    refine ⟨7451310063494620244186813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4967540042329746829457875 7451310063494620244186813)
    ·
      refine ⟨2794241273810482591570055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7451310063494620244186813 2794241273810482591570055)
      ·
        refine ⟨4191361910715723887355083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794241273810482591570055 4191361910715723887355083)
        ·
          refine ⟨6287042866073585831032625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191361910715723887355083 6287042866073585831032625)
          ·
            refine ⟨4715282149555189373274469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6287042866073585831032625 4715282149555189373274469)
            ·
              refine ⟨884115403041598007488963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4715282149555189373274469 884115403041598007488963)
              ·
                refine ⟨1326173104562397011233445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884115403041598007488963 1326173104562397011233445)
                ·
                  refine ⟨248657457105449439606271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1326173104562397011233445 248657457105449439606271)
                  ·
                    rfl

theorem cell21_1089582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1089582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089582 prefixEnd_1089582 := by exact prefixLift 1089582
  have htrace : WordTrace (prefixWord ++ tailWord_1089582) baseStart_1089582 baseEnd_1089582 := by
    simpa [prefixWord, tailWord_1089582, baseEnd_1089582] using wordTrace_append hprefix tailTrace_1089582
  have hstable : (prefixWord ++ tailWord_1089582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089582).length < 2 ^ (prefixWord ++ tailWord_1089582).sum := by decide
  have hdescent : baseEnd_1089582 < baseStart_1089582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089610 : List Nat := [3, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_1089610 : Nat := 118140960795 + 1089610 * 2 ^ 59
def prefixEnd_1089610 : Nat := 4983230072969 + 3 ^ 40 * 1089610 * 2
def baseEnd_1089610 : Nat := 248663847086927613139547

theorem tailTrace_1089610 : CollatzResearch.WordTrace tailWord_1089610 prefixEnd_1089610 248663847086927613139547 := by
  unfold tailWord_1089610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9935335395634133854420571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26494227721691023611788189 9935335395634133854420571)
  ·
    refine ⟨14903003093451200781630857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9935335395634133854420571 14903003093451200781630857)
    ·
      refine ⟨11177252320088400586223143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14903003093451200781630857 11177252320088400586223143)
      ·
        refine ⟨16765878480132600879334715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11177252320088400586223143 16765878480132600879334715)
        ·
          refine ⟨25148817720198901319002073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16765878480132600879334715 25148817720198901319002073)
          ·
            refine ⟨18861613290149175989251555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25148817720198901319002073 18861613290149175989251555)
            ·
              refine ⟨28292419935223763983877333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18861613290149175989251555 28292419935223763983877333)
              ·
                refine ⟨663103592231806968372125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28292419935223763983877333 663103592231806968372125)
                ·
                  refine ⟨248663847086927613139547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663103592231806968372125 248663847086927613139547)
                  ·
                    rfl

theorem cell21_1089610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_1089610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089610 prefixEnd_1089610 := by exact prefixLift 1089610
  have htrace : WordTrace (prefixWord ++ tailWord_1089610) baseStart_1089610 baseEnd_1089610 := by
    simpa [prefixWord, tailWord_1089610, baseEnd_1089610] using wordTrace_append hprefix tailTrace_1089610
  have hstable : (prefixWord ++ tailWord_1089610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089610).length < 2 ^ (prefixWord ++ tailWord_1089610).sum := by decide
  have hdescent : baseEnd_1089610 < baseStart_1089610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089624 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_1089624 : Nat := 118140960795 + 1089624 * 2 ^ 59
def prefixEnd_1089624 : Nat := 4983230072969 + 3 ^ 40 * 1089624 * 2
def baseEnd_1089624 : Nat := 248667042077666699906185

theorem tailTrace_1089624 : CollatzResearch.WordTrace tailWord_1089624 prefixEnd_1089624 248667042077666699906185 := by
  unfold tailWord_1089624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19870926102242907904345963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26494568136323877205794617 19870926102242907904345963)
  ·
    refine ⟨29806389153364361856518945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19870926102242907904345963 29806389153364361856518945)
    ·
      refine ⟨22354791865023271392389209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29806389153364361856518945 22354791865023271392389209)
      ·
        refine ⟨16766093898767453544291907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22354791865023271392389209 16766093898767453544291907)
        ·
          refine ⟨25149140848151180316437861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16766093898767453544291907 25149140848151180316437861)
          ·
            refine ⟨4715463909028346309332099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25149140848151180316437861 4715463909028346309332099)
            ·
              refine ⟨7073195863542519463998149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715463909028346309332099 7073195863542519463998149)
              ·
                refine ⟨1326224224414222399499653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7073195863542519463998149 1326224224414222399499653)
                ·
                  refine ⟨248667042077666699906185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1326224224414222399499653 248667042077666699906185)
                  ·
                    rfl

theorem cell21_1089624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_1089624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089624 prefixEnd_1089624 := by exact prefixLift 1089624
  have htrace : WordTrace (prefixWord ++ tailWord_1089624) baseStart_1089624 baseEnd_1089624 := by
    simpa [prefixWord, tailWord_1089624, baseEnd_1089624] using wordTrace_append hprefix tailTrace_1089624
  have hstable : (prefixWord ++ tailWord_1089624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089624).length < 2 ^ (prefixWord ++ tailWord_1089624).sum := by decide
  have hdescent : baseEnd_1089624 < baseStart_1089624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089630 : List Nat := [4, 4, 1, 1, 2, 2, 1, 6]
def baseStart_1089630 : Nat := 118140960795 + 1089630 * 2 ^ 59
def prefixEnd_1089630 : Nat := 4983230072969 + 3 ^ 40 * 1089630 * 2
def baseEnd_1089630 : Nat := 82889470453137340935391

theorem tailTrace_1089630 : CollatzResearch.WordTrace tailWord_1089630 prefixEnd_1089630 82889470453137340935391 := by
  unfold tailWord_1089630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4967758880308009854176293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26494714028309385888940229 4967758880308009854176293)
  ·
    refine ⟨931454790057751847658055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4967758880308009854176293 931454790057751847658055)
    ·
      refine ⟨1397182185086627771487083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931454790057751847658055 1397182185086627771487083)
      ·
        refine ⟨2095773277629941657230625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397182185086627771487083 2095773277629941657230625)
        ·
          refine ⟨1571829958222456242922969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095773277629941657230625 1571829958222456242922969)
          ·
            refine ⟨1178872468666842182192227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1571829958222456242922969 1178872468666842182192227)
            ·
              refine ⟨1768308703000263273288341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178872468666842182192227 1768308703000263273288341)
              ·
                refine ⟨82889470453137340935391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1768308703000263273288341 82889470453137340935391)
                ·
                  rfl

theorem cell21_1089630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_1089630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089630 prefixEnd_1089630 := by exact prefixLift 1089630
  have htrace : WordTrace (prefixWord ++ tailWord_1089630) baseStart_1089630 baseEnd_1089630 := by
    simpa [prefixWord, tailWord_1089630, baseEnd_1089630] using wordTrace_append hprefix tailTrace_1089630
  have hstable : (prefixWord ++ tailWord_1089630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089630).length < 2 ^ (prefixWord ++ tailWord_1089630).sum := by decide
  have hdescent : baseEnd_1089630 < baseStart_1089630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089655 : List Nat := [1, 1, 3, 1, 1, 6, 3, 5]
def baseStart_1089655 : Nat := 118140960795 + 1089655 * 2 ^ 59
def prefixEnd_1089655 : Nat := 4983230072969 + 3 ^ 40 * 1089655 * 2
def baseEnd_1089655 : Nat := 82891372233339178296485

theorem tailTrace_1089655 : CollatzResearch.WordTrace tailWord_1089655 prefixEnd_1089655 82891372233339178296485 := by
  unfold tailWord_1089655
  simp only [CollatzResearch.WordTrace]
  refine ⟨39742982867373508103070419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26495321911582338735380279 39742982867373508103070419)
  ·
    refine ⟨59614474301060262154605629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39742982867373508103070419 59614474301060262154605629)
    ·
      refine ⟨22355427862897598307977111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59614474301060262154605629 22355427862897598307977111)
      ·
        refine ⟨33533141794346397461965667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22355427862897598307977111 33533141794346397461965667)
        ·
          refine ⟨50299712691519596192948501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33533141794346397461965667 50299712691519596192948501)
          ·
            refine ⟨2357799032414981071544461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50299712691519596192948501 2357799032414981071544461)
            ·
              refine ⟨884174637155617901829173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2357799032414981071544461 884174637155617901829173)
              ·
                refine ⟨82891372233339178296485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 884174637155617901829173 82891372233339178296485)
                ·
                  rfl

theorem cell21_1089655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 5].length) (baseStart_1089655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089655 prefixEnd_1089655 := by exact prefixLift 1089655
  have htrace : WordTrace (prefixWord ++ tailWord_1089655) baseStart_1089655 baseEnd_1089655 := by
    simpa [prefixWord, tailWord_1089655, baseEnd_1089655] using wordTrace_append hprefix tailTrace_1089655
  have hstable : (prefixWord ++ tailWord_1089655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089655).length < 2 ^ (prefixWord ++ tailWord_1089655).sum := by decide
  have hdescent : baseEnd_1089655 < baseStart_1089655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089706 : List Nat := [3, 1, 5, 1, 3, 1, 2, 5]
def baseStart_1089706 : Nat := 118140960795 + 1089706 * 2 ^ 59
def prefixEnd_1089706 : Nat := 4983230072969 + 3 ^ 40 * 1089706 * 2
def baseEnd_1089706 : Nat := 82895251864950926513117

theorem tailTrace_1089706 : CollatzResearch.WordTrace tailWord_1089706 prefixEnd_1089706 82895251864950926513117 := by
  unfold tailWord_1089706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936210747547185953294243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26496561993459162542117981 9936210747547185953294243)
  ·
    refine ⟨14904316121320778929941365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9936210747547185953294243 14904316121320778929941365)
    ·
      refine ⟨1397279636373823024682003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14904316121320778929941365 1397279636373823024682003)
      ·
        refine ⟨2095919454560734537023005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397279636373823024682003 2095919454560734537023005)
        ·
          refine ⟨785969795460275451383627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2095919454560734537023005 785969795460275451383627)
          ·
            refine ⟨1178954693190413177075441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785969795460275451383627 1178954693190413177075441)
            ·
              refine ⟨884216019892809882806581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178954693190413177075441 884216019892809882806581)
              ·
                refine ⟨82895251864950926513117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 884216019892809882806581 82895251864950926513117)
                ·
                  rfl

theorem cell21_1089706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_1089706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089706 prefixEnd_1089706 := by exact prefixLift 1089706
  have htrace : WordTrace (prefixWord ++ tailWord_1089706) baseStart_1089706 baseEnd_1089706 := by
    simpa [prefixWord, tailWord_1089706, baseEnd_1089706] using wordTrace_append hprefix tailTrace_1089706
  have hstable : (prefixWord ++ tailWord_1089706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089706).length < 2 ^ (prefixWord ++ tailWord_1089706).sum := by decide
  have hdescent : baseEnd_1089706 < baseStart_1089706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089714 : List Nat := [3, 2, 1, 1, 1, 3, 3, 7]
def baseStart_1089714 : Nat := 118140960795 + 1089714 * 2 ^ 59
def prefixEnd_1089714 : Nat := 4983230072969 + 3 ^ 40 * 1089714 * 2
def baseEnd_1089714 : Nat := 82895860434615514468667

theorem tailTrace_1089714 : CollatzResearch.WordTrace tailWord_1089714 prefixEnd_1089714 82895860434615514468667 := by
  unfold tailWord_1089714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936283693539940294867049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26496756516106507452978797 9936283693539940294867049)
  ·
    refine ⟨7452212770154955221150287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9936283693539940294867049 7452212770154955221150287)
    ·
      refine ⟨11178319155232432831725431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7452212770154955221150287 11178319155232432831725431)
      ·
        refine ⟨16767478732848649247588147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11178319155232432831725431 16767478732848649247588147)
        ·
          refine ⟨25151218099272973871382221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16767478732848649247588147 25151218099272973871382221)
          ·
            refine ⟨9431706787227365201768333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25151218099272973871382221 9431706787227365201768333)
            ·
              refine ⟨3536890045210261950663125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9431706787227365201768333 3536890045210261950663125)
              ·
                refine ⟨82895860434615514468667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3536890045210261950663125 82895860434615514468667)
                ·
                  rfl

theorem cell21_1089714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_1089714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089714 prefixEnd_1089714 := by exact prefixLift 1089714
  have htrace : WordTrace (prefixWord ++ tailWord_1089714) baseStart_1089714 baseEnd_1089714 := by
    simpa [prefixWord, tailWord_1089714, baseEnd_1089714] using wordTrace_append hprefix tailTrace_1089714
  have hstable : (prefixWord ++ tailWord_1089714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089714).length < 2 ^ (prefixWord ++ tailWord_1089714).sum := by decide
  have hdescent : baseEnd_1089714 < baseStart_1089714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089745 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 5]
def baseStart_1089745 : Nat := 118140960795 + 1089745 * 2 ^ 59
def prefixEnd_1089745 : Nat := 4983230072969 + 3 ^ 40 * 1089745 * 2
def baseEnd_1089745 : Nat := 248694655926197378389271

theorem tailTrace_1089745 : CollatzResearch.WordTrace tailWord_1089745 prefixEnd_1089745 248694655926197378389271 := by
  unfold tailWord_1089745
  simp only [CollatzResearch.WordTrace]
  refine ⟨39746265437047453473846689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26497510291364968982564459 39746265437047453473846689)
  ·
    refine ⟨29809699077785590105385017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39746265437047453473846689 29809699077785590105385017)
    ·
      refine ⟨22357274308339192579038763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29809699077785590105385017 22357274308339192579038763)
      ·
        refine ⟨33535911462508788868558145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22357274308339192579038763 33535911462508788868558145)
        ·
          refine ⟨25151933596881591651418609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33535911462508788868558145 25151933596881591651418609)
          ·
            refine ⟨18863950197661193738563957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25151933596881591651418609 18863950197661193738563957)
            ·
              refine ⟨1768495331030736912990371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18863950197661193738563957 1768495331030736912990371)
              ·
                refine ⟨2652742996546105369485557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768495331030736912990371 2652742996546105369485557)
                ·
                  refine ⟨248694655926197378389271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2652742996546105369485557 248694655926197378389271)
                  ·
                    rfl

theorem cell21_1089745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_1089745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089745 prefixEnd_1089745 := by exact prefixLift 1089745
  have htrace : WordTrace (prefixWord ++ tailWord_1089745) baseStart_1089745 baseEnd_1089745 := by
    simpa [prefixWord, tailWord_1089745, baseEnd_1089745] using wordTrace_append hprefix tailTrace_1089745
  have hstable : (prefixWord ++ tailWord_1089745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089745).length < 2 ^ (prefixWord ++ tailWord_1089745).sum := by decide
  have hdescent : baseEnd_1089745 < baseStart_1089745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089880 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_1089880 : Nat := 118140960795 + 1089880 * 2 ^ 59
def prefixEnd_1089880 : Nat := 4983230072969 + 3 ^ 40 * 1089880 * 2
def baseEnd_1089880 : Nat := 248725464765467143638995

theorem tailTrace_1089880 : CollatzResearch.WordTrace tailWord_1089880 prefixEnd_1089880 248725464765467143638995 := by
  unfold tailWord_1089880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19875594645779185765005547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26500792861038914353340729 19875594645779185765005547)
  ·
    refine ⟨29813391968668778647508321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19875594645779185765005547 29813391968668778647508321)
    ·
      refine ⟨22360043976501583985631241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29813391968668778647508321 22360043976501583985631241)
      ·
        refine ⟨16770032982376187989223431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22360043976501583985631241 16770032982376187989223431)
        ·
          refine ⟨25155049473564281983835147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16770032982376187989223431 25155049473564281983835147)
          ·
            refine ⟨37732574210346422975752721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25155049473564281983835147 37732574210346422975752721)
            ·
              refine ⟨28299430657759817231814541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37732574210346422975752721 28299430657759817231814541)
              ·
                refine ⟨10612286496659931461930453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28299430657759817231814541 10612286496659931461930453)
                ·
                  refine ⟨248725464765467143638995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10612286496659931461930453 248725464765467143638995)
                  ·
                    rfl

theorem cell21_1089880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_1089880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089880 prefixEnd_1089880 := by exact prefixLift 1089880
  have htrace : WordTrace (prefixWord ++ tailWord_1089880) baseStart_1089880 baseEnd_1089880 := by
    simpa [prefixWord, tailWord_1089880, baseEnd_1089880] using wordTrace_append hprefix tailTrace_1089880
  have hstable : (prefixWord ++ tailWord_1089880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089880).length < 2 ^ (prefixWord ++ tailWord_1089880).sum := by decide
  have hdescent : baseEnd_1089880 < baseStart_1089880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089928 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_1089928 : Nat := 118140960795 + 1089928 * 2 ^ 59
def prefixEnd_1089928 : Nat := 4983230072969 + 3 ^ 40 * 1089928 * 2
def baseEnd_1089928 : Nat := 248736419019429726838897

theorem tailTrace_1089928 : CollatzResearch.WordTrace tailWord_1089928 prefixEnd_1089928 248736419019429726838897 := by
  unfold tailWord_1089928
  simp only [CollatzResearch.WordTrace]
  refine ⟨19876469997692237863879219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26501959996922983818505625 19876469997692237863879219)
  ·
    refine ⟨29814704996538356795818829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19876469997692237863879219 29814704996538356795818829)
    ·
      refine ⟨11180514373701883798432061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29814704996538356795818829 11180514373701883798432061)
      ·
        refine ⟨4192692890138206424412023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11180514373701883798432061 4192692890138206424412023)
        ·
          refine ⟨6289039335207309636618035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192692890138206424412023 6289039335207309636618035)
          ·
            refine ⟨9433559002810964454927053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289039335207309636618035 9433559002810964454927053)
            ·
              refine ⟨3537584626054111670597645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9433559002810964454927053 3537584626054111670597645)
              ·
                refine ⟨1326594234770291876474117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3537584626054111670597645 1326594234770291876474117)
                ·
                  refine ⟨248736419019429726838897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1326594234770291876474117 248736419019429726838897)
                  ·
                    rfl

theorem cell21_1089928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_1089928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089928 prefixEnd_1089928 := by exact prefixLift 1089928
  have htrace : WordTrace (prefixWord ++ tailWord_1089928) baseStart_1089928 baseEnd_1089928 := by
    simpa [prefixWord, tailWord_1089928, baseEnd_1089928] using wordTrace_append hprefix tailTrace_1089928
  have hstable : (prefixWord ++ tailWord_1089928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089928).length < 2 ^ (prefixWord ++ tailWord_1089928).sum := by decide
  have hdescent : baseEnd_1089928 < baseStart_1089928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089965 : List Nat := [1, 5, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1089965 : Nat := 118140960795 + 1089965 * 2 ^ 59
def prefixEnd_1089965 : Nat := 4983230072969 + 3 ^ 40 * 1089965 * 2
def baseEnd_1089965 : Nat := 248744862923525884722155

theorem tailTrace_1089965 : CollatzResearch.WordTrace tailWord_1089965 prefixEnd_1089965 248744862923525884722155 := by
  unfold tailWord_1089965
  simp only [CollatzResearch.WordTrace]
  refine ⟨39754289496250431046855349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26502859664166954031236899 39754289496250431046855349)
  ·
    refine ⟨3726964640273477910642689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39754289496250431046855349 3726964640273477910642689)
    ·
      refine ⟨2795223480205108432982017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3726964640273477910642689 2795223480205108432982017)
      ·
        refine ⟨2096417610153831324736513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2795223480205108432982017 2096417610153831324736513)
        ·
          refine ⟨1572313207615373493552385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2096417610153831324736513 1572313207615373493552385)
          ·
            refine ⟨1179234905711530120164289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572313207615373493552385 1179234905711530120164289)
            ·
              refine ⟨884426179283647590123217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179234905711530120164289 884426179283647590123217)
              ·
                refine ⟨663319634462735692592413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884426179283647590123217 663319634462735692592413)
                ·
                  refine ⟨248744862923525884722155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663319634462735692592413 248744862923525884722155)
                  ·
                    rfl

theorem cell21_1089965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1089965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1089965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1089965 prefixEnd_1089965 := by exact prefixLift 1089965
  have htrace : WordTrace (prefixWord ++ tailWord_1089965) baseStart_1089965 baseEnd_1089965 := by
    simpa [prefixWord, tailWord_1089965, baseEnd_1089965] using wordTrace_append hprefix tailTrace_1089965
  have hstable : (prefixWord ++ tailWord_1089965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089965).length < 2 ^ (prefixWord ++ tailWord_1089965).sum := by decide
  have hdescent : baseEnd_1089965 < baseStart_1089965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090001 : List Nat := [1, 2, 2, 1, 2, 1, 1, 11]
def baseStart_1090001 : Nat := 118140960795 + 1090001 * 2 ^ 59
def prefixEnd_1090001 : Nat := 4983230072969 + 3 ^ 40 * 1090001 * 2
def baseEnd_1090001 : Nat := 82917692871332607374027

theorem tailTrace_1090001 : CollatzResearch.WordTrace tailWord_1090001 prefixEnd_1090001 82917692871332607374027 := by
  unfold tailWord_1090001
  simp only [CollatzResearch.WordTrace]
  refine ⟨39755602524120009195165857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26503735016080006130110571 39755602524120009195165857)
  ·
    refine ⟨29816701893090006896374393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39755602524120009195165857 29816701893090006896374393)
    ·
      refine ⟨22362526419817505172280795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29816701893090006896374393 22362526419817505172280795)
      ·
        refine ⟨33543789629726257758421193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22362526419817505172280795 33543789629726257758421193)
        ·
          refine ⟨25157842222294693318815895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33543789629726257758421193 25157842222294693318815895)
          ·
            refine ⟨37736763333442039978223843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25157842222294693318815895 37736763333442039978223843)
            ·
              refine ⟨56605145000163059967335765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37736763333442039978223843 56605145000163059967335765)
              ·
                refine ⟨82917692871332607374027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56605145000163059967335765 82917692871332607374027)
                ·
                  rfl

theorem cell21_1090001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 11].length) (baseStart_1090001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090001 prefixEnd_1090001 := by exact prefixLift 1090001
  have htrace : WordTrace (prefixWord ++ tailWord_1090001) baseStart_1090001 baseEnd_1090001 := by
    simpa [prefixWord, tailWord_1090001, baseEnd_1090001] using wordTrace_append hprefix tailTrace_1090001
  have hstable : (prefixWord ++ tailWord_1090001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090001).length < 2 ^ (prefixWord ++ tailWord_1090001).sum := by decide
  have hdescent : baseEnd_1090001 < baseStart_1090001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090049 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 5]
def baseStart_1090049 : Nat := 118140960795 + 1090049 * 2 ^ 59
def prefixEnd_1090049 : Nat := 4983230072969 + 3 ^ 40 * 1090049 * 2
def baseEnd_1090049 : Nat := 248764032867960405321983

theorem tailTrace_1090049 : CollatzResearch.WordTrace tailWord_1090049 prefixEnd_1090049 248764032867960405321983 := by
  unfold tailWord_1090049
  simp only [CollatzResearch.WordTrace]
  refine ⟨39757353227946113392913201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26504902151964075595275467 39757353227946113392913201)
  ·
    refine ⟨29818014920959585044684901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39757353227946113392913201 29818014920959585044684901)
    ·
      refine ⟨5590877797679922195878419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29818014920959585044684901 5590877797679922195878419)
      ·
        refine ⟨8386316696519883293817629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5590877797679922195878419 8386316696519883293817629)
        ·
          refine ⟨3144868761194956235181611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8386316696519883293817629 3144868761194956235181611)
          ·
            refine ⟨4717303141792434352772417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144868761194956235181611 4717303141792434352772417)
            ·
              refine ⟨3537977356344325764579313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4717303141792434352772417 3537977356344325764579313)
              ·
                refine ⟨2653483017258244323434485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3537977356344325764579313 2653483017258244323434485)
                ·
                  refine ⟨248764032867960405321983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2653483017258244323434485 248764032867960405321983)
                  ·
                    rfl

theorem cell21_1090049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_1090049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090049 prefixEnd_1090049 := by exact prefixLift 1090049
  have htrace : WordTrace (prefixWord ++ tailWord_1090049) baseStart_1090049 baseEnd_1090049 := by
    simpa [prefixWord, tailWord_1090049, baseEnd_1090049] using wordTrace_append hprefix tailTrace_1090049
  have hstable : (prefixWord ++ tailWord_1090049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090049).length < 2 ^ (prefixWord ++ tailWord_1090049).sum := by decide
  have hdescent : baseEnd_1090049 < baseStart_1090049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090052 : List Nat := [2, 3, 2, 3, 1, 3, 2, 5]
def baseStart_1090052 : Nat := 118140960795 + 1090052 * 2 ^ 59
def prefixEnd_1090052 : Nat := 4983230072969 + 3 ^ 40 * 1090052 * 2
def baseEnd_1090052 : Nat := 82921572502944355590659

theorem tailTrace_1090052 : CollatzResearch.WordTrace tailWord_1090052 prefixEnd_1090052 82921572502944355590659 := by
  unfold tailWord_1090052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878731323467622452636205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26504975097956829936848273 19878731323467622452636205)
  ·
    refine ⟨7454524246300358419738577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19878731323467622452636205 7454524246300358419738577)
    ·
      refine ⟨5590893184725268814803933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7454524246300358419738577 5590893184725268814803933)
      ·
        refine ⟨2096584944271975805551475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5590893184725268814803933 2096584944271975805551475)
        ·
          refine ⟨3144877416407963708327213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2096584944271975805551475 3144877416407963708327213)
          ·
            refine ⟨1179329031152986390622705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3144877416407963708327213 1179329031152986390622705)
            ·
              refine ⟨884496773364739792967029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179329031152986390622705 884496773364739792967029)
              ·
                refine ⟨82921572502944355590659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 884496773364739792967029 82921572502944355590659)
                ·
                  rfl

theorem cell21_1090052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_1090052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090052 prefixEnd_1090052 := by exact prefixLift 1090052
  have htrace : WordTrace (prefixWord ++ tailWord_1090052) baseStart_1090052 baseEnd_1090052 := by
    simpa [prefixWord, tailWord_1090052, baseEnd_1090052] using wordTrace_append hprefix tailTrace_1090052
  have hstable : (prefixWord ++ tailWord_1090052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090052).length < 2 ^ (prefixWord ++ tailWord_1090052).sum := by decide
  have hdescent : baseEnd_1090052 < baseStart_1090052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090083 : List Nat := [1, 1, 1, 4, 4, 2, 3, 2, 3]
def baseStart_1090083 : Nat := 118140960795 + 1090083 * 2 ^ 59
def prefixEnd_1090083 : Nat := 4983230072969 + 3 ^ 40 * 1090083 * 2
def baseEnd_1090083 : Nat := 248771792131183901755247

theorem tailTrace_1090083 : CollatzResearch.WordTrace tailWord_1090083 prefixEnd_1090083 248771792131183901755247 := by
  unfold tailWord_1090083
  simp only [CollatzResearch.WordTrace]
  refine ⟨39758593309822937199650903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26505728873215291466433935 39758593309822937199650903)
  ·
    refine ⟨59637889964734405799476355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39758593309822937199650903 59637889964734405799476355)
    ·
      refine ⟨89456834947101608699214533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59637889964734405799476355 89456834947101608699214533)
      ·
        refine ⟨16773156552581551631102725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89456834947101608699214533 16773156552581551631102725)
        ·
          refine ⟨3144966853609040930831761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16773156552581551631102725 3144966853609040930831761)
          ·
            refine ⟨2358725140206780698123821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3144966853609040930831761 2358725140206780698123821)
            ·
              refine ⟨884521927577542761796433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2358725140206780698123821 884521927577542761796433)
              ·
                refine ⟨663391445683157071347325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884521927577542761796433 663391445683157071347325)
                ·
                  refine ⟨248771792131183901755247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663391445683157071347325 248771792131183901755247)
                  ·
                    rfl

theorem cell21_1090083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 3].length) (baseStart_1090083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090083 prefixEnd_1090083 := by exact prefixLift 1090083
  have htrace : WordTrace (prefixWord ++ tailWord_1090083) baseStart_1090083 baseEnd_1090083 := by
    simpa [prefixWord, tailWord_1090083, baseEnd_1090083] using wordTrace_append hprefix tailTrace_1090083
  have hstable : (prefixWord ++ tailWord_1090083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090083).length < 2 ^ (prefixWord ++ tailWord_1090083).sum := by decide
  have hdescent : baseEnd_1090083 < baseStart_1090083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090201 : List Nat := [1, 2, 1, 2, 1, 2, 3, 6, 3]
def baseStart_1090201 : Nat := 118140960795 + 1090201 * 2 ^ 59
def prefixEnd_1090201 : Nat := 4983230072969 + 3 ^ 40 * 1090201 * 2
def baseEnd_1090201 : Nat := 248798721338841918788339

theorem tailTrace_1090201 : CollatzResearch.WordTrace tailWord_1090201 prefixEnd_1090201 248798721338841918788339 := by
  unfold tailWord_1090201
  simp only [CollatzResearch.WordTrace]
  refine ⟨39762897123395443352446457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26508598082263628901630971 39762897123395443352446457)
  ·
    refine ⟨29822172842546582514334843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39762897123395443352446457 29822172842546582514334843)
    ·
      refine ⟨44733259263819873771502265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29822172842546582514334843 44733259263819873771502265)
      ·
        refine ⟨33549944447864905328626699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44733259263819873771502265 33549944447864905328626699)
        ·
          refine ⟨50324916671797357992940049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33549944447864905328626699 50324916671797357992940049)
          ·
            refine ⟨37743687503848018494705037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50324916671797357992940049 37743687503848018494705037)
            ·
              refine ⟨14153882813943006935514389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37743687503848018494705037 14153882813943006935514389)
              ·
                refine ⟨663463256903578450102237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14153882813943006935514389 663463256903578450102237)
                ·
                  refine ⟨248798721338841918788339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663463256903578450102237 248798721338841918788339)
                  ·
                    rfl

theorem cell21_1090201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_1090201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090201 prefixEnd_1090201 := by exact prefixLift 1090201
  have htrace : WordTrace (prefixWord ++ tailWord_1090201) baseStart_1090201 baseEnd_1090201 := by
    simpa [prefixWord, tailWord_1090201, baseEnd_1090201] using wordTrace_append hprefix tailTrace_1090201
  have hstable : (prefixWord ++ tailWord_1090201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090201).length < 2 ^ (prefixWord ++ tailWord_1090201).sum := by decide
  have hdescent : baseEnd_1090201 < baseStart_1090201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090294 : List Nat := [5, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1090294 : Nat := 118140960795 + 1090294 * 2 ^ 59
def prefixEnd_1090294 : Nat := 4983230072969 + 3 ^ 40 * 1090294 * 2
def baseEnd_1090294 : Nat := 248819945205894423738149

theorem tailTrace_1090294 : CollatzResearch.WordTrace tailWord_1090294 prefixEnd_1090294 248819945205894423738149 := by
  unfold tailWord_1090294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485393069503657514723871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26510859408039013490387957 2485393069503657514723871)
  ·
    refine ⟨3728089604255486272085807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485393069503657514723871 3728089604255486272085807)
    ·
      refine ⟨5592134406383229408128711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728089604255486272085807 5592134406383229408128711)
      ·
        refine ⟨8388201609574844112193067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592134406383229408128711 8388201609574844112193067)
        ·
          refine ⟨12582302414362266168289601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388201609574844112193067 12582302414362266168289601)
          ·
            refine ⟨9436726810771699626217201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12582302414362266168289601 9436726810771699626217201)
            ·
              refine ⟨7077545108078774719662901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9436726810771699626217201 7077545108078774719662901)
              ·
                refine ⟨663519853882385129968397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7077545108078774719662901 663519853882385129968397)
                ·
                  refine ⟨248819945205894423738149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663519853882385129968397 248819945205894423738149)
                  ·
                    rfl

theorem cell21_1090294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1090294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090294 prefixEnd_1090294 := by exact prefixLift 1090294
  have htrace : WordTrace (prefixWord ++ tailWord_1090294) baseStart_1090294 baseEnd_1090294 := by
    simpa [prefixWord, tailWord_1090294, baseEnd_1090294] using wordTrace_append hprefix tailTrace_1090294
  have hstable : (prefixWord ++ tailWord_1090294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090294).length < 2 ^ (prefixWord ++ tailWord_1090294).sum := by decide
  have hdescent : baseEnd_1090294 < baseStart_1090294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090308 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1090308 : Nat := 118140960795 + 1090308 * 2 ^ 59
def prefixEnd_1090308 : Nat := 4983230072969 + 3 ^ 40 * 1090308 * 2
def baseEnd_1090308 : Nat := 248823140196633510504787

theorem tailTrace_1090308 : CollatzResearch.WordTrace tailWord_1090308 prefixEnd_1090308 248823140196633510504787 := by
  unfold tailWord_1090308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883399867003900313295789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26511199822671867084394385 19883399867003900313295789)
  ·
    refine ⟨7456274950126462617485921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19883399867003900313295789 7456274950126462617485921)
    ·
      refine ⟨5592206212594846963114441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7456274950126462617485921 5592206212594846963114441)
      ·
        refine ⟨4194154659446135222335831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5592206212594846963114441 4194154659446135222335831)
        ·
          refine ⟨6291231989169202833503747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194154659446135222335831 6291231989169202833503747)
          ·
            refine ⟨9436847983753804250255621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6291231989169202833503747 9436847983753804250255621)
            ·
              refine ⟨1769408996953838296922929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9436847983753804250255621 1769408996953838296922929)
              ·
                refine ⟨1327056747715378722692197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1769408996953838296922929 1327056747715378722692197)
                ·
                  refine ⟨248823140196633510504787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1327056747715378722692197 248823140196633510504787)
                  ·
                    rfl

theorem cell21_1090308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1090308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090308 prefixEnd_1090308 := by exact prefixLift 1090308
  have htrace : WordTrace (prefixWord ++ tailWord_1090308) baseStart_1090308 baseEnd_1090308 := by
    simpa [prefixWord, tailWord_1090308, baseEnd_1090308] using wordTrace_append hprefix tailTrace_1090308
  have hstable : (prefixWord ++ tailWord_1090308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090308).length < 2 ^ (prefixWord ++ tailWord_1090308).sum := by decide
  have hdescent : baseEnd_1090308 < baseStart_1090308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090311 : List Nat := [1, 1, 4, 4, 1, 1, 4, 2, 3]
def baseStart_1090311 : Nat := 118140960795 + 1090311 * 2 ^ 59
def prefixEnd_1090311 : Nat := 4983230072969 + 3 ^ 40 * 1090311 * 2
def baseEnd_1090311 : Nat := 248823824837506171954781

theorem tailTrace_1090311 : CollatzResearch.WordTrace tailWord_1090311 prefixEnd_1090311 248823824837506171954781 := by
  unfold tailWord_1090311
  simp only [CollatzResearch.WordTrace]
  refine ⟨39766909152996932138950787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26511272768664621425967191 39766909152996932138950787)
  ·
    refine ⟨59650363729495398208426181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39766909152996932138950787 59650363729495398208426181)
    ·
      refine ⟨11184443199280387164079909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59650363729495398208426181 11184443199280387164079909)
      ·
        refine ⟨2097083099865072593264983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11184443199280387164079909 2097083099865072593264983)
        ·
          refine ⟨3145624649797608889897475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097083099865072593264983 3145624649797608889897475)
          ·
            refine ⟨4718436974696413334846213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145624649797608889897475 4718436974696413334846213)
            ·
              refine ⟨884706932755577500283665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4718436974696413334846213 884706932755577500283665)
              ·
                refine ⟨663530199566683125212749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884706932755577500283665 663530199566683125212749)
                ·
                  refine ⟨248823824837506171954781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663530199566683125212749 248823824837506171954781)
                  ·
                    rfl

theorem cell21_1090311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 3].length) (baseStart_1090311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090311 prefixEnd_1090311 := by exact prefixLift 1090311
  have htrace : WordTrace (prefixWord ++ tailWord_1090311) baseStart_1090311 baseEnd_1090311 := by
    simpa [prefixWord, tailWord_1090311, baseEnd_1090311] using wordTrace_append hprefix tailTrace_1090311
  have hstable : (prefixWord ++ tailWord_1090311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090311).length < 2 ^ (prefixWord ++ tailWord_1090311).sum := by decide
  have hdescent : baseEnd_1090311 < baseStart_1090311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090336 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_1090336 : Nat := 118140960795 + 1090336 * 2 ^ 59
def prefixEnd_1090336 : Nat := 4983230072969 + 3 ^ 40 * 1090336 * 2
def baseEnd_1090336 : Nat := 248829530178111684038063

theorem tailTrace_1090336 : CollatzResearch.WordTrace tailWord_1090336 prefixEnd_1090336 248829530178111684038063 := by
  unfold tailWord_1090336
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883910488953180704305431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26511880651937574272407241 19883910488953180704305431)
  ·
    refine ⟨29825865733429771056458147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19883910488953180704305431 29825865733429771056458147)
    ·
      refine ⟨44738798600144656584687221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29825865733429771056458147 44738798600144656584687221)
      ·
        refine ⟨4194262368763561554814427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44738798600144656584687221 4194262368763561554814427)
        ·
          refine ⟨6291393553145342332221641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194262368763561554814427 6291393553145342332221641)
          ·
            refine ⟨4718545164859006749166231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6291393553145342332221641 4718545164859006749166231)
            ·
              refine ⟨7077817747288510123749347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4718545164859006749166231 7077817747288510123749347)
              ·
                refine ⟨10616726620932765185624021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7077817747288510123749347 10616726620932765185624021)
                ·
                  refine ⟨248829530178111684038063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10616726620932765185624021 248829530178111684038063)
                  ·
                    rfl

theorem cell21_1090336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_1090336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090336 prefixEnd_1090336 := by exact prefixLift 1090336
  have htrace : WordTrace (prefixWord ++ tailWord_1090336) baseStart_1090336 baseEnd_1090336 := by
    simpa [prefixWord, tailWord_1090336, baseEnd_1090336] using wordTrace_append hprefix tailTrace_1090336
  have hstable : (prefixWord ++ tailWord_1090336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090336).length < 2 ^ (prefixWord ++ tailWord_1090336).sum := by decide
  have hdescent : baseEnd_1090336 < baseStart_1090336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090367 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 6]
def baseStart_1090367 : Nat := 118140960795 + 1090367 * 2 ^ 59
def prefixEnd_1090367 : Nat := 4983230072969 + 3 ^ 40 * 1090367 * 2
def baseEnd_1090367 : Nat := 248836604800462519021333

theorem tailTrace_1090367 : CollatzResearch.WordTrace tailWord_1090367 prefixEnd_1090367 248836604800462519021333 := by
  unfold tailWord_1090367
  simp only [CollatzResearch.WordTrace]
  refine ⟨39768951640794053702989355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26512634427196035801992903 39768951640794053702989355)
  ·
    refine ⟨59653427461191080554484033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39768951640794053702989355 59653427461191080554484033)
    ·
      refine ⟨44740070595893310415863025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59653427461191080554484033 44740070595893310415863025)
      ·
        refine ⟨33555052946919982811897269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44740070595893310415863025 33555052946919982811897269)
        ·
          refine ⟨3145786213773748388615369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33555052946919982811897269 3145786213773748388615369)
          ·
            refine ⟨2359339660330311291461527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3145786213773748388615369 2359339660330311291461527)
            ·
              refine ⟨3539009490495466937192291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359339660330311291461527 3539009490495466937192291)
              ·
                refine ⟨5308514235743200405788437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539009490495466937192291 5308514235743200405788437)
                ·
                  refine ⟨248836604800462519021333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5308514235743200405788437 248836604800462519021333)
                  ·
                    rfl

theorem cell21_1090367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_1090367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090367 prefixEnd_1090367 := by exact prefixLift 1090367
  have htrace : WordTrace (prefixWord ++ tailWord_1090367) baseStart_1090367 baseEnd_1090367 := by
    simpa [prefixWord, tailWord_1090367, baseEnd_1090367] using wordTrace_append hprefix tailTrace_1090367
  have hstable : (prefixWord ++ tailWord_1090367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090367).length < 2 ^ (prefixWord ++ tailWord_1090367).sum := by decide
  have hdescent : baseEnd_1090367 < baseStart_1090367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090395 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 13]
def baseStart_1090395 : Nat := 118140960795 + 1090395 * 2 ^ 59
def prefixEnd_1090395 : Nat := 4983230072969 + 3 ^ 40 * 1090395 * 2
def baseEnd_1090395 : Nat := 248842994781940692554609

theorem tailTrace_1090395 : CollatzResearch.WordTrace tailWord_1090395 prefixEnd_1090395 248842994781940692554609 := by
  unfold tailWord_1090395
  simp only [CollatzResearch.WordTrace]
  refine ⟨39769972884692614485008639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26513315256461742990005759 39769972884692614485008639)
  ·
    refine ⟨59654959327038921727512959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39769972884692614485008639 59654959327038921727512959)
    ·
      refine ⟨89482438990558382591269439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59654959327038921727512959 89482438990558382591269439)
      ·
        refine ⟨134223658485837573886904159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89482438990558382591269439 134223658485837573886904159)
        ·
          refine ⟨201335487728756360830356239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134223658485837573886904159 201335487728756360830356239)
          ·
            refine ⟨302003231593134541245534359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201335487728756360830356239 302003231593134541245534359)
            ·
              refine ⟨453004847389701811868301539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302003231593134541245534359 453004847389701811868301539)
              ·
                refine ⟨679507271084552717802452309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453004847389701811868301539 679507271084552717802452309)
                ·
                  refine ⟨248842994781940692554609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 679507271084552717802452309 248842994781940692554609)
                  ·
                    rfl

theorem cell21_1090395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_1090395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090395 prefixEnd_1090395 := by exact prefixLift 1090395
  have htrace : WordTrace (prefixWord ++ tailWord_1090395) baseStart_1090395 baseEnd_1090395 := by
    simpa [prefixWord, tailWord_1090395, baseEnd_1090395] using wordTrace_append hprefix tailTrace_1090395
  have hstable : (prefixWord ++ tailWord_1090395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090395).length < 2 ^ (prefixWord ++ tailWord_1090395).sum := by decide
  have hdescent : baseEnd_1090395 < baseStart_1090395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090429 : List Nat := [1, 4, 1, 1, 2, 1, 2, 6, 3]
def baseStart_1090429 : Nat := 118140960795 + 1090429 * 2 ^ 59
def prefixEnd_1090429 : Nat := 4983230072969 + 3 ^ 40 * 1090429 * 2
def baseEnd_1090429 : Nat := 248850754045164188987873

theorem tailTrace_1090429 : CollatzResearch.WordTrace tailWord_1090429 prefixEnd_1090429 248850754045164188987873 := by
  unfold tailWord_1090429
  simp only [CollatzResearch.WordTrace]
  refine ⟨39771212966569438291746341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26514141977712958861164227 39771212966569438291746341)
  ·
    refine ⟨7457102431231769679702439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39771212966569438291746341 7457102431231769679702439)
    ·
      refine ⟨11185653646847654519553659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7457102431231769679702439 11185653646847654519553659)
      ·
        refine ⟨16778480470271481779330489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11185653646847654519553659 16778480470271481779330489)
        ·
          refine ⟨12583860352703611334497867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16778480470271481779330489 12583860352703611334497867)
          ·
            refine ⟨18875790529055417001746801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12583860352703611334497867 18875790529055417001746801)
            ·
              refine ⟨14156842896791562751310101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18875790529055417001746801 14156842896791562751310101)
              ·
                refine ⟨663602010787104503967661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14156842896791562751310101 663602010787104503967661)
                ·
                  refine ⟨248850754045164188987873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663602010787104503967661 248850754045164188987873)
                  ·
                    rfl

theorem cell21_1090429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_1090429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090429 prefixEnd_1090429 := by exact prefixLift 1090429
  have htrace : WordTrace (prefixWord ++ tailWord_1090429) baseStart_1090429 baseEnd_1090429 := by
    simpa [prefixWord, tailWord_1090429, baseEnd_1090429] using wordTrace_append hprefix tailTrace_1090429
  have hstable : (prefixWord ++ tailWord_1090429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090429).length < 2 ^ (prefixWord ++ tailWord_1090429).sum := by decide
  have hdescent : baseEnd_1090429 < baseStart_1090429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090522 : List Nat := [3, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_1090522 : Nat := 118140960795 + 1090522 * 2 ^ 59
def prefixEnd_1090522 : Nat := 4983230072969 + 3 ^ 40 * 1090522 * 2
def baseEnd_1090522 : Nat := 248871977912216693937683

theorem tailTrace_1090522 : CollatzResearch.WordTrace tailWord_1090522 prefixEnd_1090522 248871977912216693937683 := by
  unfold tailWord_1090522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9943651238808128793720455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26516403303488343449921213 9943651238808128793720455)
  ·
    refine ⟨14915476858212193190580683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9943651238808128793720455 14915476858212193190580683)
    ·
      refine ⟨22373215287318289785871025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14915476858212193190580683 22373215287318289785871025)
      ·
        refine ⟨16779911465488717339403269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22373215287318289785871025 16779911465488717339403269)
        ·
          refine ⟨3146233399779134501138113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16779911465488717339403269 3146233399779134501138113)
          ·
            refine ⟨2359675049834350875853585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3146233399779134501138113 2359675049834350875853585)
            ·
              refine ⟨1769756287375763156890189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2359675049834350875853585 1769756287375763156890189)
              ·
                refine ⟨663658607765911183833821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1769756287375763156890189 663658607765911183833821)
                ·
                  refine ⟨248871977912216693937683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663658607765911183833821 248871977912216693937683)
                  ·
                    rfl

theorem cell21_1090522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_1090522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090522 prefixEnd_1090522 := by exact prefixLift 1090522
  have htrace : WordTrace (prefixWord ++ tailWord_1090522) baseStart_1090522 baseEnd_1090522 := by
    simpa [prefixWord, tailWord_1090522, baseEnd_1090522] using wordTrace_append hprefix tailTrace_1090522
  have hstable : (prefixWord ++ tailWord_1090522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090522).length < 2 ^ (prefixWord ++ tailWord_1090522).sum := by decide
  have hdescent : baseEnd_1090522 < baseStart_1090522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090609 : List Nat := [1, 2, 2, 3, 1, 2, 4, 6]
def baseStart_1090609 : Nat := 118140960795 + 1090609 * 2 ^ 59
def prefixEnd_1090609 : Nat := 4983230072969 + 3 ^ 40 * 1090609 * 2
def baseEnd_1090609 : Nat := 82963944165841291995835

theorem tailTrace_1090609 : CollatzResearch.WordTrace tailWord_1090609 prefixEnd_1090609 82963944165841291995835 := by
  unfold tailWord_1090609
  simp only [CollatzResearch.WordTrace]
  refine ⟨39777778105917329033298881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26518518737278219355532587 39777778105917329033298881)
  ·
    refine ⟨29833333579437996774974161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39777778105917329033298881 29833333579437996774974161)
    ·
      refine ⟨22375000184578497581230621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29833333579437996774974161 22375000184578497581230621)
      ·
        refine ⟨8390625069216936592961483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22375000184578497581230621 8390625069216936592961483)
        ·
          refine ⟨12585937603825404889442225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8390625069216936592961483 12585937603825404889442225)
          ·
            refine ⟨9439453202869053667081669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12585937603825404889442225 9439453202869053667081669)
            ·
              refine ⟨1769897475537947562577813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9439453202869053667081669 1769897475537947562577813)
              ·
                refine ⟨82963944165841291995835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1769897475537947562577813 82963944165841291995835)
                ·
                  rfl

theorem cell21_1090609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 6].length) (baseStart_1090609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090609 prefixEnd_1090609 := by exact prefixLift 1090609
  have htrace : WordTrace (prefixWord ++ tailWord_1090609) baseStart_1090609 baseEnd_1090609 := by
    simpa [prefixWord, tailWord_1090609, baseEnd_1090609] using wordTrace_append hprefix tailTrace_1090609
  have hstable : (prefixWord ++ tailWord_1090609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090609).length < 2 ^ (prefixWord ++ tailWord_1090609).sum := by decide
  have hdescent : baseEnd_1090609 < baseStart_1090609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090623 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 7]
def baseStart_1090623 : Nat := 118140960795 + 1090623 * 2 ^ 59
def prefixEnd_1090623 : Nat := 4983230072969 + 3 ^ 40 * 1090623 * 2
def baseEnd_1090623 : Nat := 248895027488262962754143

theorem tailTrace_1090623 : CollatzResearch.WordTrace tailWord_1090623 prefixEnd_1090623 248895027488262962754143 := by
  unfold tailWord_1090623
  simp only [CollatzResearch.WordTrace]
  refine ⟨39778288727866609424308523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26518859151911072949539015 39778288727866609424308523)
  ·
    refine ⟨59667433091799914136462785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39778288727866609424308523 59667433091799914136462785)
    ·
      refine ⟨44750574818849935602347089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59667433091799914136462785 44750574818849935602347089)
      ·
        refine ⟨33562931114137451701760317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44750574818849935602347089 33562931114137451701760317)
        ·
          refine ⟨12586099167801544388160119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33562931114137451701760317 12586099167801544388160119)
          ·
            refine ⟨18879148751702316582240179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12586099167801544388160119 18879148751702316582240179)
            ·
              refine ⟨28318723127553474873360269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18879148751702316582240179 28318723127553474873360269)
              ·
                refine ⟨10619521172832553077510101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28318723127553474873360269 10619521172832553077510101)
                ·
                  refine ⟨248895027488262962754143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10619521172832553077510101 248895027488262962754143)
                  ·
                    rfl

theorem cell21_1090623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_1090623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090623 prefixEnd_1090623 := by exact prefixLift 1090623
  have htrace : WordTrace (prefixWord ++ tailWord_1090623) baseStart_1090623 baseEnd_1090623 := by
    simpa [prefixWord, tailWord_1090623, baseEnd_1090623] using wordTrace_append hprefix tailTrace_1090623
  have hstable : (prefixWord ++ tailWord_1090623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090623).length < 2 ^ (prefixWord ++ tailWord_1090623).sum := by decide
  have hdescent : baseEnd_1090623 < baseStart_1090623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090646 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1090646 : Nat := 118140960795 + 1090646 * 2 ^ 59
def prefixEnd_1090646 : Nat := 4983230072969 + 3 ^ 40 * 1090646 * 2
def baseEnd_1090646 : Nat := 248900276401620033870763

theorem tailTrace_1090646 : CollatzResearch.WordTrace tailWord_1090646 prefixEnd_1090646 248900276401620033870763 := by
  unfold tailWord_1090646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486195475423955272024737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26519418404522189568263861 2486195475423955272024737)
  ·
    refine ⟨1864646606567966454018553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2486195475423955272024737 1864646606567966454018553)
    ·
      refine ⟨1398484954925974840513915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1864646606567966454018553 1398484954925974840513915)
      ·
        refine ⟨2097727432388962260770873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398484954925974840513915 2097727432388962260770873)
        ·
          refine ⟨1573295574291721695578155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2097727432388962260770873 1573295574291721695578155)
          ·
            refine ⟨2359943361437582543367233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573295574291721695578155 2359943361437582543367233)
            ·
              refine ⟨1769957521078186907525425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2359943361437582543367233 1769957521078186907525425)
              ·
                refine ⟨1327468140808640180644069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1769957521078186907525425 1327468140808640180644069)
                ·
                  refine ⟨248900276401620033870763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1327468140808640180644069 248900276401620033870763)
                  ·
                    rfl

theorem cell21_1090646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1090646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090646 prefixEnd_1090646 := by exact prefixLift 1090646
  have htrace : WordTrace (prefixWord ++ tailWord_1090646) baseStart_1090646 baseEnd_1090646 := by
    simpa [prefixWord, tailWord_1090646, baseEnd_1090646] using wordTrace_append hprefix tailTrace_1090646
  have hstable : (prefixWord ++ tailWord_1090646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090646).length < 2 ^ (prefixWord ++ tailWord_1090646).sum := by decide
  have hdescent : baseEnd_1090646 < baseStart_1090646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090716 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1090716 : Nat := 118140960795 + 1090716 * 2 ^ 59
def prefixEnd_1090716 : Nat := 4983230072969 + 3 ^ 40 * 1090716 * 2
def baseEnd_1090716 : Nat := 248916251355315467703953

theorem tailTrace_1090716 : CollatzResearch.WordTrace tailWord_1090716 prefixEnd_1090716 248916251355315467703953 := by
  unfold tailWord_1090716
  simp only [CollatzResearch.WordTrace]
  refine ⟨19890840358264843153722001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26521120477686457538296001 19890840358264843153722001)
  ·
    refine ⟨14918130268698632365291501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19890840358264843153722001 14918130268698632365291501)
    ·
      refine ⟨5594298850761987136984313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14918130268698632365291501 5594298850761987136984313)
      ·
        refine ⟨4195724138071490352738235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5594298850761987136984313 4195724138071490352738235)
        ·
          refine ⟨6293586207107235529107353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4195724138071490352738235 6293586207107235529107353)
          ·
            refine ⟨4720189655330426646830515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6293586207107235529107353 4720189655330426646830515)
            ·
              refine ⟨7080284482995639970245773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4720189655330426646830515 7080284482995639970245773)
              ·
                refine ⟨2655106681123364988842165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7080284482995639970245773 2655106681123364988842165)
                ·
                  refine ⟨248916251355315467703953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2655106681123364988842165 248916251355315467703953)
                  ·
                    rfl

theorem cell21_1090716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1090716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090716 prefixEnd_1090716 := by exact prefixLift 1090716
  have htrace : WordTrace (prefixWord ++ tailWord_1090716) baseStart_1090716 baseEnd_1090716 := by
    simpa [prefixWord, tailWord_1090716, baseEnd_1090716] using wordTrace_append hprefix tailTrace_1090716
  have hstable : (prefixWord ++ tailWord_1090716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090716).length < 2 ^ (prefixWord ++ tailWord_1090716).sum := by decide
  have hdescent : baseEnd_1090716 < baseStart_1090716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090750 : List Nat := [4, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_1090750 : Nat := 118140960795 + 1090750 * 2 ^ 59
def prefixEnd_1090750 : Nat := 4983230072969 + 3 ^ 40 * 1090750 * 2
def baseEnd_1090750 : Nat := 248924010618538964137217

theorem tailTrace_1090750 : CollatzResearch.WordTrace tailWord_1090750 prefixEnd_1090750 248924010618538964137217 := by
  unfold tailWord_1090750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4972865099800813764272713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26521947198937673409454469 4972865099800813764272713)
  ·
    refine ⟨3729648824850610323204535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4972865099800813764272713 3729648824850610323204535)
    ·
      refine ⟨5594473237275915484806803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3729648824850610323204535 5594473237275915484806803)
      ·
        refine ⟨8391709855913873227210205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594473237275915484806803 8391709855913873227210205)
        ·
          refine ⟨3146891195967702460203827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8391709855913873227210205 3146891195967702460203827)
          ·
            refine ⟨4720336793951553690305741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146891195967702460203827 4720336793951553690305741)
            ·
              refine ⟨1770126297731832633864653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4720336793951553690305741 1770126297731832633864653)
              ·
                refine ⟨663797361649437237699245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1770126297731832633864653 663797361649437237699245)
                ·
                  refine ⟨248924010618538964137217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663797361649437237699245 248924010618538964137217)
                  ·
                    rfl

theorem cell21_1090750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_1090750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090750 prefixEnd_1090750 := by exact prefixLift 1090750
  have htrace : WordTrace (prefixWord ++ tailWord_1090750) baseStart_1090750 baseEnd_1090750 := by
    simpa [prefixWord, tailWord_1090750, baseEnd_1090750] using wordTrace_append hprefix tailTrace_1090750
  have hstable : (prefixWord ++ tailWord_1090750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090750).length < 2 ^ (prefixWord ++ tailWord_1090750).sum := by decide
  have hdescent : baseEnd_1090750 < baseStart_1090750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090851 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 7]
def baseStart_1090851 : Nat := 118140960795 + 1090851 * 2 ^ 59
def prefixEnd_1090851 : Nat := 4983230072969 + 3 ^ 40 * 1090851 * 2
def baseEnd_1090851 : Nat := 248947060194585232953677

theorem tailTrace_1090851 : CollatzResearch.WordTrace tailWord_1090851 prefixEnd_1090851 248947060194585232953677 := by
  unfold tailWord_1090851
  simp only [CollatzResearch.WordTrace]
  refine ⟨39786604571040604363608407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26524403047360402909072271 39786604571040604363608407)
  ·
    refine ⟨59679906856560906545412611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39786604571040604363608407 59679906856560906545412611)
    ·
      refine ⟨89519860284841359818118917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59679906856560906545412611 89519860284841359818118917)
      ·
        refine ⟨16784973803407754965897297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89519860284841359818118917 16784973803407754965897297)
        ·
          refine ⟨12588730352555816224422973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16784973803407754965897297 12588730352555816224422973)
          ·
            refine ⟨4720773882208431084158615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12588730352555816224422973 4720773882208431084158615)
            ·
              refine ⟨7081160823312646626237923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4720773882208431084158615 7081160823312646626237923)
              ·
                refine ⟨10621741234968969939356885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081160823312646626237923 10621741234968969939356885)
                ·
                  refine ⟨248947060194585232953677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10621741234968969939356885 248947060194585232953677)
                  ·
                    rfl

theorem cell21_1090851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_1090851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090851 prefixEnd_1090851 := by exact prefixLift 1090851
  have htrace : WordTrace (prefixWord ++ tailWord_1090851) baseStart_1090851 baseEnd_1090851 := by
    simpa [prefixWord, tailWord_1090851, baseEnd_1090851] using wordTrace_append hprefix tailTrace_1090851
  have hstable : (prefixWord ++ tailWord_1090851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090851).length < 2 ^ (prefixWord ++ tailWord_1090851).sum := by decide
  have hdescent : baseEnd_1090851 < baseStart_1090851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090868 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1090868 : Nat := 118140960795 + 1090868 * 2 ^ 59
def prefixEnd_1090868 : Nat := 4983230072969 + 3 ^ 40 * 1090868 * 2
def baseEnd_1090868 : Nat := 248950939826196981170309

theorem tailTrace_1090868 : CollatzResearch.WordTrace tailWord_1090868 prefixEnd_1090868 248950939826196981170309 := by
  unfold tailWord_1090868
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893612305989508133488629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26524816407986010844651505 19893612305989508133488629)
  ·
    refine ⟨1865026153686516387514559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19893612305989508133488629 1865026153686516387514559)
    ·
      refine ⟨2797539230529774581271839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1865026153686516387514559 2797539230529774581271839)
      ·
        refine ⟨4196308845794661871907759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2797539230529774581271839 4196308845794661871907759)
        ·
          refine ⟨6294463268691992807861639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196308845794661871907759 6294463268691992807861639)
          ·
            refine ⟨9441694903037989211792459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294463268691992807861639 9441694903037989211792459)
            ·
              refine ⟨14162542354556983817688689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9441694903037989211792459 14162542354556983817688689)
              ·
                refine ⟨10621906765917737863266517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14162542354556983817688689 10621906765917737863266517)
                ·
                  refine ⟨248950939826196981170309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10621906765917737863266517 248950939826196981170309)
                  ·
                    rfl

theorem cell21_1090868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1090868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090868 prefixEnd_1090868 := by exact prefixLift 1090868
  have htrace : WordTrace (prefixWord ++ tailWord_1090868) baseStart_1090868 baseEnd_1090868 := by
    simpa [prefixWord, tailWord_1090868, baseEnd_1090868] using wordTrace_append hprefix tailTrace_1090868
  have hstable : (prefixWord ++ tailWord_1090868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090868).length < 2 ^ (prefixWord ++ tailWord_1090868).sum := by decide
  have hdescent : baseEnd_1090868 < baseStart_1090868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090896 : List Nat := [2, 1, 1, 1, 1, 5, 2, 8]
def baseStart_1090896 : Nat := 118140960795 + 1090896 * 2 ^ 59
def prefixEnd_1090896 : Nat := 4983230072969 + 3 ^ 40 * 1090896 * 2
def baseEnd_1090896 : Nat := 82985776602558384901195

theorem tailTrace_1090896 : CollatzResearch.WordTrace tailWord_1090896 prefixEnd_1090896 82985776602558384901195 := by
  unfold tailWord_1090896
  simp only [CollatzResearch.WordTrace]
  refine ⟨19894122927938788524498271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26525497237251718032664361 19894122927938788524498271)
  ·
    refine ⟨29841184391908182786747407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19894122927938788524498271 29841184391908182786747407)
    ·
      refine ⟨44761776587862274180121111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29841184391908182786747407 44761776587862274180121111)
      ·
        refine ⟨67142664881793411270181667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44761776587862274180121111 67142664881793411270181667)
        ·
          refine ⟨100713997322690116905272501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67142664881793411270181667 100713997322690116905272501)
          ·
            refine ⟨9441937249002198459869297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100713997322690116905272501 9441937249002198459869297)
            ·
              refine ⟨7081452936751648844901973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9441937249002198459869297 7081452936751648844901973)
              ·
                refine ⟨82985776602558384901195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7081452936751648844901973 82985776602558384901195)
                ·
                  rfl

theorem cell21_1090896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_1090896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090896 prefixEnd_1090896 := by exact prefixLift 1090896
  have htrace : WordTrace (prefixWord ++ tailWord_1090896) baseStart_1090896 baseEnd_1090896 := by
    simpa [prefixWord, tailWord_1090896, baseEnd_1090896] using wordTrace_append hprefix tailTrace_1090896
  have hstable : (prefixWord ++ tailWord_1090896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090896).length < 2 ^ (prefixWord ++ tailWord_1090896).sum := by decide
  have hdescent : baseEnd_1090896 < baseStart_1090896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090899 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 4]
def baseStart_1090899 : Nat := 118140960795 + 1090899 * 2 ^ 59
def prefixEnd_1090899 : Nat := 4983230072969 + 3 ^ 40 * 1090899 * 2
def baseEnd_1090899 : Nat := 248958014448547816153579

theorem tailTrace_1090899 : CollatzResearch.WordTrace tailWord_1090899 prefixEnd_1090899 248958014448547816153579 := by
  unfold tailWord_1090899
  simp only [CollatzResearch.WordTrace]
  refine ⟨39788355274866708561355751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26525570183244472374237167 39788355274866708561355751)
  ·
    refine ⟨59682532912300062842033627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39788355274866708561355751 59682532912300062842033627)
    ·
      refine ⟨89523799368450094263050441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59682532912300062842033627 89523799368450094263050441)
      ·
        refine ⟨67142849526337570697287831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89523799368450094263050441 67142849526337570697287831)
        ·
          refine ⟨100714274289506356045931747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67142849526337570697287831 100714274289506356045931747)
          ·
            refine ⟨151071411434259534068897621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100714274289506356045931747 151071411434259534068897621)
            ·
              refine ⟨885184051372614457434947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 151071411434259534068897621 885184051372614457434947)
              ·
                refine ⟨1327776077058921686152421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885184051372614457434947 1327776077058921686152421)
                ·
                  refine ⟨248958014448547816153579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1327776077058921686152421 248958014448547816153579)
                  ·
                    rfl

theorem cell21_1090899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 4].length) (baseStart_1090899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090899 prefixEnd_1090899 := by exact prefixLift 1090899
  have htrace : WordTrace (prefixWord ++ tailWord_1090899) baseStart_1090899 baseEnd_1090899 := by
    simpa [prefixWord, tailWord_1090899, baseEnd_1090899] using wordTrace_append hprefix tailTrace_1090899
  have hstable : (prefixWord ++ tailWord_1090899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090899).length < 2 ^ (prefixWord ++ tailWord_1090899).sum := by decide
  have hdescent : baseEnd_1090899 < baseStart_1090899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090919 : List Nat := [1, 1, 5, 1, 5, 1, 1, 3, 3]
def baseStart_1090919 : Nat := 118140960795 + 1090919 * 2 ^ 59
def prefixEnd_1090919 : Nat := 4983230072969 + 3 ^ 40 * 1090919 * 2
def baseEnd_1090919 : Nat := 248962578721032225820205

theorem tailTrace_1090919 : CollatzResearch.WordTrace tailWord_1090919 prefixEnd_1090919 248962578721032225820205 := by
  unfold tailWord_1090919
  simp only [CollatzResearch.WordTrace]
  refine ⟨39789084734794251977083811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26526056489862834651389207 39789084734794251977083811)
  ·
    refine ⟨59683627102191377965625717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39789084734794251977083811 59683627102191377965625717)
    ·
      refine ⟨5595340040830441684277411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59683627102191377965625717 5595340040830441684277411)
      ·
        refine ⟨8393010061245662526416117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5595340040830441684277411 8393010061245662526416117)
        ·
          refine ⟨786844693241780861851511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8393010061245662526416117 786844693241780861851511)
          ·
            refine ⟨1180267039862671292777267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786844693241780861851511 1180267039862671292777267)
            ·
              refine ⟨1770400559794006939165901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180267039862671292777267 1770400559794006939165901)
              ·
                refine ⟨663900209922752602187213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1770400559794006939165901 663900209922752602187213)
                ·
                  refine ⟨248962578721032225820205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663900209922752602187213 248962578721032225820205)
                  ·
                    rfl

theorem cell21_1090919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 3].length) (baseStart_1090919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090919 prefixEnd_1090919 := by exact prefixLift 1090919
  have htrace : WordTrace (prefixWord ++ tailWord_1090919) baseStart_1090919 baseEnd_1090919 := by
    simpa [prefixWord, tailWord_1090919, baseEnd_1090919] using wordTrace_append hprefix tailTrace_1090919
  have hstable : (prefixWord ++ tailWord_1090919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090919).length < 2 ^ (prefixWord ++ tailWord_1090919).sum := by decide
  have hdescent : baseEnd_1090919 < baseStart_1090919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090944 : List Nat := [2, 1, 1, 2, 1, 2, 1, 8, 3]
def baseStart_1090944 : Nat := 118140960795 + 1090944 * 2 ^ 59
def prefixEnd_1090944 : Nat := 4983230072969 + 3 ^ 40 * 1090944 * 2
def baseEnd_1090944 : Nat := 248968284061637737903487

theorem tailTrace_1090944 : CollatzResearch.WordTrace tailWord_1090944 prefixEnd_1090944 248968284061637737903487 := by
  unfold tailWord_1090944
  simp only [CollatzResearch.WordTrace]
  refine ⟨19894998279851840623371943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26526664373135787497829257 19894998279851840623371943)
  ·
    refine ⟨29842497419777760935057915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19894998279851840623371943 29842497419777760935057915)
    ·
      refine ⟨44763746129666641402586873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29842497419777760935057915 44763746129666641402586873)
      ·
        refine ⟨33572809597249981051940155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44763746129666641402586873 33572809597249981051940155)
        ·
          refine ⟨50359214395874971577910233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33572809597249981051940155 50359214395874971577910233)
          ·
            refine ⟨37769410796906228683432675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50359214395874971577910233 37769410796906228683432675)
            ·
              refine ⟨56654116195359343025149013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37769410796906228683432675 56654116195359343025149013)
              ·
                refine ⟨663915424164367301075965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 56654116195359343025149013 663915424164367301075965)
                ·
                  refine ⟨248968284061637737903487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663915424164367301075965 248968284061637737903487)
                  ·
                    rfl

theorem cell21_1090944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_1090944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090944 prefixEnd_1090944 := by exact prefixLift 1090944
  have htrace : WordTrace (prefixWord ++ tailWord_1090944) baseStart_1090944 baseEnd_1090944 := by
    simpa [prefixWord, tailWord_1090944, baseEnd_1090944] using wordTrace_append hprefix tailTrace_1090944
  have hstable : (prefixWord ++ tailWord_1090944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090944).length < 2 ^ (prefixWord ++ tailWord_1090944).sum := by decide
  have hdescent : baseEnd_1090944 < baseStart_1090944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1090989 : List Nat := [1, 5, 2, 2, 1, 10]
def baseStart_1090989 : Nat := 118140960795 + 1090989 * 2 ^ 59
def prefixEnd_1090989 : Nat := 4983230072969 + 3 ^ 40 * 1090989 * 2
def baseEnd_1090989 : Nat := 9221427913878802209385

theorem tailTrace_1090989 : CollatzResearch.WordTrace tailWord_1090989 prefixEnd_1090989 9221427913878802209385 := by
  unfold tailWord_1090989
  simp only [CollatzResearch.WordTrace]
  refine ⟨39791637844540653932132021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26527758563027102621421347 39791637844540653932132021)
  ·
    refine ⟨3730466047925686306137377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39791637844540653932132021 3730466047925686306137377)
    ·
      refine ⟨2797849535944264729603033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3730466047925686306137377 2797849535944264729603033)
      ·
        refine ⟨2098387151958198547202275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2797849535944264729603033 2098387151958198547202275)
        ·
          refine ⟨3147580727937297820803413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098387151958198547202275 3147580727937297820803413)
          ·
            refine ⟨9221427913878802209385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3147580727937297820803413 9221427913878802209385)
            ·
              rfl

theorem cell21_1090989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 10].length) (baseStart_1090989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1090989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1090989 prefixEnd_1090989 := by exact prefixLift 1090989
  have htrace : WordTrace (prefixWord ++ tailWord_1090989) baseStart_1090989 baseEnd_1090989 := by
    simpa [prefixWord, tailWord_1090989, baseEnd_1090989] using wordTrace_append hprefix tailTrace_1090989
  have hstable : (prefixWord ++ tailWord_1090989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1090989).length < 2 ^ (prefixWord ++ tailWord_1090989).sum := by decide
  have hdescent : baseEnd_1090989 < baseStart_1090989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1090989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091017 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 8]
def baseStart_1091017 : Nat := 118140960795 + 1091017 * 2 ^ 59
def prefixEnd_1091017 : Nat := 4983230072969 + 3 ^ 40 * 1091017 * 2
def baseEnd_1091017 : Nat := 248984943656205833186671

theorem tailTrace_1091017 : CollatzResearch.WordTrace tailWord_1091017 prefixEnd_1091017 248984943656205833186671 := by
  unfold tailWord_1091017
  simp only [CollatzResearch.WordTrace]
  refine ⟨39792659088439214714151305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26528439392292809809434203 39792659088439214714151305)
  ·
    refine ⟨29844494316329411035613479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39792659088439214714151305 29844494316329411035613479)
    ·
      refine ⟨44766741474494116553420219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29844494316329411035613479 44766741474494116553420219)
      ·
        refine ⟨67150112211741174830130329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44766741474494116553420219 67150112211741174830130329)
        ·
          refine ⟨50362584158805881122597747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67150112211741174830130329 50362584158805881122597747)
          ·
            refine ⟨75543876238208821683896621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50362584158805881122597747 75543876238208821683896621)
            ·
              refine ⟨28328953589328308131461233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75543876238208821683896621 28328953589328308131461233)
              ·
                refine ⟨21246715191996231098595925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28328953589328308131461233 21246715191996231098595925)
                ·
                  refine ⟨248984943656205833186671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21246715191996231098595925 248984943656205833186671)
                  ·
                    rfl

theorem cell21_1091017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_1091017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091017 prefixEnd_1091017 := by exact prefixLift 1091017
  have htrace : WordTrace (prefixWord ++ tailWord_1091017) baseStart_1091017 baseEnd_1091017 := by
    simpa [prefixWord, tailWord_1091017, baseEnd_1091017] using wordTrace_append hprefix tailTrace_1091017
  have hstable : (prefixWord ++ tailWord_1091017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091017).length < 2 ^ (prefixWord ++ tailWord_1091017).sum := by decide
  have hdescent : baseEnd_1091017 < baseStart_1091017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091020 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1091020 : Nat := 118140960795 + 1091020 * 2 ^ 59
def prefixEnd_1091020 : Nat := 4983230072969 + 3 ^ 40 * 1091020 * 2
def baseEnd_1091020 : Nat := 248985628297078494636665

theorem tailTrace_1091020 : CollatzResearch.WordTrace tailWord_1091020 prefixEnd_1091020 248985628297078494636665 := by
  unfold tailWord_1091020
  simp only [CollatzResearch.WordTrace]
  refine ⟨19896384253714173113255257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26528512338285564151007009 19896384253714173113255257)
  ·
    refine ⟨14922288190285629834941443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19896384253714173113255257 14922288190285629834941443)
    ·
      refine ⟨22383432285428444752412165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14922288190285629834941443 22383432285428444752412165)
      ·
        refine ⟨4196893553517833391077281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22383432285428444752412165 4196893553517833391077281)
        ·
          refine ⟨3147670165138375043307961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4196893553517833391077281 3147670165138375043307961)
          ·
            refine ⟨2360752623853781282480971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147670165138375043307961 2360752623853781282480971)
            ·
              refine ⟨3541128935780671923721457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360752623853781282480971 3541128935780671923721457)
              ·
                refine ⟨2655846701835503942791093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541128935780671923721457 2655846701835503942791093)
                ·
                  refine ⟨248985628297078494636665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2655846701835503942791093 248985628297078494636665)
                  ·
                    rfl

theorem cell21_1091020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1091020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091020 prefixEnd_1091020 := by exact prefixLift 1091020
  have htrace : WordTrace (prefixWord ++ tailWord_1091020) baseStart_1091020 baseEnd_1091020 := by
    simpa [prefixWord, tailWord_1091020, baseEnd_1091020] using wordTrace_append hprefix tailTrace_1091020
  have hstable : (prefixWord ++ tailWord_1091020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091020).length < 2 ^ (prefixWord ++ tailWord_1091020).sum := by decide
  have hdescent : baseEnd_1091020 < baseStart_1091020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091037 : List Nat := [1, 4, 3, 1, 1, 2, 1, 5, 3]
def baseStart_1091037 : Nat := 118140960795 + 1091037 * 2 ^ 59
def prefixEnd_1091037 : Nat := 4983230072969 + 3 ^ 40 * 1091037 * 2
def baseEnd_1091037 : Nat := 248989507928690242853297

theorem tailTrace_1091037 : CollatzResearch.WordTrace tailWord_1091037 prefixEnd_1091037 248989507928690242853297 := by
  unfold tailWord_1091037
  simp only [CollatzResearch.WordTrace]
  refine ⟨39793388548366758129879365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26528925698911172086586243 39793388548366758129879365)
  ·
    refine ⟨7461260352818767149352381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39793388548366758129879365 7461260352818767149352381)
    ·
      refine ⟨2797972632307037681007143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7461260352818767149352381 2797972632307037681007143)
      ·
        refine ⟨4196958948460556521510715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2797972632307037681007143 4196958948460556521510715)
        ·
          refine ⟨6295438422690834782266073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196958948460556521510715 6295438422690834782266073)
          ·
            refine ⟨4721578817018126086699555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6295438422690834782266073 4721578817018126086699555)
            ·
              refine ⟨7082368225527189130049333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721578817018126086699555 7082368225527189130049333)
              ·
                refine ⟨663972021143173980942125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7082368225527189130049333 663972021143173980942125)
                ·
                  refine ⟨248989507928690242853297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663972021143173980942125 248989507928690242853297)
                  ·
                    rfl

theorem cell21_1091037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_1091037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091037 prefixEnd_1091037 := by exact prefixLift 1091037
  have htrace : WordTrace (prefixWord ++ tailWord_1091037) baseStart_1091037 baseEnd_1091037 := by
    simpa [prefixWord, tailWord_1091037, baseEnd_1091037] using wordTrace_append hprefix tailTrace_1091037
  have hstable : (prefixWord ++ tailWord_1091037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091037).length < 2 ^ (prefixWord ++ tailWord_1091037).sum := by decide
  have hdescent : baseEnd_1091037 < baseStart_1091037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091048 : List Nat := [2, 1, 4, 1, 1, 2, 10]
def baseStart_1091048 : Nat := 118140960795 + 1091048 * 2 ^ 59
def prefixEnd_1091048 : Nat := 4983230072969 + 3 ^ 40 * 1091048 * 2
def baseEnd_1091048 : Nat := 27665779808728518685549

theorem tailTrace_1091048 : CollatzResearch.WordTrace tailWord_1091048 prefixEnd_1091048 27665779808728518685549 := by
  unfold tailWord_1091048
  simp only [CollatzResearch.WordTrace]
  refine ⟨19896894875663453504264899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26529193167551271339019865 19896894875663453504264899)
  ·
    refine ⟨29845342313495180256397349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19896894875663453504264899 29845342313495180256397349)
    ·
      refine ⟨5596001683780346298074503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29845342313495180256397349 5596001683780346298074503)
      ·
        refine ⟨8394002525670519447111755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5596001683780346298074503 8394002525670519447111755)
        ·
          refine ⟨12591003788505779170667633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8394002525670519447111755 12591003788505779170667633)
          ·
            refine ⟨9443252841379334378000725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12591003788505779170667633 9443252841379334378000725)
            ·
              refine ⟨27665779808728518685549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9443252841379334378000725 27665779808728518685549)
              ·
                rfl

theorem cell21_1091048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 10].length) (baseStart_1091048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091048 prefixEnd_1091048 := by exact prefixLift 1091048
  have htrace : WordTrace (prefixWord ++ tailWord_1091048) baseStart_1091048 baseEnd_1091048 := by
    simpa [prefixWord, tailWord_1091048, baseEnd_1091048] using wordTrace_append hprefix tailTrace_1091048
  have hstable : (prefixWord ++ tailWord_1091048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091048).length < 2 ^ (prefixWord ++ tailWord_1091048).sum := by decide
  have hdescent : baseEnd_1091048 < baseStart_1091048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091082 : List Nat := [3, 1, 2, 2, 2, 4, 2, 5]
def baseStart_1091082 : Nat := 118140960795 + 1091082 * 2 ^ 59
def prefixEnd_1091082 : Nat := 4983230072969 + 3 ^ 40 * 1091082 * 2
def baseEnd_1091082 : Nat := 82999925847260054867735

theorem tailTrace_1091082 : CollatzResearch.WordTrace tailWord_1091082 prefixEnd_1091082 82999925847260054867735 := by
  unfold tailWord_1091082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9948757458300932703816875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26530019888802487210178333 9948757458300932703816875)
  ·
    refine ⟨14923136187451399055725313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9948757458300932703816875 14923136187451399055725313)
    ·
      refine ⟨11192352140588549291793985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14923136187451399055725313 11192352140588549291793985)
      ·
        refine ⟨8394264105441411968845489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11192352140588549291793985 8394264105441411968845489)
        ·
          refine ⟨6295698079081058976634117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8394264105441411968845489 6295698079081058976634117)
          ·
            refine ⟨1180443389827698558118897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6295698079081058976634117 1180443389827698558118897)
            ·
              refine ⟨885332542370773918589173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180443389827698558118897 885332542370773918589173)
              ·
                refine ⟨82999925847260054867735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 885332542370773918589173 82999925847260054867735)
                ·
                  rfl

theorem cell21_1091082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_1091082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091082 prefixEnd_1091082 := by exact prefixLift 1091082
  have htrace : WordTrace (prefixWord ++ tailWord_1091082) baseStart_1091082 baseEnd_1091082 := by
    simpa [prefixWord, tailWord_1091082, baseEnd_1091082] using wordTrace_append hprefix tailTrace_1091082
  have hstable : (prefixWord ++ tailWord_1091082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091082).length < 2 ^ (prefixWord ++ tailWord_1091082).sum := by decide
  have hdescent : baseEnd_1091082 < baseStart_1091082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091127 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 4]
def baseStart_1091127 : Nat := 118140960795 + 1091127 * 2 ^ 59
def prefixEnd_1091127 : Nat := 4983230072969 + 3 ^ 40 * 1091127 * 2
def baseEnd_1091127 : Nat := 249010047154870086353113

theorem tailTrace_1091127 : CollatzResearch.WordTrace tailWord_1091127 prefixEnd_1091127 249010047154870086353113 := by
  unfold tailWord_1091127
  simp only [CollatzResearch.WordTrace]
  refine ⟨39796671118040703500655635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26531114078693802333770423 39796671118040703500655635)
  ·
    refine ⟨59695006677061055250983453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39796671118040703500655635 59695006677061055250983453)
    ·
      refine ⟨22385627503897895719118795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59695006677061055250983453 22385627503897895719118795)
      ·
        refine ⟨33578441255846843578678193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22385627503897895719118795 33578441255846843578678193)
        ·
          refine ⟨25183830941885132684008645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33578441255846843578678193 25183830941885132684008645)
          ·
            refine ⟨4721968301603462378251621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25183830941885132684008645 4721968301603462378251621)
            ·
              refine ⟨885369056550649195922179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4721968301603462378251621 885369056550649195922179)
              ·
                refine ⟨1328053584825973793883269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885369056550649195922179 1328053584825973793883269)
                ·
                  refine ⟨249010047154870086353113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328053584825973793883269 249010047154870086353113)
                  ·
                    rfl

theorem cell21_1091127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 4].length) (baseStart_1091127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091127 prefixEnd_1091127 := by exact prefixLift 1091127
  have htrace : WordTrace (prefixWord ++ tailWord_1091127) baseStart_1091127 baseEnd_1091127 := by
    simpa [prefixWord, tailWord_1091127, baseEnd_1091127] using wordTrace_append hprefix tailTrace_1091127
  have hstable : (prefixWord ++ tailWord_1091127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091127).length < 2 ^ (prefixWord ++ tailWord_1091127).sum := by decide
  have hdescent : baseEnd_1091127 < baseStart_1091127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091158 : List Nat := [5, 2, 2, 2, 10]
def baseStart_1091158 : Nat := 118140960795 + 1091158 * 2 ^ 59
def prefixEnd_1091158 : Nat := 4983230072969 + 3 ^ 40 * 1091158 * 2
def baseEnd_1091158 : Nat := 3074285454039764460943

theorem tailTrace_1091158 : CollatzResearch.WordTrace tailWord_1091158 prefixEnd_1091158 3074285454039764460943 := by
  unfold tailWord_1091158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487362611308024737189633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26531867853952263863356085 2487362611308024737189633)
  ·
    refine ⟨1865521958481018552892225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2487362611308024737189633 1865521958481018552892225)
    ·
      refine ⟨1399141468860763914669169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1865521958481018552892225 1399141468860763914669169)
      ·
        refine ⟨1049356101645572936001877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1399141468860763914669169 1049356101645572936001877)
        ·
          refine ⟨3074285454039764460943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1049356101645572936001877 3074285454039764460943)
          ·
            rfl

theorem cell21_1091158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 10].length) (baseStart_1091158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091158 prefixEnd_1091158 := by exact prefixLift 1091158
  have htrace : WordTrace (prefixWord ++ tailWord_1091158) baseStart_1091158 baseEnd_1091158 := by
    simpa [prefixWord, tailWord_1091158, baseEnd_1091158] using wordTrace_append hprefix tailTrace_1091158
  have hstable : (prefixWord ++ tailWord_1091158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091158).length < 2 ^ (prefixWord ++ tailWord_1091158).sum := by decide
  have hdescent : baseEnd_1091158 < baseStart_1091158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091262 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1091262 : Nat := 118140960795 + 1091262 * 2 ^ 59
def prefixEnd_1091262 : Nat := 4983230072969 + 3 ^ 40 * 1091262 * 2
def baseEnd_1091262 : Nat := 249040855994139851602837

theorem tailTrace_1091262 : CollatzResearch.WordTrace tailWord_1091262 prefixEnd_1091262 249040855994139851602837 := by
  unfold tailWord_1091262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975199371568952694602505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26534396648367747704546693 4975199371568952694602505)
  ·
    refine ⟨3731399528676714520951879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4975199371568952694602505 3731399528676714520951879)
    ·
      refine ⟨5597099293015071781427819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3731399528676714520951879 5597099293015071781427819)
      ·
        refine ⟨8395648939522607672141729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597099293015071781427819 8395648939522607672141729)
        ·
          refine ⟨6296736704641955754106297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8395648939522607672141729 6296736704641955754106297)
          ·
            refine ⟨4722552528481466815579723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296736704641955754106297 4722552528481466815579723)
            ·
              refine ⟨7083828792722200223369585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722552528481466815579723 7083828792722200223369585)
              ·
                refine ⟨5312871594541650167527189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083828792722200223369585 5312871594541650167527189)
                ·
                  refine ⟨249040855994139851602837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5312871594541650167527189 249040855994139851602837)
                  ·
                    rfl

theorem cell21_1091262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1091262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091262 prefixEnd_1091262 := by exact prefixLift 1091262
  have htrace : WordTrace (prefixWord ++ tailWord_1091262) baseStart_1091262 baseEnd_1091262 := by
    simpa [prefixWord, tailWord_1091262, baseEnd_1091262] using wordTrace_append hprefix tailTrace_1091262
  have hstable : (prefixWord ++ tailWord_1091262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091262).length < 2 ^ (prefixWord ++ tailWord_1091262).sum := by decide
  have hdescent : baseEnd_1091262 < baseStart_1091262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091282 : List Nat := [3, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_1091282 : Nat := 118140960795 + 1091282 * 2 ^ 59
def prefixEnd_1091282 : Nat := 4983230072969 + 3 ^ 40 * 1091282 * 2
def baseEnd_1091282 : Nat := 249045420266624261269463

theorem tailTrace_1091282 : CollatzResearch.WordTrace tailWord_1091282 prefixEnd_1091282 249045420266624261269463 := by
  unfold tailWord_1091282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9950581108119791243137025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26534882954986109981698733 9950581108119791243137025)
  ·
    refine ⟨7462935831089843432352769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9950581108119791243137025 7462935831089843432352769)
    ·
      refine ⟨5597201873317382574264577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7462935831089843432352769 5597201873317382574264577)
      ·
        refine ⟨4197901404988036930698433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5597201873317382574264577 4197901404988036930698433)
        ·
          refine ⟨3148426053741027698023825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4197901404988036930698433 3148426053741027698023825)
          ·
            refine ⟨2361319540305770773517869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3148426053741027698023825 2361319540305770773517869)
            ·
              refine ⟨885494827614664040069201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2361319540305770773517869 885494827614664040069201)
              ·
                refine ⟨664121120710998030051901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885494827614664040069201 664121120710998030051901)
                ·
                  refine ⟨249045420266624261269463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664121120710998030051901 249045420266624261269463)
                  ·
                    rfl

theorem cell21_1091282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_1091282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091282 prefixEnd_1091282 := by exact prefixLift 1091282
  have htrace : WordTrace (prefixWord ++ tailWord_1091282) baseStart_1091282 baseEnd_1091282 := by
    simpa [prefixWord, tailWord_1091282, baseEnd_1091282] using wordTrace_append hprefix tailTrace_1091282
  have hstable : (prefixWord ++ tailWord_1091282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091282).length < 2 ^ (prefixWord ++ tailWord_1091282).sum := by decide
  have hdescent : baseEnd_1091282 < baseStart_1091282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091324 : List Nat := [2, 2, 2, 1, 3, 1, 2, 5, 3]
def baseStart_1091324 : Nat := 118140960795 + 1091324 * 2 ^ 59
def prefixEnd_1091324 : Nat := 4983230072969 + 3 ^ 40 * 1091324 * 2
def baseEnd_1091324 : Nat := 249055005238841521569377

theorem tailTrace_1091324 : CollatzResearch.WordTrace tailWord_1091324 prefixEnd_1091324 249055005238841521569377 := by
  unfold tailWord_1091324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19901928149163503072788513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26535904198884670763718017 19901928149163503072788513)
  ·
    refine ⟨14926446111872627304591385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19901928149163503072788513 14926446111872627304591385)
    ·
      refine ⟨11194834583904470478443539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14926446111872627304591385 11194834583904470478443539)
      ·
        refine ⟨16792251875856705717665309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11194834583904470478443539 16792251875856705717665309)
        ·
          refine ⟨6297094453446264644124491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16792251875856705717665309 6297094453446264644124491)
          ·
            refine ⟨9445641680169396966186737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6297094453446264644124491 9445641680169396966186737)
            ·
              refine ⟨7084231260127047724640053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9445641680169396966186737 7084231260127047724640053)
              ·
                refine ⟨664146680636910724185005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7084231260127047724640053 664146680636910724185005)
                ·
                  refine ⟨249055005238841521569377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664146680636910724185005 249055005238841521569377)
                  ·
                    rfl

theorem cell21_1091324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_1091324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091324 prefixEnd_1091324 := by exact prefixLift 1091324
  have htrace : WordTrace (prefixWord ++ tailWord_1091324) baseStart_1091324 baseEnd_1091324 := by
    simpa [prefixWord, tailWord_1091324, baseEnd_1091324] using wordTrace_append hprefix tailTrace_1091324
  have hstable : (prefixWord ++ tailWord_1091324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091324).length < 2 ^ (prefixWord ++ tailWord_1091324).sum := by decide
  have hdescent : baseEnd_1091324 < baseStart_1091324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091338 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_1091338 : Nat := 118140960795 + 1091338 * 2 ^ 59
def prefixEnd_1091338 : Nat := 4983230072969 + 3 ^ 40 * 1091338 * 2
def baseEnd_1091338 : Nat := 249058200229580608336015

theorem tailTrace_1091338 : CollatzResearch.WordTrace tailWord_1091338 prefixEnd_1091338 249058200229580608336015 := by
  unfold tailWord_1091338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9951091730069071634146667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26536244613517524357724445 9951091730069071634146667)
  ·
    refine ⟨14926637595103607451220001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9951091730069071634146667 14926637595103607451220001)
    ·
      refine ⟨11194978196327705588415001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14926637595103607451220001 11194978196327705588415001)
      ·
        refine ⟨8396233647245779191311251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11194978196327705588415001 8396233647245779191311251)
        ·
          refine ⟨12594350470868668786966877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8396233647245779191311251 12594350470868668786966877)
          ·
            refine ⟨4722881426575750795112579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12594350470868668786966877 4722881426575750795112579)
            ·
              refine ⟨7084322139863626192668869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722881426575750795112579 7084322139863626192668869)
              ·
                refine ⟨1328310401224429911125413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7084322139863626192668869 1328310401224429911125413)
                ·
                  refine ⟨249058200229580608336015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328310401224429911125413 249058200229580608336015)
                  ·
                    rfl

theorem cell21_1091338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_1091338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091338 prefixEnd_1091338 := by exact prefixLift 1091338
  have htrace : WordTrace (prefixWord ++ tailWord_1091338) baseStart_1091338 baseEnd_1091338 := by
    simpa [prefixWord, tailWord_1091338, baseEnd_1091338] using wordTrace_append hprefix tailTrace_1091338
  have hstable : (prefixWord ++ tailWord_1091338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091338).length < 2 ^ (prefixWord ++ tailWord_1091338).sum := by decide
  have hdescent : baseEnd_1091338 < baseStart_1091338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091352 : List Nat := [2, 1, 2, 3, 1, 1, 5, 6]
def baseStart_1091352 : Nat := 118140960795 + 1091352 * 2 ^ 59
def prefixEnd_1091352 : Nat := 4983230072969 + 3 ^ 40 * 1091352 * 2
def baseEnd_1091352 : Nat := 83020465073439898367551

theorem tailTrace_1091352 : CollatzResearch.WordTrace tailWord_1091352 prefixEnd_1091352 83020465073439898367551 := by
  unfold tailWord_1091352
  simp only [CollatzResearch.WordTrace]
  refine ⟨19902438771112783463798155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26536585028150377951730873 19902438771112783463798155)
  ·
    refine ⟨29853658156669175195697233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19902438771112783463798155 29853658156669175195697233)
    ·
      refine ⟨22390243617501881396772925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29853658156669175195697233 22390243617501881396772925)
      ·
        refine ⟨8396341356563205523789847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22390243617501881396772925 8396341356563205523789847)
        ·
          refine ⟨12594512034844808285684771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8396341356563205523789847 12594512034844808285684771)
          ·
            refine ⟨18891768052267212428527157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12594512034844808285684771 18891768052267212428527157)
            ·
              refine ⟨1771103254900051165174421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18891768052267212428527157 1771103254900051165174421)
              ·
                refine ⟨83020465073439898367551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1771103254900051165174421 83020465073439898367551)
                ·
                  rfl

theorem cell21_1091352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_1091352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091352 prefixEnd_1091352 := by exact prefixLift 1091352
  have htrace : WordTrace (prefixWord ++ tailWord_1091352) baseStart_1091352 baseEnd_1091352 := by
    simpa [prefixWord, tailWord_1091352, baseEnd_1091352] using wordTrace_append hprefix tailTrace_1091352
  have hstable : (prefixWord ++ tailWord_1091352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091352).length < 2 ^ (prefixWord ++ tailWord_1091352).sum := by decide
  have hdescent : baseEnd_1091352 < baseStart_1091352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091358 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1091358 : Nat := 118140960795 + 1091358 * 2 ^ 59
def prefixEnd_1091358 : Nat := 4983230072969 + 3 ^ 40 * 1091358 * 2
def baseEnd_1091358 : Nat := 249062764502065018002641

theorem tailTrace_1091358 : CollatzResearch.WordTrace tailWord_1091358 prefixEnd_1091358 249062764502065018002641 := by
  unfold tailWord_1091358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975637047525478744039341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26536730920135886634876485 4975637047525478744039341)
  ·
    refine ⟨1865863892822054529014753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4975637047525478744039341 1865863892822054529014753)
    ·
      refine ⟨1399397919616540896761065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1865863892822054529014753 1399397919616540896761065)
      ·
        refine ⟨1049548439712405672570799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1399397919616540896761065 1049548439712405672570799)
        ·
          refine ⟨1574322659568608508856199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049548439712405672570799 1574322659568608508856199)
          ·
            refine ⟨2361483989352912763284299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574322659568608508856199 2361483989352912763284299)
            ·
              refine ⟨3542225984029369144926449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361483989352912763284299 3542225984029369144926449)
              ·
                refine ⟨2656669488022026858694837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3542225984029369144926449 2656669488022026858694837)
                ·
                  refine ⟨249062764502065018002641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656669488022026858694837 249062764502065018002641)
                  ·
                    rfl

theorem cell21_1091358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1091358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091358 prefixEnd_1091358 := by exact prefixLift 1091358
  have htrace : WordTrace (prefixWord ++ tailWord_1091358) baseStart_1091358 baseEnd_1091358 := by
    simpa [prefixWord, tailWord_1091358, baseEnd_1091358] using wordTrace_append hprefix tailTrace_1091358
  have hstable : (prefixWord ++ tailWord_1091358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091358).length < 2 ^ (prefixWord ++ tailWord_1091358).sum := by decide
  have hdescent : baseEnd_1091358 < baseStart_1091358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091397 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1091397 : Nat := 118140960795 + 1091397 * 2 ^ 59
def prefixEnd_1091397 : Nat := 4983230072969 + 3 ^ 40 * 1091397 * 2
def baseEnd_1091397 : Nat := 249071664833409616852561

theorem tailTrace_1091397 : CollatzResearch.WordTrace tailWord_1091397 prefixEnd_1091397 249071664833409616852561 := by
  unfold tailWord_1091397
  simp only [CollatzResearch.WordTrace]
  refine ⟨39806518827062539612984445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26537679218041693075322963 39806518827062539612984445)
  ·
    refine ⟨14927444560148452354869167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39806518827062539612984445 14927444560148452354869167)
    ·
      refine ⟨22391166840222678532303751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14927444560148452354869167 22391166840222678532303751)
      ·
        refine ⟨33586750260334017798455627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22391166840222678532303751 33586750260334017798455627)
        ·
          refine ⟨50380125390501026697683441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33586750260334017798455627 50380125390501026697683441)
          ·
            refine ⟨37785094042875770023262581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50380125390501026697683441 37785094042875770023262581)
            ·
              refine ⟨3542352566519603439680867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37785094042875770023262581 3542352566519603439680867)
              ·
                refine ⟨5313528849779405159521301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542352566519603439680867 5313528849779405159521301)
                ·
                  refine ⟨249071664833409616852561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5313528849779405159521301 249071664833409616852561)
                  ·
                    rfl

theorem cell21_1091397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1091397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091397 prefixEnd_1091397 := by exact prefixLift 1091397
  have htrace : WordTrace (prefixWord ++ tailWord_1091397) baseStart_1091397 baseEnd_1091397 := by
    simpa [prefixWord, tailWord_1091397, baseEnd_1091397] using wordTrace_append hprefix tailTrace_1091397
  have hstable : (prefixWord ++ tailWord_1091397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091397).length < 2 ^ (prefixWord ++ tailWord_1091397).sum := by decide
  have hdescent : baseEnd_1091397 < baseStart_1091397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091400 : List Nat := [2, 1, 3, 1, 1, 4, 2, 4, 3]
def baseStart_1091400 : Nat := 118140960795 + 1091400 * 2 ^ 59
def prefixEnd_1091400 : Nat := 4983230072969 + 3 ^ 40 * 1091400 * 2
def baseEnd_1091400 : Nat := 249072349474282278302555

theorem tailTrace_1091400 : CollatzResearch.WordTrace tailWord_1091400 prefixEnd_1091400 249072349474282278302555 := by
  unfold tailWord_1091400
  simp only [CollatzResearch.WordTrace]
  refine ⟨19903314123025835562671827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26537752164034447416895769 19903314123025835562671827)
  ·
    refine ⟨29854971184538753344007741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19903314123025835562671827 29854971184538753344007741)
    ·
      refine ⟨11195614194202032504002903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29854971184538753344007741 11195614194202032504002903)
      ·
        refine ⟨16793421291303048756004355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11195614194202032504002903 16793421291303048756004355)
        ·
          refine ⟨25190131936954573134006533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16793421291303048756004355 25190131936954573134006533)
          ·
            refine ⟨4723149738178982462626225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25190131936954573134006533 4723149738178982462626225)
            ·
              refine ⟨3542362303634236846969669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4723149738178982462626225 3542362303634236846969669)
              ·
                refine ⟨664192931931419408806813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3542362303634236846969669 664192931931419408806813)
                ·
                  refine ⟨249072349474282278302555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664192931931419408806813 249072349474282278302555)
                  ·
                    rfl

theorem cell21_1091400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_1091400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091400 prefixEnd_1091400 := by exact prefixLift 1091400
  have htrace : WordTrace (prefixWord ++ tailWord_1091400) baseStart_1091400 baseEnd_1091400 := by
    simpa [prefixWord, tailWord_1091400, baseEnd_1091400] using wordTrace_append hprefix tailTrace_1091400
  have hstable : (prefixWord ++ tailWord_1091400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091400).length < 2 ^ (prefixWord ++ tailWord_1091400).sum := by decide
  have hdescent : baseEnd_1091400 < baseStart_1091400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091459 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 5]
def baseStart_1091459 : Nat := 118140960795 + 1091459 * 2 ^ 59
def prefixEnd_1091459 : Nat := 4983230072969 + 3 ^ 40 * 1091459 * 2
def baseEnd_1091459 : Nat := 249085814078111286819101

theorem tailTrace_1091459 : CollatzResearch.WordTrace tailWord_1091459 prefixEnd_1091459 249085814078111286819101 := by
  unfold tailWord_1091459
  simp only [CollatzResearch.WordTrace]
  refine ⟨39808780152837924201741431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26539186768558616134494287 39808780152837924201741431)
  ·
    refine ⟨59713170229256886302612147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39808780152837924201741431 59713170229256886302612147)
    ·
      refine ⟨89569755343885329453918221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59713170229256886302612147 89569755343885329453918221)
      ·
        refine ⟨33588658253956998545219333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89569755343885329453918221 33588658253956998545219333)
        ·
          refine ⟨6297873422616937227228625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33588658253956998545219333 6297873422616937227228625)
          ·
            refine ⟨4723405066962702920421469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6297873422616937227228625 4723405066962702920421469)
            ·
              refine ⟨1771276900111013595158051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4723405066962702920421469 1771276900111013595158051)
              ·
                refine ⟨2656915350166520392737077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771276900111013595158051 2656915350166520392737077)
                ·
                  refine ⟨249085814078111286819101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656915350166520392737077 249085814078111286819101)
                  ·
                    rfl

theorem cell21_1091459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_1091459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091459 prefixEnd_1091459 := by exact prefixLift 1091459
  have htrace : WordTrace (prefixWord ++ tailWord_1091459) baseStart_1091459 baseEnd_1091459 := by
    simpa [prefixWord, tailWord_1091459, baseEnd_1091459] using wordTrace_append hprefix tailTrace_1091459
  have hstable : (prefixWord ++ tailWord_1091459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091459).length < 2 ^ (prefixWord ++ tailWord_1091459).sum := by decide
  have hdescent : baseEnd_1091459 < baseStart_1091459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1091538 : List Nat := [3, 2, 2, 3, 2, 1, 3, 5]
def baseStart_1091538 : Nat := 118140960795 + 1091538 * 2 ^ 59
def prefixEnd_1091538 : Nat := 4983230072969 + 3 ^ 40 * 1091538 * 2
def baseEnd_1091538 : Nat := 83034614318141568334091

theorem tailTrace_1091538 : CollatzResearch.WordTrace tailWord_1091538 prefixEnd_1091538 83034614318141568334091 := by
  unfold tailWord_1091538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952915379887930173466817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26541107679701147129244845 9952915379887930173466817)
  ·
    refine ⟨7464686534915947630100113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9952915379887930173466817 7464686534915947630100113)
    ·
      refine ⟨5598514901186960722575085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7464686534915947630100113 5598514901186960722575085)
      ·
        refine ⟨2099443087945110270965657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5598514901186960722575085 2099443087945110270965657)
        ·
          refine ⟨1574582315958832703224243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2099443087945110270965657 1574582315958832703224243)
          ·
            refine ⟨2361873473938249054836365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574582315958832703224243 2361873473938249054836365)
            ·
              refine ⟨885702552726843395563637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2361873473938249054836365 885702552726843395563637)
              ·
                refine ⟨83034614318141568334091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 885702552726843395563637 83034614318141568334091)
                ·
                  rfl

theorem cell21_1091538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_1091538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1091538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1091538 prefixEnd_1091538 := by exact prefixLift 1091538
  have htrace : WordTrace (prefixWord ++ tailWord_1091538) baseStart_1091538 baseEnd_1091538 := by
    simpa [prefixWord, tailWord_1091538, baseEnd_1091538] using wordTrace_append hprefix tailTrace_1091538
  have hstable : (prefixWord ++ tailWord_1091538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1091538).length < 2 ^ (prefixWord ++ tailWord_1091538).sum := by decide
  have hdescent : baseEnd_1091538 < baseStart_1091538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1091538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
