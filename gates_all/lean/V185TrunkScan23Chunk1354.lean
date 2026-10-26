import V185TrunkScan23Chunk1353

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8018387 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6]
def baseStart_8018387 : Nat := 118140960795 + 8018387 * 2 ^ 59
def prefixEnd_8018387 : Nat := 4983230072969 + 3 ^ 40 * 8018387 * 2
def baseEnd_8018387 : Nat := 4117286604763024757686615

theorem tailTrace_8018387 : CollatzResearch.WordTrace tailWord_8018387 prefixEnd_8018387 4117286604763024757686615 := by
  unfold tailWord_8018387
  simp only [CollatzResearch.WordTrace]
  refine ⟨292454600001760805318701415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194969733334507203545800943 292454600001760805318701415)
  ·
    refine ⟨438681900002641207978052123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292454600001760805318701415 438681900002641207978052123)
    ·
      refine ⟨658022850003961811967078185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438681900002641207978052123 658022850003961811967078185)
      ·
        refine ⟨493517137502971358975308639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658022850003961811967078185 493517137502971358975308639)
        ·
          refine ⟨740275706254457038462962959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493517137502971358975308639 740275706254457038462962959)
          ·
            refine ⟨1110413559381685557694444439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740275706254457038462962959 1110413559381685557694444439)
            ·
              refine ⟨1665620339072528336541666659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110413559381685557694444439 1665620339072528336541666659)
              ·
                refine ⟨2498430508608792504812499989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665620339072528336541666659 2498430508608792504812499989)
                ·
                  refine ⟨117113930091037148663085937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2498430508608792504812499989 117113930091037148663085937)
                  ·
                    refine ⟨87835447568277861497314453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117113930091037148663085937 87835447568277861497314453)
                    ·
                      refine ⟨4117286604763024757686615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87835447568277861497314453 4117286604763024757686615)
                      ·
                        rfl

theorem cell23_8018387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_8018387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018387 prefixEnd_8018387 := by exact prefixLift 8018387
  have htrace : WordTrace (prefixWord ++ tailWord_8018387) baseStart_8018387 baseEnd_8018387 := by
    simpa [prefixWord, tailWord_8018387, baseEnd_8018387] using wordTrace_append hprefix tailTrace_8018387
  have hstable : (prefixWord ++ tailWord_8018387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018387).length < 2 ^ (prefixWord ++ tailWord_8018387).sum := by decide
  have hdescent : baseEnd_8018387 < baseStart_8018387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018405 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_8018405 : Nat := 118140960795 + 8018405 * 2 ^ 59
def prefixEnd_8018405 : Nat := 4983230072969 + 3 ^ 40 * 8018405 * 2
def baseEnd_8018405 : Nat := 1372431949138268562420511

theorem tailTrace_8018405 : CollatzResearch.WordTrace tailWord_8018405 prefixEnd_8018405 1372431949138268562420511 := by
  unfold tailWord_8018405
  simp only [CollatzResearch.WordTrace]
  refine ⟨292455256515695594392856669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194970171010463729595237779 292455256515695594392856669)
  ·
    refine ⟨109670721193385847897321251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292455256515695594392856669 109670721193385847897321251)
    ·
      refine ⟨164506081790078771845981877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109670721193385847897321251 164506081790078771845981877)
      ·
        refine ⟨15422445167819884860560801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164506081790078771845981877 15422445167819884860560801)
        ·
          refine ⟨11566833875864913645420601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15422445167819884860560801 11566833875864913645420601)
          ·
            refine ⟨8675125406898685234065451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11566833875864913645420601 8675125406898685234065451)
            ·
              refine ⟨13012688110348027851098177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675125406898685234065451 13012688110348027851098177)
              ·
                refine ⟨9759516082761020888323633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13012688110348027851098177 9759516082761020888323633)
                ·
                  refine ⟨7319637062070765666242725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9759516082761020888323633 7319637062070765666242725)
                  ·
                    refine ⟨1372431949138268562420511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7319637062070765666242725 1372431949138268562420511)
                    ·
                      rfl

theorem cell23_8018405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_8018405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018405 prefixEnd_8018405 := by exact prefixLift 8018405
  have htrace : WordTrace (prefixWord ++ tailWord_8018405) baseStart_8018405 baseEnd_8018405 := by
    simpa [prefixWord, tailWord_8018405, baseEnd_8018405] using wordTrace_append hprefix tailTrace_8018405
  have hstable : (prefixWord ++ tailWord_8018405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018405).length < 2 ^ (prefixWord ++ tailWord_8018405).sum := by decide
  have hdescent : baseEnd_8018405 < baseStart_8018405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018411 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 3]
def baseStart_8018411 : Nat := 118140960795 + 8018411 * 2 ^ 59
def prefixEnd_8018411 : Nat := 4983230072969 + 3 ^ 40 * 8018411 * 2
def baseEnd_8018411 : Nat := 4117298928298732663786505

theorem tailTrace_8018411 : CollatzResearch.WordTrace tailWord_8018411 prefixEnd_8018411 4117298928298732663786505 := by
  unfold tailWord_8018411
  simp only [CollatzResearch.WordTrace]
  refine ⟨292455475353673857417575087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194970316902449238278383391 292455475353673857417575087)
  ·
    refine ⟨438683213030510786126362631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292455475353673857417575087 438683213030510786126362631)
    ·
      refine ⟨658024819545766179189543947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438683213030510786126362631 658024819545766179189543947)
      ·
        refine ⟨987037229318649268784315921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658024819545766179189543947 987037229318649268784315921)
        ·
          refine ⟨740277921988986951588236941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987037229318649268784315921 740277921988986951588236941)
          ·
            refine ⟨277604220745870106845588853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740277921988986951588236941 277604220745870106845588853)
            ·
              refine ⟨26025395694925322516773955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277604220745870106845588853 26025395694925322516773955)
              ·
                refine ⟨39038093542387983775160933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26025395694925322516773955 39038093542387983775160933)
                ·
                  refine ⟨7319642539197746957842675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39038093542387983775160933 7319642539197746957842675)
                  ·
                    refine ⟨10979463808796620436764013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7319642539197746957842675 10979463808796620436764013)
                    ·
                      refine ⟨4117298928298732663786505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10979463808796620436764013 4117298928298732663786505)
                      ·
                        rfl

theorem cell23_8018411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 3].length) (baseStart_8018411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018411 prefixEnd_8018411 := by exact prefixLift 8018411
  have htrace : WordTrace (prefixWord ++ tailWord_8018411) baseStart_8018411 baseEnd_8018411 := by
    simpa [prefixWord, tailWord_8018411, baseEnd_8018411] using wordTrace_append hprefix tailTrace_8018411
  have hstable : (prefixWord ++ tailWord_8018411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018411).length < 2 ^ (prefixWord ++ tailWord_8018411).sum := by decide
  have hdescent : baseEnd_8018411 < baseStart_8018411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018451 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 3, 4, 2]
def baseStart_8018451 : Nat := 118140960795 + 8018451 * 2 ^ 59
def prefixEnd_8018451 : Nat := 4983230072969 + 3 ^ 40 * 8018451 * 2
def baseEnd_8018451 : Nat := 4117319467524912507286321

theorem tailTrace_8018451 : CollatzResearch.WordTrace tailWord_8018451 prefixEnd_8018451 4117319467524912507286321 := by
  unfold tailWord_8018451
  simp only [CollatzResearch.WordTrace]
  refine ⟨292456934273528944249031207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194971289515685962832687471 292456934273528944249031207)
  ·
    refine ⟨438685401410293416373546811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292456934273528944249031207 438685401410293416373546811)
    ·
      refine ⟨658028102115440124560320217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438685401410293416373546811 658028102115440124560320217)
      ·
        refine ⟨493521076586580093420240163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658028102115440124560320217 493521076586580093420240163)
        ·
          refine ⟨740281614879870140130360245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493521076586580093420240163 740281614879870140130360245)
          ·
            refine ⟨69401401394987825637221273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 740281614879870140130360245 69401401394987825637221273)
            ·
              refine ⟨52051051046240869227915955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69401401394987825637221273 52051051046240869227915955)
              ·
                refine ⟨78076576569361303841873933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52051051046240869227915955 78076576569361303841873933)
                ·
                  refine ⟨29278716213510488940702725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78076576569361303841873933 29278716213510488940702725)
                  ·
                    refine ⟨5489759290033216676381761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29278716213510488940702725 5489759290033216676381761)
                    ·
                      refine ⟨4117319467524912507286321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489759290033216676381761 4117319467524912507286321)
                      ·
                        rfl

theorem cell23_8018451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4, 2].length) (baseStart_8018451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018451 prefixEnd_8018451 := by exact prefixLift 8018451
  have htrace : WordTrace (prefixWord ++ tailWord_8018451) baseStart_8018451 baseEnd_8018451 := by
    simpa [prefixWord, tailWord_8018451, baseEnd_8018451] using wordTrace_append hprefix tailTrace_8018451
  have hstable : (prefixWord ++ tailWord_8018451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018451).length < 2 ^ (prefixWord ++ tailWord_8018451).sum := by decide
  have hdescent : baseEnd_8018451 < baseStart_8018451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018485 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_8018485 : Nat := 118140960795 + 8018485 * 2 ^ 59
def prefixEnd_8018485 : Nat := 4983230072969 + 3 ^ 40 * 8018485 * 2
def baseEnd_8018485 : Nat := 4117336925867165374261165

theorem tailTrace_8018485 : CollatzResearch.WordTrace tailWord_8018485 prefixEnd_8018485 4117336925867165374261165 := by
  unfold tailWord_8018485
  simp only [CollatzResearch.WordTrace]
  refine ⟨292458174355405768055768909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194972116236937178703845939 292458174355405768055768909)
  ·
    refine ⟨109671815383277163020913341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292458174355405768055768909 109671815383277163020913341)
    ·
      refine ⟨41126930768728936132842503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109671815383277163020913341 41126930768728936132842503)
      ·
        refine ⟨61690396153093404199263755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41126930768728936132842503 61690396153093404199263755)
        ·
          refine ⟨92535594229640106298895633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61690396153093404199263755 92535594229640106298895633)
          ·
            refine ⟨69401695672230079724171725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92535594229640106298895633 69401695672230079724171725)
            ·
              refine ⟨26025635877086279896564397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69401695672230079724171725 26025635877086279896564397)
              ·
                refine ⟨9759613453907354961211649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26025635877086279896564397 9759613453907354961211649)
                ·
                  refine ⟨7319710090430516220908737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9759613453907354961211649 7319710090430516220908737)
                  ·
                    refine ⟨5489782567822887165681553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7319710090430516220908737 5489782567822887165681553)
                    ·
                      refine ⟨4117336925867165374261165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489782567822887165681553 4117336925867165374261165)
                      ·
                        rfl

theorem cell23_8018485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_8018485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018485 prefixEnd_8018485 := by exact prefixLift 8018485
  have htrace : WordTrace (prefixWord ++ tailWord_8018485) baseStart_8018485 baseEnd_8018485 := by
    simpa [prefixWord, tailWord_8018485, baseEnd_8018485] using wordTrace_append hprefix tailTrace_8018485
  have hstable : (prefixWord ++ tailWord_8018485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018485).length < 2 ^ (prefixWord ++ tailWord_8018485).sum := by decide
  have hdescent : baseEnd_8018485 < baseStart_8018485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018502 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_8018502 : Nat := 118140960795 + 8018502 * 2 ^ 59
def prefixEnd_8018502 : Nat := 4983230072969 + 3 ^ 40 * 8018502 * 2
def baseEnd_8018502 : Nat := 4117345655038291807748587

theorem tailTrace_8018502 : CollatzResearch.WordTrace tailWord_8018502 prefixEnd_8018502 4117345655038291807748587 := by
  unfold tailWord_8018502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9139337324885755623723055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194972529597562786639425173 9139337324885755623723055)
  ·
    refine ⟨13709005987328633435584583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9139337324885755623723055 13709005987328633435584583)
    ·
      refine ⟨20563508980992950153376875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13709005987328633435584583 20563508980992950153376875)
      ·
        refine ⟨30845263471489425230065313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20563508980992950153376875 30845263471489425230065313)
        ·
          refine ⟨23133947603617068922548985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30845263471489425230065313 23133947603617068922548985)
          ·
            refine ⟨17350460702712801691911739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23133947603617068922548985 17350460702712801691911739)
            ·
              refine ⟨26025691054069202537867609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17350460702712801691911739 26025691054069202537867609)
              ·
                refine ⟨19519268290551901903400707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26025691054069202537867609 19519268290551901903400707)
                ·
                  refine ⟨29278902435827852855101061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19519268290551901903400707 29278902435827852855101061)
                  ·
                    refine ⟨5489794206717722410331449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29278902435827852855101061 5489794206717722410331449)
                    ·
                      refine ⟨4117345655038291807748587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489794206717722410331449 4117345655038291807748587)
                      ·
                        rfl

theorem cell23_8018502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_8018502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018502 prefixEnd_8018502 := by exact prefixLift 8018502
  have htrace : WordTrace (prefixWord ++ tailWord_8018502) baseStart_8018502 baseEnd_8018502 := by
    simpa [prefixWord, tailWord_8018502, baseEnd_8018502] using wordTrace_append hprefix tailTrace_8018502
  have hstable : (prefixWord ++ tailWord_8018502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018502).length < 2 ^ (prefixWord ++ tailWord_8018502).sum := by decide
  have hdescent : baseEnd_8018502 < baseStart_8018502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018504 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 1, 7]
def baseStart_8018504 : Nat := 118140960795 + 8018504 * 2 ^ 59
def prefixEnd_8018504 : Nat := 4983230072969 + 3 ^ 40 * 8018504 * 2
def baseEnd_8018504 : Nat := 1372448893999866933307859

theorem tailTrace_8018504 : CollatzResearch.WordTrace tailWord_8018504 prefixEnd_8018504 1372448893999866933307859 := by
  unfold tailWord_8018504
  simp only [CollatzResearch.WordTrace]
  refine ⟨146229433671168467150355283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194972578228224622867140377 146229433671168467150355283)
  ·
    refine ⟨219344150506752700725532925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146229433671168467150355283 219344150506752700725532925)
    ·
      refine ⟨82254056440032262772074847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219344150506752700725532925 82254056440032262772074847)
      ·
        refine ⟨123381084660048394158112271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82254056440032262772074847 123381084660048394158112271)
        ·
          refine ⟨185071626990072591237168407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123381084660048394158112271 185071626990072591237168407)
          ·
            refine ⟨277607440485108886855752611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185071626990072591237168407 277607440485108886855752611)
            ·
              refine ⟨416411160727663330283628917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277607440485108886855752611 416411160727663330283628917)
              ·
                refine ⟨39038546318218437214090211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416411160727663330283628917 39038546318218437214090211)
                ·
                  refine ⟨58557819477327655821135317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39038546318218437214090211 58557819477327655821135317)
                  ·
                    refine ⟨1372448893999866933307859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58557819477327655821135317 1372448893999866933307859)
                    ·
                      rfl

theorem cell23_8018504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_8018504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018504 prefixEnd_8018504 := by exact prefixLift 8018504
  have htrace : WordTrace (prefixWord ++ tailWord_8018504) baseStart_8018504 baseEnd_8018504 := by
    simpa [prefixWord, tailWord_8018504, baseEnd_8018504] using wordTrace_append hprefix tailTrace_8018504
  have hstable : (prefixWord ++ tailWord_8018504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018504).length < 2 ^ (prefixWord ++ tailWord_8018504).sum := by decide
  have hdescent : baseEnd_8018504 < baseStart_8018504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018551 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 5, 4]
def baseStart_8018551 : Nat := 118140960795 + 8018551 * 2 ^ 59
def prefixEnd_8018551 : Nat := 4983230072969 + 3 ^ 40 * 8018551 * 2
def baseEnd_8018551 : Nat := 1372456938530120705345287

theorem tailTrace_8018551 : CollatzResearch.WordTrace tailWord_8018551 prefixEnd_8018551 1372456938530120705345287 := by
  unfold tailWord_8018551
  simp only [CollatzResearch.WordTrace]
  refine ⟨292460581573166661327671507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194973721048777774218447671 292460581573166661327671507)
  ·
    refine ⟨438690872359749991991507261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292460581573166661327671507 438690872359749991991507261)
    ·
      refine ⟨164509077134906246996815223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438690872359749991991507261 164509077134906246996815223)
      ·
        refine ⟨246763615702359370495222835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164509077134906246996815223 246763615702359370495222835)
        ·
          refine ⟨370145423553539055742834253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246763615702359370495222835 370145423553539055742834253)
          ·
            refine ⟨138804533832577145903562845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370145423553539055742834253 138804533832577145903562845)
            ·
              refine ⟨52051700187216429713836067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138804533832577145903562845 52051700187216429713836067)
              ·
                refine ⟨78077550280824644570754101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52051700187216429713836067 78077550280824644570754101)
                ·
                  refine ⟨7319770338827310428508197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78077550280824644570754101 7319770338827310428508197)
                  ·
                    refine ⟨1372456938530120705345287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7319770338827310428508197 1372456938530120705345287)
                    ·
                      rfl

theorem cell23_8018551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_8018551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018551 prefixEnd_8018551 := by exact prefixLift 8018551
  have htrace : WordTrace (prefixWord ++ tailWord_8018551) baseStart_8018551 baseEnd_8018551 := by
    simpa [prefixWord, tailWord_8018551, baseEnd_8018551] using wordTrace_append hprefix tailTrace_8018551
  have hstable : (prefixWord ++ tailWord_8018551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018551).length < 2 ^ (prefixWord ++ tailWord_8018551).sum := by decide
  have hdescent : baseEnd_8018551 < baseStart_8018551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018618 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2]
def baseStart_8018618 : Nat := 118140960795 + 8018618 * 2 ^ 59
def prefixEnd_8018618 : Nat := 4983230072969 + 3 ^ 40 * 8018618 * 2
def baseEnd_8018618 : Nat := 4117405218794213353898053

theorem tailTrace_8018618 : CollatzResearch.WordTrace tailWord_8018618 prefixEnd_8018618 4117405218794213353898053 := by
  unfold tailWord_8018618
  simp only [CollatzResearch.WordTrace]
  refine ⟨73115756315980982942590127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194975350175949287846907005 73115756315980982942590127)
  ·
    refine ⟨109673634473971474413885191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73115756315980982942590127 109673634473971474413885191)
    ·
      refine ⟨164510451710957211620827787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109673634473971474413885191 164510451710957211620827787)
      ·
        refine ⟨246765677566435817431241681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164510451710957211620827787 246765677566435817431241681)
        ·
          refine ⟨185074258174826863073431261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246765677566435817431241681 185074258174826863073431261)
          ·
            refine ⟨69402846815560073652536723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185074258174826863073431261 69402846815560073652536723)
            ·
              refine ⟨104104270223340110478805085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69402846815560073652536723 104104270223340110478805085)
              ·
                refine ⟨39039101333752541429551907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104104270223340110478805085 39039101333752541429551907)
                ·
                  refine ⟨58558652000628812144327861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39039101333752541429551907 58558652000628812144327861)
                  ·
                    refine ⟨5489873625058951138530737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58558652000628812144327861 5489873625058951138530737)
                    ·
                      refine ⟨4117405218794213353898053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489873625058951138530737 4117405218794213353898053)
                      ·
                        rfl

theorem cell23_8018618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_8018618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018618 prefixEnd_8018618 := by exact prefixLift 8018618
  have htrace : WordTrace (prefixWord ++ tailWord_8018618) baseStart_8018618 baseEnd_8018618 := by
    simpa [prefixWord, tailWord_8018618, baseEnd_8018618] using wordTrace_append hprefix tailTrace_8018618
  have hstable : (prefixWord ++ tailWord_8018618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018618).length < 2 ^ (prefixWord ++ tailWord_8018618).sum := by decide
  have hdescent : baseEnd_8018618 < baseStart_8018618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018665 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 3, 2, 2]
def baseStart_8018665 : Nat := 118140960795 + 8018665 * 2 ^ 59
def prefixEnd_8018665 : Nat := 4983230072969 + 3 ^ 40 * 8018665 * 2
def baseEnd_8018665 : Nat := 4117429352384974670010337

theorem tailTrace_8018665 : CollatzResearch.WordTrace tailWord_8018665 prefixEnd_8018665 4117429352384974670010337 := by
  unfold tailWord_8018665
  simp only [CollatzResearch.WordTrace]
  refine ⟨292464739494753658797321449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194976492996502439198214299 292464739494753658797321449)
  ·
    refine ⟨219348554621065244097991087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292464739494753658797321449 219348554621065244097991087)
    ·
      refine ⟨329022831931597866146986631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219348554621065244097991087 329022831931597866146986631)
      ·
        refine ⟨493534247897396799220479947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329022831931597866146986631 493534247897396799220479947)
        ·
          refine ⟨740301371846095198830719921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493534247897396799220479947 740301371846095198830719921)
          ·
            refine ⟨555226028884571399123039941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740301371846095198830719921 555226028884571399123039941)
            ·
              refine ⟨104104880415857137335569989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 555226028884571399123039941 104104880415857137335569989)
              ·
                refine ⟨19519665077973213250419373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104104880415857137335569989 19519665077973213250419373)
                ·
                  refine ⟨7319874404239954968907265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19519665077973213250419373 7319874404239954968907265)
                  ·
                    refine ⟨5489905803179966226680449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7319874404239954968907265 5489905803179966226680449)
                    ·
                      refine ⟨4117429352384974670010337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489905803179966226680449 4117429352384974670010337)
                      ·
                        rfl

theorem cell23_8018665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 2, 2].length) (baseStart_8018665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018665 prefixEnd_8018665 := by exact prefixLift 8018665
  have htrace : WordTrace (prefixWord ++ tailWord_8018665) baseStart_8018665 baseEnd_8018665 := by
    simpa [prefixWord, tailWord_8018665, baseEnd_8018665] using wordTrace_append hprefix tailTrace_8018665
  have hstable : (prefixWord ++ tailWord_8018665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018665).length < 2 ^ (prefixWord ++ tailWord_8018665).sum := by decide
  have hdescent : baseEnd_8018665 < baseStart_8018665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018671 : List Nat := [1, 1, 2, 1, 5, 2, 2, 9]
def baseStart_8018671 : Nat := 118140960795 + 8018671 * 2 ^ 59
def prefixEnd_8018671 : Nat := 4983230072969 + 3 ^ 40 * 8018671 * 2
def baseEnd_8018671 : Nat := 152497497528477838760567

theorem tailTrace_8018671 : CollatzResearch.WordTrace tailWord_8018671 prefixEnd_8018671 152497497528477838760567 := by
  unfold tailWord_8018671
  simp only [CollatzResearch.WordTrace]
  refine ⟨292464958332731921822039867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194976638888487947881359911 292464958332731921822039867)
  ·
    refine ⟨438697437499097882733059801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292464958332731921822039867 438697437499097882733059801)
    ·
      refine ⟨329023078124323412049794851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438697437499097882733059801 329023078124323412049794851)
      ·
        refine ⟨493534617186485118074692277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329023078124323412049794851 493534617186485118074692277)
        ·
          refine ⟨46268870361232979819502401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 493534617186485118074692277 46268870361232979819502401)
          ·
            refine ⟨34701652770924734864626801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46268870361232979819502401 34701652770924734864626801)
            ·
              refine ⟨26026239578193551148470101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34701652770924734864626801 26026239578193551148470101)
              ·
                refine ⟨152497497528477838760567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26026239578193551148470101 152497497528477838760567)
                ·
                  rfl

theorem cell23_8018671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 9].length) (baseStart_8018671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018671 prefixEnd_8018671 := by exact prefixLift 8018671
  have htrace : WordTrace (prefixWord ++ tailWord_8018671) baseStart_8018671 baseEnd_8018671 := by
    simpa [prefixWord, tailWord_8018671, baseEnd_8018671] using wordTrace_append hprefix tailTrace_8018671
  have hstable : (prefixWord ++ tailWord_8018671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018671).length < 2 ^ (prefixWord ++ tailWord_8018671).sum := by decide
  have hdescent : baseEnd_8018671 < baseStart_8018671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018698 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_8018698 : Nat := 118140960795 + 8018698 * 2 ^ 59
def prefixEnd_8018698 : Nat := 4983230072969 + 3 ^ 40 * 8018698 * 2
def baseEnd_8018698 : Nat := 4117446297246573040897685

theorem tailTrace_8018698 : CollatzResearch.WordTrace tailWord_8018698 prefixEnd_8018698 4117446297246573040897685 := by
  unfold tailWord_8018698
  simp only [CollatzResearch.WordTrace]
  refine ⟨73116485775908526358318187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194977295402422736955515165 73116485775908526358318187)
  ·
    refine ⟨109674728663862789537477281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73116485775908526358318187 109674728663862789537477281)
    ·
      refine ⟨82256046497897092153107961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109674728663862789537477281 82256046497897092153107961)
      ·
        refine ⟨61692034873422819114830971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82256046497897092153107961 61692034873422819114830971)
        ·
          refine ⟨92538052310134228672246457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61692034873422819114830971 92538052310134228672246457)
          ·
            refine ⟨69403539232600671504184843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92538052310134228672246457 69403539232600671504184843)
            ·
              refine ⟨104105308848901007256277265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69403539232600671504184843 104105308848901007256277265)
              ·
                refine ⟨78078981636675755442207949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104105308848901007256277265 78078981636675755442207949)
                ·
                  refine ⟨29279618113753408290827981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78078981636675755442207949 29279618113753408290827981)
                  ·
                    refine ⟨10979856792657528109060493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29279618113753408290827981 10979856792657528109060493)
                    ·
                      refine ⟨4117446297246573040897685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10979856792657528109060493 4117446297246573040897685)
                      ·
                        rfl

theorem cell23_8018698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_8018698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018698 prefixEnd_8018698 := by exact prefixLift 8018698
  have htrace : WordTrace (prefixWord ++ tailWord_8018698) baseStart_8018698 baseEnd_8018698 := by
    simpa [prefixWord, tailWord_8018698, baseEnd_8018698] using wordTrace_append hprefix tailTrace_8018698
  have hstable : (prefixWord ++ tailWord_8018698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018698).length < 2 ^ (prefixWord ++ tailWord_8018698).sum := by decide
  have hdescent : baseEnd_8018698 < baseStart_8018698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018725 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 3, 3, 2]
def baseStart_8018725 : Nat := 118140960795 + 8018725 * 2 ^ 59
def prefixEnd_8018725 : Nat := 4983230072969 + 3 ^ 40 * 8018725 * 2
def baseEnd_8018725 : Nat := 4117460161224244435260061

theorem tailTrace_8018725 : CollatzResearch.WordTrace tailWord_8018725 prefixEnd_8018725 4117460161224244435260061 := by
  unfold tailWord_8018725
  simp only [CollatzResearch.WordTrace]
  refine ⟨292466927874536289044505629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194977951916357526029670419 292466927874536289044505629)
  ·
    refine ⟨109675097952951108391689611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292466927874536289044505629 109675097952951108391689611)
    ·
      refine ⟨164512646929426662587534417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109675097952951108391689611 164512646929426662587534417)
      ·
        refine ⟨123384485197069996940650813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164512646929426662587534417 123384485197069996940650813)
        ·
          refine ⟨46269181948901248852744055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123384485197069996940650813 46269181948901248852744055)
          ·
            refine ⟨69403772923351873279116083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46269181948901248852744055 69403772923351873279116083)
            ·
              refine ⟨104105659385027809918674125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69403772923351873279116083 104105659385027809918674125)
              ·
                refine ⟨39039622269385428719502797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104105659385027809918674125 39039622269385428719502797)
                ·
                  refine ⟨14639858351019535769813549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39039622269385428719502797 14639858351019535769813549)
                  ·
                    refine ⟨5489946881632325913680081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14639858351019535769813549 5489946881632325913680081)
                    ·
                      refine ⟨4117460161224244435260061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489946881632325913680081 4117460161224244435260061)
                      ·
                        rfl

theorem cell23_8018725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_8018725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018725 prefixEnd_8018725 := by exact prefixLift 8018725
  have htrace : WordTrace (prefixWord ++ tailWord_8018725) baseStart_8018725 baseEnd_8018725 := by
    simpa [prefixWord, tailWord_8018725, baseEnd_8018725] using wordTrace_append hprefix tailTrace_8018725
  have hstable : (prefixWord ++ tailWord_8018725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018725).length < 2 ^ (prefixWord ++ tailWord_8018725).sum := by decide
  have hdescent : baseEnd_8018725 < baseStart_8018725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018728 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_8018728 : Nat := 118140960795 + 8018728 * 2 ^ 59
def prefixEnd_8018728 : Nat := 4983230072969 + 3 ^ 40 * 8018728 * 2
def baseEnd_8018728 : Nat := 4117461701666207923522547

theorem tailTrace_8018728 : CollatzResearch.WordTrace tailWord_8018728 prefixEnd_8018728 4117461701666207923522547 := by
  unfold tailWord_8018728
  simp only [CollatzResearch.WordTrace]
  refine ⟨146233518646762710278432419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194978024862350280371243225 146233518646762710278432419)
  ·
    refine ⟨219350277970144065417648629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146233518646762710278432419 219350277970144065417648629)
    ·
      refine ⟨20564088559701006132904559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219350277970144065417648629 20564088559701006132904559)
      ·
        refine ⟨30846132839551509199356839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20564088559701006132904559 30846132839551509199356839)
        ·
          refine ⟨46269199259327263799035259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30846132839551509199356839 46269199259327263799035259)
          ·
            refine ⟨69403798888990895698552889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46269199259327263799035259 69403798888990895698552889)
            ·
              refine ⟨52052849166743171773914667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69403798888990895698552889 52052849166743171773914667)
              ·
                refine ⟨78079273750114757660872001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52052849166743171773914667 78079273750114757660872001)
                ·
                  refine ⟨58559455312586068245654001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78079273750114757660872001 58559455312586068245654001)
                  ·
                    refine ⟨43919591484439551184240501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58559455312586068245654001 43919591484439551184240501)
                    ·
                      refine ⟨4117461701666207923522547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43919591484439551184240501 4117461701666207923522547)
                      ·
                        rfl

theorem cell23_8018728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_8018728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018728 prefixEnd_8018728 := by exact prefixLift 8018728
  have htrace : WordTrace (prefixWord ++ tailWord_8018728) baseStart_8018728 baseEnd_8018728 := by
    simpa [prefixWord, tailWord_8018728, baseEnd_8018728] using wordTrace_append hprefix tailTrace_8018728
  have hstable : (prefixWord ++ tailWord_8018728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018728).length < 2 ^ (prefixWord ++ tailWord_8018728).sum := by decide
  have hdescent : baseEnd_8018728 < baseStart_8018728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018731 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 4, 6]
def baseStart_8018731 : Nat := 118140960795 + 8018731 * 2 ^ 59
def prefixEnd_8018731 : Nat := 4983230072969 + 3 ^ 40 * 8018731 * 2
def baseEnd_8018731 : Nat := 1372487747369390470595011

theorem tailTrace_8018731 : CollatzResearch.WordTrace tailWord_8018731 prefixEnd_8018731 1372487747369390470595011 := by
  unfold tailWord_8018731
  simp only [CollatzResearch.WordTrace]
  refine ⟨292467146712514552069224047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194978097808343034712816031 292467146712514552069224047)
  ·
    refine ⟨438700720068771828103836071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292467146712514552069224047 438700720068771828103836071)
    ·
      refine ⟨658051080103157742155754107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438700720068771828103836071 658051080103157742155754107)
      ·
        refine ⟨987076620154736613233631161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658051080103157742155754107 987076620154736613233631161)
        ·
          refine ⟨740307465116052459925223371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987076620154736613233631161 740307465116052459925223371)
          ·
            refine ⟨1110461197674078689887835057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740307465116052459925223371 1110461197674078689887835057)
            ·
              refine ⟨832845898255559017415876293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110461197674078689887835057 832845898255559017415876293)
              ·
                refine ⟨156158605922917315765476805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832845898255559017415876293 156158605922917315765476805)
                ·
                  refine ⟨29279738610546996706026901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156158605922917315765476805 29279738610546996706026901)
                  ·
                    refine ⟨1372487747369390470595011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29279738610546996706026901 1372487747369390470595011)
                    ·
                      rfl

theorem cell23_8018731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 6].length) (baseStart_8018731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018731 prefixEnd_8018731 := by exact prefixLift 8018731
  have htrace : WordTrace (prefixWord ++ tailWord_8018731) baseStart_8018731 baseEnd_8018731 := by
    simpa [prefixWord, tailWord_8018731, baseEnd_8018731] using wordTrace_append hprefix tailTrace_8018731
  have hstable : (prefixWord ++ tailWord_8018731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018731).length < 2 ^ (prefixWord ++ tailWord_8018731).sum := by decide
  have hdescent : baseEnd_8018731 < baseStart_8018731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018733 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_8018733 : Nat := 118140960795 + 8018733 * 2 ^ 59
def prefixEnd_8018733 : Nat := 4983230072969 + 3 ^ 40 * 8018733 * 2
def baseEnd_8018733 : Nat := 4117464269069480403960025

theorem tailTrace_8018733 : CollatzResearch.WordTrace tailWord_8018733 prefixEnd_8018733 4117464269069480403960025 := by
  unfold tailWord_8018733
  simp only [CollatzResearch.WordTrace]
  refine ⟨292467219658507306410796853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194978146439004870940531235 292467219658507306410796853)
  ·
    refine ⟨27418801842985059976012205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292467219658507306410796853 27418801842985059976012205)
    ·
      refine ⟨10282050691119397491004577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27418801842985059976012205 10282050691119397491004577)
      ·
        refine ⟨7711538018339548118253433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10282050691119397491004577 7711538018339548118253433)
        ·
          refine ⟨5783653513754661088690075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7711538018339548118253433 5783653513754661088690075)
          ·
            refine ⟨8675480270631991633035113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783653513754661088690075 8675480270631991633035113)
            ·
              refine ⟨6506610202973993724776335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8675480270631991633035113 6506610202973993724776335)
              ·
                refine ⟨9759915304460990587164503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506610202973993724776335 9759915304460990587164503)
                ·
                  refine ⟨14639872956691485880746755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9759915304460990587164503 14639872956691485880746755)
                  ·
                    refine ⟨21959809435037228821120133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14639872956691485880746755 21959809435037228821120133)
                    ·
                      refine ⟨4117464269069480403960025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21959809435037228821120133 4117464269069480403960025)
                      ·
                        rfl

theorem cell23_8018733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_8018733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018733 prefixEnd_8018733 := by exact prefixLift 8018733
  have htrace : WordTrace (prefixWord ++ tailWord_8018733) baseStart_8018733 baseEnd_8018733 := by
    simpa [prefixWord, tailWord_8018733, baseEnd_8018733] using wordTrace_append hprefix tailTrace_8018733
  have hstable : (prefixWord ++ tailWord_8018733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018733).length < 2 ^ (prefixWord ++ tailWord_8018733).sum := by decide
  have hdescent : baseEnd_8018733 < baseStart_8018733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018768 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_8018768 : Nat := 118140960795 + 8018768 * 2 ^ 59
def prefixEnd_8018768 : Nat := 4983230072969 + 3 ^ 40 * 8018768 * 2
def baseEnd_8018768 : Nat := 4117482240892387767022363

theorem tailTrace_8018768 : CollatzResearch.WordTrace tailWord_8018768 prefixEnd_8018768 4117482240892387767022363 := by
  unfold tailWord_8018768
  simp only [CollatzResearch.WordTrace]
  refine ⟨146234248106690253694160479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194978997475587004925547305 146234248106690253694160479)
  ·
    refine ⟨219351372160035380541240719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146234248106690253694160479 219351372160035380541240719)
    ·
      refine ⟨329027058240053070811861079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219351372160035380541240719 329027058240053070811861079)
      ·
        refine ⟨493540587360079606217791619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329027058240053070811861079 493540587360079606217791619)
        ·
          refine ⟨740310881040119409326687429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493540587360079606217791619 740310881040119409326687429)
          ·
            refine ⟨138808290195022389248753893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 740310881040119409326687429 138808290195022389248753893)
            ·
              refine ⟨26026554411566697984141355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138808290195022389248753893 26026554411566697984141355)
              ·
                refine ⟨39039831617350046976212033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26026554411566697984141355 39039831617350046976212033)
                ·
                  refine ⟨29279873713012535232159025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39039831617350046976212033 29279873713012535232159025)
                  ·
                    refine ⟨21959905284759401424119269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29279873713012535232159025 21959905284759401424119269)
                    ·
                      refine ⟨4117482240892387767022363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21959905284759401424119269 4117482240892387767022363)
                      ·
                        rfl

theorem cell23_8018768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_8018768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018768 prefixEnd_8018768 := by exact prefixLift 8018768
  have htrace : WordTrace (prefixWord ++ tailWord_8018768) baseStart_8018768 baseEnd_8018768 := by
    simpa [prefixWord, tailWord_8018768, baseEnd_8018768] using wordTrace_append hprefix tailTrace_8018768
  have hstable : (prefixWord ++ tailWord_8018768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018768).length < 2 ^ (prefixWord ++ tailWord_8018768).sum := by decide
  have hdescent : baseEnd_8018768 < baseStart_8018768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018771 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9]
def baseStart_8018771 : Nat := 118140960795 + 8018771 * 2 ^ 59
def prefixEnd_8018771 : Nat := 4983230072969 + 3 ^ 40 * 8018771 * 2
def baseEnd_8018771 : Nat := 4117483781334351255284849

theorem tailTrace_8018771 : CollatzResearch.WordTrace tailWord_8018771 prefixEnd_8018771 4117483781334351255284849 := by
  unfold tailWord_8018771
  simp only [CollatzResearch.WordTrace]
  refine ⟨292468605632369638900680167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194979070421579759267120111 292468605632369638900680167)
  ·
    refine ⟨438702908448554458351020251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292468605632369638900680167 438702908448554458351020251)
    ·
      refine ⟨658054362672831687526530377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438702908448554458351020251 658054362672831687526530377)
      ·
        refine ⟨493540772004623765644897783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658054362672831687526530377 493540772004623765644897783)
        ·
          refine ⟨740311158006935648467346675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493540772004623765644897783 740311158006935648467346675)
          ·
            refine ⟨1110466737010403472701020013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740311158006935648467346675 1110466737010403472701020013)
            ·
              refine ⟨416425026378901302262882505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1110466737010403472701020013 416425026378901302262882505)
              ·
                refine ⟨312318769784175976697161879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416425026378901302262882505 312318769784175976697161879)
                ·
                  refine ⟨468478154676263965045742819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312318769784175976697161879 468478154676263965045742819)
                  ·
                    refine ⟨702717232014395947568614229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 468478154676263965045742819 702717232014395947568614229)
                    ·
                      refine ⟨4117483781334351255284849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 702717232014395947568614229 4117483781334351255284849)
                      ·
                        rfl

theorem cell23_8018771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_8018771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018771 prefixEnd_8018771 := by exact prefixLift 8018771
  have htrace : WordTrace (prefixWord ++ tailWord_8018771) baseStart_8018771 baseEnd_8018771 := by
    simpa [prefixWord, tailWord_8018771, baseEnd_8018771] using wordTrace_append hprefix tailTrace_8018771
  have hstable : (prefixWord ++ tailWord_8018771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018771).length < 2 ^ (prefixWord ++ tailWord_8018771).sum := by decide
  have hdescent : baseEnd_8018771 < baseStart_8018771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018778 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 7]
def baseStart_8018778 : Nat := 118140960795 + 8018778 * 2 ^ 59
def prefixEnd_8018778 : Nat := 4983230072969 + 3 ^ 40 * 8018778 * 2
def baseEnd_8018778 : Nat := 457498597299881414210813

theorem tailTrace_8018778 : CollatzResearch.WordTrace tailWord_8018778 prefixEnd_8018778 457498597299881414210813 := by
  unfold tailWord_8018778
  simp only [CollatzResearch.WordTrace]
  refine ⟨73117215235836069774046247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194979240628896186064123325 73117215235836069774046247)
  ·
    refine ⟨109675822853754104661069371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73117215235836069774046247 109675822853754104661069371)
    ·
      refine ⟨164513734280631156991604057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109675822853754104661069371 164513734280631156991604057)
      ·
        refine ⟨123385300710473367743703043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164513734280631156991604057 123385300710473367743703043)
        ·
          refine ⟨185077951065710051615554565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123385300710473367743703043 185077951065710051615554565)
          ·
            refine ⟨34702115824820634677916481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185077951065710051615554565 34702115824820634677916481)
            ·
              refine ⟨26026586868615476008437361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34702115824820634677916481 26026586868615476008437361)
              ·
                refine ⟨19519940151461607006328021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26026586868615476008437361 19519940151461607006328021)
                ·
                  refine ⟨457498597299881414210813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19519940151461607006328021 457498597299881414210813)
                  ·
                    rfl

theorem cell23_8018778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_8018778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018778 prefixEnd_8018778 := by exact prefixLift 8018778
  have htrace : WordTrace (prefixWord ++ tailWord_8018778) baseStart_8018778 baseEnd_8018778 := by
    simpa [prefixWord, tailWord_8018778, baseEnd_8018778] using wordTrace_append hprefix tailTrace_8018778
  have hstable : (prefixWord ++ tailWord_8018778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018778).length < 2 ^ (prefixWord ++ tailWord_8018778).sum := by decide
  have hdescent : baseEnd_8018778 < baseStart_8018778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018795 : List Nat := [1, 1, 1, 1, 2, 2, 7, 3, 5]
def baseStart_8018795 : Nat := 118140960795 + 8018795 * 2 ^ 59
def prefixEnd_8018795 : Nat := 4983230072969 + 3 ^ 40 * 8018795 * 2
def baseEnd_8018795 : Nat := 457499567207784351264971

theorem tailTrace_8018795 : CollatzResearch.WordTrace tailWord_8018795 prefixEnd_8018795 457499567207784351264971 := by
  unfold tailWord_8018795
  simp only [CollatzResearch.WordTrace]
  refine ⟨292469480984282690999553839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194979653989521793999702559 292469480984282690999553839)
  ·
    refine ⟨438704221476424036499330759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292469480984282690999553839 438704221476424036499330759)
    ·
      refine ⟨658056332214636054748996139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438704221476424036499330759 658056332214636054748996139)
      ·
        refine ⟨987084498321954082123494209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658056332214636054748996139 987084498321954082123494209)
        ·
          refine ⟨740313373741465561592620657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987084498321954082123494209 740313373741465561592620657)
          ·
            refine ⟨555235030306099171194465493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740313373741465561592620657 555235030306099171194465493)
            ·
              refine ⟨13013321022799199324870285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 555235030306099171194465493 13013321022799199324870285)
              ·
                refine ⟨4879995383549699746826357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13013321022799199324870285 4879995383549699746826357)
                ·
                  refine ⟨457499567207784351264971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4879995383549699746826357 457499567207784351264971)
                  ·
                    rfl

theorem cell23_8018795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 5].length) (baseStart_8018795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018795 prefixEnd_8018795 := by exact prefixLift 8018795
  have htrace : WordTrace (prefixWord ++ tailWord_8018795) baseStart_8018795 baseEnd_8018795 := by
    simpa [prefixWord, tailWord_8018795, baseEnd_8018795] using wordTrace_append hprefix tailTrace_8018795
  have hstable : (prefixWord ++ tailWord_8018795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018795).length < 2 ^ (prefixWord ++ tailWord_8018795).sum := by decide
  have hdescent : baseEnd_8018795 < baseStart_8018795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018828 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_8018828 : Nat := 118140960795 + 8018828 * 2 ^ 59
def prefixEnd_8018828 : Nat := 4983230072969 + 3 ^ 40 * 8018828 * 2
def baseEnd_8018828 : Nat := 4117513049731657532272087

theorem tailTrace_8018828 : CollatzResearch.WordTrace tailWord_8018828 prefixEnd_8018828 4117513049731657532272087 := by
  unfold tailWord_8018828
  simp only [CollatzResearch.WordTrace]
  refine ⟨146235342296581568817752569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194980456395442091757003425 146235342296581568817752569)
  ·
    refine ⟨109676506722436176613314427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146235342296581568817752569 109676506722436176613314427)
    ·
      refine ⟨164514760083654264919971641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109676506722436176613314427 164514760083654264919971641)
      ·
        refine ⟨123386070062740698689978731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164514760083654264919971641 123386070062740698689978731)
        ·
          refine ⟨185079105094111048034968097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123386070062740698689978731 185079105094111048034968097)
          ·
            refine ⟨138809328820583286026226073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185079105094111048034968097 138809328820583286026226073)
            ·
              refine ⟨104106996615437464519669555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138809328820583286026226073 104106996615437464519669555)
              ·
                refine ⟨156160494923156196779504333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104106996615437464519669555 156160494923156196779504333)
                ·
                  refine ⟨58560185596183573792314125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156160494923156196779504333 58560185596183573792314125)
                  ·
                    refine ⟨21960069598568840172117797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58560185596183573792314125 21960069598568840172117797)
                    ·
                      refine ⟨4117513049731657532272087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21960069598568840172117797 4117513049731657532272087)
                      ·
                        rfl

theorem cell23_8018828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_8018828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018828 prefixEnd_8018828 := by exact prefixLift 8018828
  have htrace : WordTrace (prefixWord ++ tailWord_8018828) baseStart_8018828 baseEnd_8018828 := by
    simpa [prefixWord, tailWord_8018828, baseEnd_8018828] using wordTrace_append hprefix tailTrace_8018828
  have hstable : (prefixWord ++ tailWord_8018828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018828).length < 2 ^ (prefixWord ++ tailWord_8018828).sum := by decide
  have hdescent : baseEnd_8018828 < baseStart_8018828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018842 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_8018842 : Nat := 118140960795 + 8018842 * 2 ^ 59
def prefixEnd_8018842 : Nat := 4983230072969 + 3 ^ 40 * 8018842 * 2
def baseEnd_8018842 : Nat := 1372506746153606825832341

theorem tailTrace_8018842 : CollatzResearch.WordTrace tailWord_8018842 prefixEnd_8018842 1372506746153606825832341 := by
  unfold tailWord_8018842
  simp only [CollatzResearch.WordTrace]
  refine ⟨73117798803778104506628695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194980796810074945351009853 73117798803778104506628695)
  ·
    refine ⟨109676698205667156759943043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73117798803778104506628695 109676698205667156759943043)
    ·
      refine ⟨164515047308500735139914565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109676698205667156759943043 164515047308500735139914565)
      ·
        refine ⟨30846571370343887838733981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164515047308500735139914565 30846571370343887838733981)
        ·
          refine ⟨11567464263878957939525243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30846571370343887838733981 11567464263878957939525243)
          ·
            refine ⟨17351196395818436909287865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11567464263878957939525243 17351196395818436909287865)
            ·
              refine ⟨13013397296863827681965899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17351196395818436909287865 13013397296863827681965899)
              ·
                refine ⟨19520095945295741522948849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13013397296863827681965899 19520095945295741522948849)
                ·
                  refine ⟨14640071958971806142211637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19520095945295741522948849 14640071958971806142211637)
                  ·
                    refine ⟨1372506746153606825832341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14640071958971806142211637 1372506746153606825832341)
                    ·
                      rfl

theorem cell23_8018842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_8018842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018842 prefixEnd_8018842 := by exact prefixLift 8018842
  have htrace : WordTrace (prefixWord ++ tailWord_8018842) baseStart_8018842 baseEnd_8018842 := by
    simpa [prefixWord, tailWord_8018842, baseEnd_8018842] using wordTrace_append hprefix tailTrace_8018842
  have hstable : (prefixWord ++ tailWord_8018842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018842).length < 2 ^ (prefixWord ++ tailWord_8018842).sum := by decide
  have hdescent : baseEnd_8018842 < baseStart_8018842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018893 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_8018893 : Nat := 118140960795 + 8018893 * 2 ^ 59
def prefixEnd_8018893 : Nat := 4983230072969 + 3 ^ 40 * 8018893 * 2
def baseEnd_8018893 : Nat := 1372515475324733259319763

theorem tailTrace_8018893 : CollatzResearch.WordTrace tailWord_8018893 prefixEnd_8018893 1372515475324733259319763 := by
  unfold tailWord_8018893
  simp only [CollatzResearch.WordTrace]
  refine ⟨292473055337927653736621333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194982036891951769157747555 292473055337927653736621333)
  ·
    refine ⟨13709674468965358768904125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292473055337927653736621333 13709674468965358768904125)
    ·
      refine ⟨5141127925862009538339047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13709674468965358768904125 5141127925862009538339047)
      ·
        refine ⟨7711691888793014307508571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141127925862009538339047 7711691888793014307508571)
        ·
          refine ⟨11567537833189521461262857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7711691888793014307508571 11567537833189521461262857)
          ·
            refine ⟨8675653374892141095947143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11567537833189521461262857 8675653374892141095947143)
            ·
              refine ⟨13013480062338211643920715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675653374892141095947143 13013480062338211643920715)
              ·
                refine ⟨19520220093507317465881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13013480062338211643920715 19520220093507317465881073)
                ·
                  refine ⟨14640165070130488099410805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19520220093507317465881073 14640165070130488099410805)
                  ·
                    refine ⟨1372515475324733259319763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14640165070130488099410805 1372515475324733259319763)
                    ·
                      rfl

theorem cell23_8018893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_8018893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018893 prefixEnd_8018893 := by exact prefixLift 8018893
  have htrace : WordTrace (prefixWord ++ tailWord_8018893) baseStart_8018893 baseEnd_8018893 := by
    simpa [prefixWord, tailWord_8018893, baseEnd_8018893] using wordTrace_append hprefix tailTrace_8018893
  have hstable : (prefixWord ++ tailWord_8018893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018893).length < 2 ^ (prefixWord ++ tailWord_8018893).sum := by decide
  have hdescent : baseEnd_8018893 < baseStart_8018893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018929 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_8018929 : Nat := 118140960795 + 8018929 * 2 ^ 59
def prefixEnd_8018929 : Nat := 4983230072969 + 3 ^ 40 * 8018929 * 2
def baseEnd_8018929 : Nat := 4117564911277761637109123

theorem tailTrace_8018929 : CollatzResearch.WordTrace tailWord_8018929 prefixEnd_8018929 4117564911277761637109123 := by
  unfold tailWord_8018929
  simp only [CollatzResearch.WordTrace]
  refine ⟨292474368365797231884931841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194982912243864821256621227 292474368365797231884931841)
  ·
    refine ⟨219355776274347923913698881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292474368365797231884931841 219355776274347923913698881)
    ·
      refine ⟨164516832205760942935274161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219355776274347923913698881 164516832205760942935274161)
      ·
        refine ⟨123387624154320707201455621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164516832205760942935274161 123387624154320707201455621)
        ·
          refine ⟨23135179528935132600272929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123387624154320707201455621 23135179528935132600272929)
          ·
            refine ⟨17351384646701349450204697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23135179528935132600272929 17351384646701349450204697)
            ·
              refine ⟨13013538485026012087653523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17351384646701349450204697 13013538485026012087653523)
              ·
                refine ⟨19520307727539018131480285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13013538485026012087653523 19520307727539018131480285)
                ·
                  refine ⟨7320115397827131799305107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19520307727539018131480285 7320115397827131799305107)
                  ·
                    refine ⟨10980173096740697698957661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7320115397827131799305107 10980173096740697698957661)
                    ·
                      refine ⟨4117564911277761637109123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10980173096740697698957661 4117564911277761637109123)
                      ·
                        rfl

theorem cell23_8018929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_8018929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018929 prefixEnd_8018929 := by exact prefixLift 8018929
  have htrace : WordTrace (prefixWord ++ tailWord_8018929) baseStart_8018929 baseEnd_8018929 := by
    simpa [prefixWord, tailWord_8018929, baseEnd_8018929] using wordTrace_append hprefix tailTrace_8018929
  have hstable : (prefixWord ++ tailWord_8018929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018929).length < 2 ^ (prefixWord ++ tailWord_8018929).sum := by decide
  have hdescent : baseEnd_8018929 < baseStart_8018929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018952 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_8018952 : Nat := 118140960795 + 8018952 * 2 ^ 59
def prefixEnd_8018952 : Nat := 4983230072969 + 3 ^ 40 * 8018952 * 2
def baseEnd_8018952 : Nat := 4117576721332815047121517

theorem tailTrace_8018952 : CollatzResearch.WordTrace tailWord_8018952 prefixEnd_8018952 4117576721332815047121517 := by
  unfold tailWord_8018952
  simp only [CollatzResearch.WordTrace]
  refine ⟨146237603622356953406509555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194983471496475937875346073 146237603622356953406509555)
  ·
    refine ⟨219356405433535430109764333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146237603622356953406509555 219356405433535430109764333)
    ·
      refine ⟨82258652037575786291161625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219356405433535430109764333 82258652037575786291161625)
      ·
        refine ⟨61693989028181839718371219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82258652037575786291161625 61693989028181839718371219)
        ·
          refine ⟨92540983542272759577556829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61693989028181839718371219 92540983542272759577556829)
          ·
            refine ⟨34702868828352284841583811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92540983542272759577556829 34702868828352284841583811)
            ·
              refine ⟨52054303242528427262375717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34702868828352284841583811 52054303242528427262375717)
              ·
                refine ⟨9760181857974080111695447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52054303242528427262375717 9760181857974080111695447)
                ·
                  refine ⟨14640272786961120167543171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760181857974080111695447 14640272786961120167543171)
                  ·
                    refine ⟨21960409180441680251314757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14640272786961120167543171 21960409180441680251314757)
                    ·
                      refine ⟨4117576721332815047121517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21960409180441680251314757 4117576721332815047121517)
                      ·
                        rfl

theorem cell23_8018952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_8018952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018952 prefixEnd_8018952 := by exact prefixLift 8018952
  have htrace : WordTrace (prefixWord ++ tailWord_8018952) baseStart_8018952 baseEnd_8018952 := by
    simpa [prefixWord, tailWord_8018952, baseEnd_8018952] using wordTrace_append hprefix tailTrace_8018952
  have hstable : (prefixWord ++ tailWord_8018952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018952).length < 2 ^ (prefixWord ++ tailWord_8018952).sum := by decide
  have hdescent : baseEnd_8018952 < baseStart_8018952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018975 : List Nat := [1, 1, 2, 4, 1, 5, 9]
def baseStart_8018975 : Nat := 118140960795 + 8018975 * 2 ^ 59
def prefixEnd_8018975 : Nat := 4983230072969 + 3 ^ 40 * 8018975 * 2
def baseEnd_8018975 : Nat := 50834426313430474779431

theorem tailTrace_8018975 : CollatzResearch.WordTrace tailWord_8018975 prefixEnd_8018975 50834426313430474779431 := by
  unfold tailWord_8018975
  simp only [CollatzResearch.WordTrace]
  refine ⟨292476046123630581741106379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194984030749087054494070919 292476046123630581741106379)
  ·
    refine ⟨438714069185445872611659569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292476046123630581741106379 438714069185445872611659569)
    ·
      refine ⟨329035551889084404458744677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438714069185445872611659569 329035551889084404458744677)
      ·
        refine ⟨61694165979203325836014627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329035551889084404458744677 61694165979203325836014627)
        ·
          refine ⟨92541248968804988754021941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61694165979203325836014627 92541248968804988754021941)
          ·
            refine ⟨8675742090825467695689557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92541248968804988754021941 8675742090825467695689557)
            ·
              refine ⟨50834426313430474779431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8675742090825467695689557 50834426313430474779431)
              ·
                rfl

theorem cell23_8018975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 9].length) (baseStart_8018975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018975 prefixEnd_8018975 := by exact prefixLift 8018975
  have htrace : WordTrace (prefixWord ++ tailWord_8018975) baseStart_8018975 baseEnd_8018975 := by
    simpa [prefixWord, tailWord_8018975, baseEnd_8018975] using wordTrace_append hprefix tailTrace_8018975
  have hstable : (prefixWord ++ tailWord_8018975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018975).length < 2 ^ (prefixWord ++ tailWord_8018975).sum := by decide
  have hdescent : baseEnd_8018975 < baseStart_8018975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018996 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_8018996 : Nat := 118140960795 + 8018996 * 2 ^ 59
def prefixEnd_8018996 : Nat := 4983230072969 + 3 ^ 40 * 8018996 * 2
def baseEnd_8018996 : Nat := 1372533104827204291657105

theorem tailTrace_8018996 : CollatzResearch.WordTrace tailWord_8018996 prefixEnd_8018996 1372533104827204291657105 := by
  unfold tailWord_8018996
  simp only [CollatzResearch.WordTrace]
  refine ⟨146238406028277251163810421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194984541371036334885080561 146238406028277251163810421)
  ·
    refine ⟨13709850565150992296607227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146238406028277251163810421 13709850565150992296607227)
    ·
      refine ⟨20564775847726488444910841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13709850565150992296607227 20564775847726488444910841)
      ·
        refine ⟨15423581885794866333683131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20564775847726488444910841 15423581885794866333683131)
        ·
          refine ⟨23135372828692299500524697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423581885794866333683131 23135372828692299500524697)
          ·
            refine ⟨17351529621519224625393523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23135372828692299500524697 17351529621519224625393523)
            ·
              refine ⟨26027294432278836938090285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17351529621519224625393523 26027294432278836938090285)
              ·
                refine ⟨9760235412104563851783857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26027294432278836938090285 9760235412104563851783857)
                ·
                  refine ⟨7320176559078422888837893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9760235412104563851783857 7320176559078422888837893)
                  ·
                    refine ⟨1372533104827204291657105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320176559078422888837893 1372533104827204291657105)
                    ·
                      rfl

theorem cell23_8018996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_8018996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018996 prefixEnd_8018996 := by exact prefixLift 8018996
  have htrace : WordTrace (prefixWord ++ tailWord_8018996) baseStart_8018996 baseEnd_8018996 := by
    simpa [prefixWord, tailWord_8018996, baseEnd_8018996] using wordTrace_append hprefix tailTrace_8018996
  have hstable : (prefixWord ++ tailWord_8018996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018996).length < 2 ^ (prefixWord ++ tailWord_8018996).sum := by decide
  have hdescent : baseEnd_8018996 < baseStart_8018996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019006 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_8019006 : Nat := 118140960795 + 8019006 * 2 ^ 59
def prefixEnd_8019006 : Nat := 4983230072969 + 3 ^ 40 * 8019006 * 2
def baseEnd_8019006 : Nat := 4117604449288157835846269

theorem tailTrace_8019006 : CollatzResearch.WordTrace tailWord_8019006 prefixEnd_8019006 4117604449288157835846269 := by
  unfold tailWord_8019006
  simp only [CollatzResearch.WordTrace]
  refine ⟨36559647098314784254435609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194984784524345516023656581 36559647098314784254435609)
  ·
    refine ⟨27419735323736088190826707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36559647098314784254435609 27419735323736088190826707)
    ·
      refine ⟨41129602985604132286240061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27419735323736088190826707 41129602985604132286240061)
      ·
        refine ⟨15423601119601549607340023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41129602985604132286240061 15423601119601549607340023)
        ·
          refine ⟨23135401679402324411010035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423601119601549607340023 23135401679402324411010035)
          ·
            refine ⟨34703102519103486616515053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23135401679402324411010035 34703102519103486616515053)
            ·
              refine ⟨13013663444663807481193145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34703102519103486616515053 13013663444663807481193145)
              ·
                refine ⟨9760247583497855610894859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13013663444663807481193145 9760247583497855610894859)
                ·
                  refine ⟨14640371375246783416342289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760247583497855610894859 14640371375246783416342289)
                  ·
                    refine ⟨10980278531435087562256717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14640371375246783416342289 10980278531435087562256717)
                    ·
                      refine ⟨4117604449288157835846269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10980278531435087562256717 4117604449288157835846269)
                      ·
                        rfl

theorem cell23_8019006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_8019006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019006 prefixEnd_8019006 := by exact prefixLift 8019006
  have htrace : WordTrace (prefixWord ++ tailWord_8019006) baseStart_8019006 baseEnd_8019006 := by
    simpa [prefixWord, tailWord_8019006, baseEnd_8019006] using wordTrace_append hprefix tailTrace_8019006
  have hstable : (prefixWord ++ tailWord_8019006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019006).length < 2 ^ (prefixWord ++ tailWord_8019006).sum := by decide
  have hdescent : baseEnd_8019006 < baseStart_8019006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019036 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_8019036 : Nat := 118140960795 + 8019036 * 2 ^ 59
def prefixEnd_8019036 : Nat := 4983230072969 + 3 ^ 40 * 8019036 * 2
def baseEnd_8019036 : Nat := 4117619853707792718471131

theorem tailTrace_8019036 : CollatzResearch.WordTrace tailWord_8019036 prefixEnd_8019036 4117619853707792718471131 := by
  unfold tailWord_8019036
  simp only [CollatzResearch.WordTrace]
  refine ⟨146239135488204794579538481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194985513984273059439384641 146239135488204794579538481)
  ·
    refine ⟨109679351616153595934653861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146239135488204794579538481 109679351616153595934653861)
    ·
      refine ⟨20564878428028799237747599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109679351616153595934653861 20564878428028799237747599)
      ·
        refine ⟨30847317642043198856621399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20564878428028799237747599 30847317642043198856621399)
        ·
          refine ⟨46270976463064798284932099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30847317642043198856621399 46270976463064798284932099)
          ·
            refine ⟨69406464694597197427398149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46270976463064798284932099 69406464694597197427398149)
            ·
              refine ⟨13013712130236974517637153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69406464694597197427398149 13013712130236974517637153)
              ·
                refine ⟨9760284097677730888227865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13013712130236974517637153 9760284097677730888227865)
                ·
                  refine ⟨7320213073258298166170899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9760284097677730888227865 7320213073258298166170899)
                  ·
                    refine ⟨10980319609887447249256349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7320213073258298166170899 10980319609887447249256349)
                    ·
                      refine ⟨4117619853707792718471131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10980319609887447249256349 4117619853707792718471131)
                      ·
                        rfl

theorem cell23_8019036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_8019036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019036 prefixEnd_8019036 := by exact prefixLift 8019036
  have htrace : WordTrace (prefixWord ++ tailWord_8019036) baseStart_8019036 baseEnd_8019036 := by
    simpa [prefixWord, tailWord_8019036, baseEnd_8019036] using wordTrace_append hprefix tailTrace_8019036
  have hstable : (prefixWord ++ tailWord_8019036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019036).length < 2 ^ (prefixWord ++ tailWord_8019036).sum := by decide
  have hdescent : baseEnd_8019036 < baseStart_8019036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019080 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_8019080 : Nat := 118140960795 + 8019080 * 2 ^ 59
def prefixEnd_8019080 : Nat := 4983230072969 + 3 ^ 40 * 8019080 * 2
def baseEnd_8019080 : Nat := 4117642446856590546320929

theorem tailTrace_8019080 : CollatzResearch.WordTrace tailWord_8019080 prefixEnd_8019080 4117642446856590546320929 := by
  unfold tailWord_8019080
  simp only [CollatzResearch.WordTrace]
  refine ⟨146239937894125092336839347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194986583858833456449119129 146239937894125092336839347)
  ·
    refine ⟨219359906841187638505259021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146239937894125092336839347 219359906841187638505259021)
    ·
      refine ⟨82259965065445364439472133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219359906841187638505259021 82259965065445364439472133)
      ·
        refine ⟨15423743449771005832401025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82259965065445364439472133 15423743449771005832401025)
        ·
          refine ⟨11567807587328254374300769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15423743449771005832401025 11567807587328254374300769)
          ·
            refine ⟨8675855690496190780725577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11567807587328254374300769 8675855690496190780725577)
            ·
              refine ⟨6506891767872143085544183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8675855690496190780725577 6506891767872143085544183)
              ·
                refine ⟨9760337651808214628316275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506891767872143085544183 9760337651808214628316275)
                ·
                  refine ⟨14640506477712321942474413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760337651808214628316275 14640506477712321942474413)
                  ·
                    refine ⟨5490189929142120728427905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14640506477712321942474413 5490189929142120728427905)
                    ·
                      refine ⟨4117642446856590546320929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5490189929142120728427905 4117642446856590546320929)
                      ·
                        rfl

theorem cell23_8019080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_8019080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019080 prefixEnd_8019080 := by exact prefixLift 8019080
  have htrace : WordTrace (prefixWord ++ tailWord_8019080) baseStart_8019080 baseEnd_8019080 := by
    simpa [prefixWord, tailWord_8019080, baseEnd_8019080] using wordTrace_append hprefix tailTrace_8019080
  have hstable : (prefixWord ++ tailWord_8019080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019080).length < 2 ^ (prefixWord ++ tailWord_8019080).sum := by decide
  have hdescent : baseEnd_8019080 < baseStart_8019080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019156 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8019156 : Nat := 118140960795 + 8019156 * 2 ^ 59
def prefixEnd_8019156 : Nat := 4983230072969 + 3 ^ 40 * 8019156 * 2
def baseEnd_8019156 : Nat := 4117681471386332248970579

theorem tailTrace_8019156 : CollatzResearch.WordTrace tailWord_8019156 prefixEnd_8019156 4117681471386332248970579 := by
  unfold tailWord_8019156
  simp only [CollatzResearch.WordTrace]
  refine ⟨146241323867987424826722661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194988431823983233102296881 146241323867987424826722661)
  ·
    refine ⟨27420248225247642155010499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146241323867987424826722661 27420248225247642155010499)
    ·
      refine ⟨41130372337871463232515749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27420248225247642155010499 41130372337871463232515749)
      ·
        refine ⟨7711944813350899356096703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41130372337871463232515749 7711944813350899356096703)
        ·
          refine ⟨11567917220026349034145055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7711944813350899356096703 11567917220026349034145055)
          ·
            refine ⟨17351875830039523551217583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11567917220026349034145055 17351875830039523551217583)
            ·
              refine ⟨26027813745059285326826375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17351875830039523551217583 26027813745059285326826375)
              ·
                refine ⟨39041720617588927990239563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26027813745059285326826375 39041720617588927990239563)
                ·
                  refine ⟨58562580926383391985359345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39041720617588927990239563 58562580926383391985359345)
                  ·
                    refine ⟨43921935694787543989019509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58562580926383391985359345 43921935694787543989019509)
                    ·
                      refine ⟨4117681471386332248970579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43921935694787543989019509 4117681471386332248970579)
                      ·
                        rfl

theorem cell23_8019156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8019156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019156 prefixEnd_8019156 := by exact prefixLift 8019156
  have htrace : WordTrace (prefixWord ++ tailWord_8019156) baseStart_8019156 baseEnd_8019156 := by
    simpa [prefixWord, tailWord_8019156, baseEnd_8019156] using wordTrace_append hprefix tailTrace_8019156
  have hstable : (prefixWord ++ tailWord_8019156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019156).length < 2 ^ (prefixWord ++ tailWord_8019156).sum := by decide
  have hdescent : baseEnd_8019156 < baseStart_8019156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019159 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 3, 4]
def baseStart_8019159 : Nat := 118140960795 + 8019159 * 2 ^ 59
def prefixEnd_8019159 : Nat := 4983230072969 + 3 ^ 40 * 8019159 * 2
def baseEnd_8019159 : Nat := 1372561003942765245744355

theorem tailTrace_8019159 : CollatzResearch.WordTrace tailWord_8019159 prefixEnd_8019159 1372561003942765245744355 := by
  unfold tailWord_8019159
  simp only [CollatzResearch.WordTrace]
  refine ⟨292482757154963981165804531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194988504769975987443869687 292482757154963981165804531)
  ·
    refine ⟨438724135732445971748706797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292482757154963981165804531 438724135732445971748706797)
    ·
      refine ⟨164521550899667239405765049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438724135732445971748706797 164521550899667239405765049)
      ·
        refine ⟨123391163174750429554323787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164521550899667239405765049 123391163174750429554323787)
        ·
          refine ⟨185086744762125644331485681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123391163174750429554323787 185086744762125644331485681)
          ·
            refine ⟨138815058571594233248614261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185086744762125644331485681 138815058571594233248614261)
            ·
              refine ⟨13013911741086959367057587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138815058571594233248614261 13013911741086959367057587)
              ·
                refine ⟨19520867611630439050586381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13013911741086959367057587 19520867611630439050586381)
                ·
                  refine ⟨7320325354361414643969893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19520867611630439050586381 7320325354361414643969893)
                  ·
                    refine ⟨1372561003942765245744355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320325354361414643969893 1372561003942765245744355)
                    ·
                      rfl

theorem cell23_8019159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_8019159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019159 prefixEnd_8019159 := by exact prefixLift 8019159
  have htrace : WordTrace (prefixWord ++ tailWord_8019159) baseStart_8019159 baseEnd_8019159 := by
    simpa [prefixWord, tailWord_8019159, baseEnd_8019159] using wordTrace_append hprefix tailTrace_8019159
  have hstable : (prefixWord ++ tailWord_8019159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019159).length < 2 ^ (prefixWord ++ tailWord_8019159).sum := by decide
  have hdescent : baseEnd_8019159 < baseStart_8019159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019249 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 1, 6]
def baseStart_8019249 : Nat := 118140960795 + 8019249 * 2 ^ 59
def prefixEnd_8019249 : Nat := 4983230072969 + 3 ^ 40 * 8019249 * 2
def baseEnd_8019249 : Nat := 1372576408362400128369217

theorem tailTrace_8019249 : CollatzResearch.WordTrace tailWord_8019249 prefixEnd_8019249 1372576408362400128369217 := by
  unfold tailWord_8019249
  simp only [CollatzResearch.WordTrace]
  refine ⟨292486039724637926536580801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194990693149758617691053867 292486039724637926536580801)
  ·
    refine ⟨219364529793478444902435601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292486039724637926536580801 219364529793478444902435601)
    ·
      refine ⟨164523397345108833676826701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219364529793478444902435601 164523397345108833676826701)
      ·
        refine ⟨61696274004415812628810013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164523397345108833676826701 61696274004415812628810013)
        ·
          refine ⟨23136102751655929735803755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61696274004415812628810013 23136102751655929735803755)
          ·
            refine ⟨34704154127483894603705633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23136102751655929735803755 34704154127483894603705633)
            ·
              refine ⟨26028115595612920952779225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34704154127483894603705633 26028115595612920952779225)
              ·
                refine ⟨19521086696709690714584419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26028115595612920952779225 19521086696709690714584419)
                ·
                  refine ⟨29281630045064536071876629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19521086696709690714584419 29281630045064536071876629)
                  ·
                    refine ⟨1372576408362400128369217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29281630045064536071876629 1372576408362400128369217)
                    ·
                      rfl

theorem cell23_8019249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_8019249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019249 prefixEnd_8019249 := by exact prefixLift 8019249
  have htrace : WordTrace (prefixWord ++ tailWord_8019249) baseStart_8019249 baseEnd_8019249 := by
    simpa [prefixWord, tailWord_8019249, baseEnd_8019249] using wordTrace_append hprefix tailTrace_8019249
  have hstable : (prefixWord ++ tailWord_8019249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019249).length < 2 ^ (prefixWord ++ tailWord_8019249).sum := by decide
  have hdescent : baseEnd_8019249 < baseStart_8019249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019250 : List Nat := [3, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_8019250 : Nat := 118140960795 + 8019250 * 2 ^ 59
def prefixEnd_8019250 : Nat := 4983230072969 + 3 ^ 40 * 8019250 * 2
def baseEnd_8019250 : Nat := 4117729738567854881195147

theorem tailTrace_8019250 : CollatzResearch.WordTrace tailWord_8019250 prefixEnd_8019250 4117729738567854881195147 := by
  unfold tailWord_8019250
  simp only [CollatzResearch.WordTrace]
  refine ⟨73121519049408575926841801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194990717465089535804911469 73121519049408575926841801)
  ·
    refine ⟨54841139287056431945131351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73121519049408575926841801 54841139287056431945131351)
    ·
      refine ⟨82261708930584647917697027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54841139287056431945131351 82261708930584647917697027)
      ·
        refine ⟨123392563395876971876545541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82261708930584647917697027 123392563395876971876545541)
        ·
          refine ⟨23136105636726932226852289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123392563395876971876545541 23136105636726932226852289)
          ·
            refine ⟨17352079227545199170139217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23136105636726932226852289 17352079227545199170139217)
            ·
              refine ⟨13014059420658899377604413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17352079227545199170139217 13014059420658899377604413)
              ·
                refine ⟨4880272282747087266601655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13014059420658899377604413 4880272282747087266601655)
                ·
                  refine ⟨7320408424120630899902483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880272282747087266601655 7320408424120630899902483)
                  ·
                    refine ⟨10980612636180946349853725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7320408424120630899902483 10980612636180946349853725)
                    ·
                      refine ⟨4117729738567854881195147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10980612636180946349853725 4117729738567854881195147)
                      ·
                        rfl

theorem cell23_8019250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_8019250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019250 prefixEnd_8019250 := by exact prefixLift 8019250
  have htrace : WordTrace (prefixWord ++ tailWord_8019250) baseStart_8019250 baseEnd_8019250 := by
    simpa [prefixWord, tailWord_8019250, baseEnd_8019250] using wordTrace_append hprefix tailTrace_8019250
  have hstable : (prefixWord ++ tailWord_8019250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019250).length < 2 ^ (prefixWord ++ tailWord_8019250).sum := by decide
  have hdescent : baseEnd_8019250 < baseStart_8019250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019253 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_8019253 : Nat := 118140960795 + 8019253 * 2 ^ 59
def prefixEnd_8019253 : Nat := 4983230072969 + 3 ^ 40 * 8019253 * 2
def baseEnd_8019253 : Nat := 1372577093003272789819211

theorem tailTrace_8019253 : CollatzResearch.WordTrace tailWord_8019253 prefixEnd_8019253 1372577093003272789819211 := by
  unfold tailWord_8019253
  simp only [CollatzResearch.WordTrace]
  refine ⟨292486185616623435219726413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194990790411082290146484275 292486185616623435219726413)
  ·
    refine ⟨109682319606233788207397405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292486185616623435219726413 109682319606233788207397405)
    ·
      refine ⟨41130869852337670577774027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109682319606233788207397405 41130869852337670577774027)
      ·
        refine ⟨61696304778506505866661041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41130869852337670577774027 61696304778506505866661041)
        ·
          refine ⟨46272228583879879399995781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61696304778506505866661041 46272228583879879399995781)
          ·
            refine ⟨8676042859477477387499209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46272228583879879399995781 8676042859477477387499209)
            ·
              refine ⟨6507032144608108040624407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8676042859477477387499209 6507032144608108040624407)
              ·
                refine ⟨9760548216912162060936611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507032144608108040624407 9760548216912162060936611)
                ·
                  refine ⟨14640822325368243091404917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760548216912162060936611 14640822325368243091404917)
                  ·
                    refine ⟨1372577093003272789819211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14640822325368243091404917 1372577093003272789819211)
                    ·
                      rfl

theorem cell23_8019253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_8019253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019253 prefixEnd_8019253 := by exact prefixLift 8019253
  have htrace : WordTrace (prefixWord ++ tailWord_8019253) baseStart_8019253 baseEnd_8019253 := by
    simpa [prefixWord, tailWord_8019253, baseEnd_8019253] using wordTrace_append hprefix tailTrace_8019253
  have hstable : (prefixWord ++ tailWord_8019253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019253).length < 2 ^ (prefixWord ++ tailWord_8019253).sum := by decide
  have hdescent : baseEnd_8019253 < baseStart_8019253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019256 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 7, 2, 2]
def baseStart_8019256 : Nat := 118140960795 + 8019256 * 2 ^ 59
def prefixEnd_8019256 : Nat := 4983230072969 + 3 ^ 40 * 8019256 * 2
def baseEnd_8019256 : Nat := 4117732819451781857720119

theorem tailTrace_8019256 : CollatzResearch.WordTrace tailWord_8019256 prefixEnd_8019256 4117732819451781857720119 := by
  unfold tailWord_8019256
  simp only [CollatzResearch.WordTrace]
  refine ⟨146243147517806283366042811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194990863357075044488057081 146243147517806283366042811)
  ·
    refine ⟨219364721276709425049064217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146243147517806283366042811 219364721276709425049064217)
    ·
      refine ⟨164523540957532068786798163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219364721276709425049064217 164523540957532068786798163)
      ·
        refine ⟨246785311436298103180197245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164523540957532068786798163 246785311436298103180197245)
        ·
          refine ⟨92544491788611788692573967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246785311436298103180197245 92544491788611788692573967)
          ·
            refine ⟨138816737682917683038860951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92544491788611788692573967 138816737682917683038860951)
            ·
              refine ⟨208225106524376524558291427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138816737682917683038860951 208225106524376524558291427)
              ·
                refine ⟨312337659786564786837437141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208225106524376524558291427 312337659786564786837437141)
                ·
                  refine ⟨7320413901247612191502433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 312337659786564786837437141 7320413901247612191502433)
                  ·
                    refine ⟨5490310425935709143626825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7320413901247612191502433 5490310425935709143626825)
                    ·
                      refine ⟨4117732819451781857720119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5490310425935709143626825 4117732819451781857720119)
                      ·
                        rfl

theorem cell23_8019256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_8019256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019256 prefixEnd_8019256 := by exact prefixLift 8019256
  have htrace : WordTrace (prefixWord ++ tailWord_8019256) baseStart_8019256 baseEnd_8019256 := by
    simpa [prefixWord, tailWord_8019256, baseEnd_8019256] using wordTrace_append hprefix tailTrace_8019256
  have hstable : (prefixWord ++ tailWord_8019256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019256).length < 2 ^ (prefixWord ++ tailWord_8019256).sum := by decide
  have hdescent : baseEnd_8019256 < baseStart_8019256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019272 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_8019272 : Nat := 118140960795 + 8019272 * 2 ^ 59
def prefixEnd_8019272 : Nat := 4983230072969 + 3 ^ 40 * 8019272 * 2
def baseEnd_8019272 : Nat := 4117741035142253795120045

theorem tailTrace_8019272 : CollatzResearch.WordTrace tailWord_8019272 prefixEnd_8019272 4117741035142253795120045 := by
  unfold tailWord_8019272
  simp only [CollatzResearch.WordTrace]
  refine ⟨146243439301777300732334035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194991252402369734309778713 146243439301777300732334035)
  ·
    refine ⟨219365158952665951098501053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146243439301777300732334035 219365158952665951098501053)
    ·
      refine ⟨82261934607249731661937895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219365158952665951098501053 82261934607249731661937895)
      ·
        refine ⟨123392901910874597492906843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82261934607249731661937895 123392901910874597492906843)
        ·
          refine ⟨185089352866311896239360265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123392901910874597492906843 185089352866311896239360265)
          ·
            refine ⟨138817014649733922179520199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185089352866311896239360265 138817014649733922179520199)
            ·
              refine ⟨208225521974600883269280299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138817014649733922179520199 208225521974600883269280299)
              ·
                refine ⟨312338282961901324903920449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208225521974600883269280299 312338282961901324903920449)
                ·
                  refine ⟨234253712221425993677940337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312338282961901324903920449 234253712221425993677940337)
                  ·
                    refine ⟨175690284166069495258455253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234253712221425993677940337 175690284166069495258455253)
                    ·
                      refine ⟨4117741035142253795120045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175690284166069495258455253 4117741035142253795120045)
                      ·
                        rfl

theorem cell23_8019272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_8019272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019272 prefixEnd_8019272 := by exact prefixLift 8019272
  have htrace : WordTrace (prefixWord ++ tailWord_8019272) baseStart_8019272 baseEnd_8019272 := by
    simpa [prefixWord, tailWord_8019272, baseEnd_8019272] using wordTrace_append hprefix tailTrace_8019272
  have hstable : (prefixWord ++ tailWord_8019272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019272).length < 2 ^ (prefixWord ++ tailWord_8019272).sum := by decide
  have hdescent : baseEnd_8019272 < baseStart_8019272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019296 : List Nat := [2, 1, 1, 3, 4, 3, 2, 7]
def baseStart_8019296 : Nat := 118140960795 + 8019296 * 2 ^ 59
def prefixEnd_8019296 : Nat := 4983230072969 + 3 ^ 40 * 8019296 * 2
def baseEnd_8019296 : Nat := 152509383654739322267405

theorem tailTrace_8019296 : CollatzResearch.WordTrace tailWord_8019296 prefixEnd_8019296 152509383654739322267405 := by
  unfold tailWord_8019296
  simp only [CollatzResearch.WordTrace]
  refine ⟨146243876977733826781770871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194991835970311769042361161 146243876977733826781770871)
  ·
    refine ⟨219365815466600740172656307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146243876977733826781770871 219365815466600740172656307)
    ·
      refine ⟨329048723199901110258984461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219365815466600740172656307 329048723199901110258984461)
      ·
        refine ⟨123393271199962916347119173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329048723199901110258984461 123393271199962916347119173)
        ·
          refine ⟨23136238349993046815084845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123393271199962916347119173 23136238349993046815084845)
          ·
            refine ⟨8676089381247392555656817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23136238349993046815084845 8676089381247392555656817)
            ·
              refine ⟨6507067035935544416742613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8676089381247392555656817 6507067035935544416742613)
              ·
                refine ⟨152509383654739322267405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6507067035935544416742613 152509383654739322267405)
                ·
                  rfl

theorem cell23_8019296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 7].length) (baseStart_8019296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019296 prefixEnd_8019296 := by exact prefixLift 8019296
  have htrace : WordTrace (prefixWord ++ tailWord_8019296) baseStart_8019296 baseEnd_8019296 := by
    simpa [prefixWord, tailWord_8019296, baseEnd_8019296] using wordTrace_append hprefix tailTrace_8019296
  have hstable : (prefixWord ++ tailWord_8019296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019296).length < 2 ^ (prefixWord ++ tailWord_8019296).sum := by decide
  have hdescent : baseEnd_8019296 < baseStart_8019296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019349 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_8019349 : Nat := 118140960795 + 8019349 * 2 ^ 59
def prefixEnd_8019349 : Nat := 4983230072969 + 3 ^ 40 * 8019349 * 2
def baseEnd_8019349 : Nat := 4117780573152649993857191

theorem tailTrace_8019349 : CollatzResearch.WordTrace tailWord_8019349 prefixEnd_8019349 4117780573152649993857191 := by
  unfold tailWord_8019349
  simp only [CollatzResearch.WordTrace]
  refine ⟨292489687024275643615221101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194993124682850429076814067 292489687024275643615221101)
  ·
    refine ⟨109683632634103366355707913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292489687024275643615221101 109683632634103366355707913)
    ·
      refine ⟨82262724475577524766780935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109683632634103366355707913 82262724475577524766780935)
      ·
        refine ⟨123394086713366287150171403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82262724475577524766780935 123394086713366287150171403)
        ·
          refine ⟨185091130070049430725257105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123394086713366287150171403 185091130070049430725257105)
          ·
            refine ⟨138818347552537073043942829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185091130070049430725257105 138818347552537073043942829)
            ·
              refine ⟨52056880332201402391478561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138818347552537073043942829 52056880332201402391478561)
              ·
                refine ⟨39042660249151051793608921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52056880332201402391478561 39042660249151051793608921)
                ·
                  refine ⟨29281995186863288845206691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39042660249151051793608921 29281995186863288845206691)
                  ·
                    refine ⟨43922992780294933267810037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29281995186863288845206691 43922992780294933267810037)
                    ·
                      refine ⟨4117780573152649993857191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43922992780294933267810037 4117780573152649993857191)
                      ·
                        rfl

theorem cell23_8019349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_8019349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019349 prefixEnd_8019349 := by exact prefixLift 8019349
  have htrace : WordTrace (prefixWord ++ tailWord_8019349) baseStart_8019349 baseEnd_8019349 := by
    simpa [prefixWord, tailWord_8019349, baseEnd_8019349] using wordTrace_append hprefix tailTrace_8019349
  have hstable : (prefixWord ++ tailWord_8019349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019349).length < 2 ^ (prefixWord ++ tailWord_8019349).sum := by decide
  have hdescent : baseEnd_8019349 < baseStart_8019349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019379 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 3]
def baseStart_8019379 : Nat := 118140960795 + 8019379 * 2 ^ 59
def prefixEnd_8019379 : Nat := 4983230072969 + 3 ^ 40 * 8019379 * 2
def baseEnd_8019379 : Nat := 4117795977572284876482053

theorem tailTrace_8019379 : CollatzResearch.WordTrace tailWord_8019379 prefixEnd_8019379 4117795977572284876482053 := by
  unfold tailWord_8019379
  simp only [CollatzResearch.WordTrace]
  refine ⟨292490781214166958738813191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194993854142777972492542127 292490781214166958738813191)
  ·
    refine ⟨438736171821250438108219787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292490781214166958738813191 438736171821250438108219787)
    ·
      refine ⟨658104257731875657162329681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438736171821250438108219787 658104257731875657162329681)
      ·
        refine ⟨493578193298906742871747261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658104257731875657162329681 493578193298906742871747261)
        ·
          refine ⟨185091822487090028576905223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493578193298906742871747261 185091822487090028576905223)
          ·
            refine ⟨277637733730635042865357835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185091822487090028576905223 277637733730635042865357835)
            ·
              refine ⟨416456600595952564298036753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277637733730635042865357835 416456600595952564298036753)
              ·
                refine ⟨312342450446964423223527565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416456600595952564298036753 312342450446964423223527565)
                ·
                  refine ⟨117128418917611658708822837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312342450446964423223527565 117128418917611658708822837)
                  ·
                    refine ⟨10980789273526093003952141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117128418917611658708822837 10980789273526093003952141)
                    ·
                      refine ⟨4117795977572284876482053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10980789273526093003952141 4117795977572284876482053)
                      ·
                        rfl

theorem cell23_8019379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_8019379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019379 prefixEnd_8019379 := by exact prefixLift 8019379
  have htrace : WordTrace (prefixWord ++ tailWord_8019379) baseStart_8019379 baseEnd_8019379 := by
    simpa [prefixWord, tailWord_8019379, baseEnd_8019379] using wordTrace_append hprefix tailTrace_8019379
  have hstable : (prefixWord ++ tailWord_8019379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019379).length < 2 ^ (prefixWord ++ tailWord_8019379).sum := by decide
  have hdescent : baseEnd_8019379 < baseStart_8019379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019399 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 1, 7]
def baseStart_8019399 : Nat := 118140960795 + 8019399 * 2 ^ 59
def prefixEnd_8019399 : Nat := 4983230072969 + 3 ^ 40 * 8019399 * 2
def baseEnd_8019399 : Nat := 1372602082395124932743987

theorem tailTrace_8019399 : CollatzResearch.WordTrace tailWord_8019399 prefixEnd_8019399 1372602082395124932743987 := by
  unfold tailWord_8019399
  simp only [CollatzResearch.WordTrace]
  refine ⟨292491510674094502154541251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194994340449396334769694167 292491510674094502154541251)
  ·
    refine ⟨438737266011141753231811877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292491510674094502154541251 438737266011141753231811877)
    ·
      refine ⟨82263237377089078730964727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438737266011141753231811877 82263237377089078730964727)
      ·
        refine ⟨123394856065633618096447091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82263237377089078730964727 123394856065633618096447091)
        ·
          refine ⟨185092284098450427144670637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123394856065633618096447091 185092284098450427144670637)
          ·
            refine ⟨69409606536918910179251489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185092284098450427144670637 69409606536918910179251489)
            ·
              refine ⟨52057204902689182634438617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69409606536918910179251489 52057204902689182634438617)
              ·
                refine ⟨39042903677016886975828963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52057204902689182634438617 39042903677016886975828963)
                ·
                  refine ⟨58564355515525330463743445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39042903677016886975828963 58564355515525330463743445)
                  ·
                    refine ⟨1372602082395124932743987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58564355515525330463743445 1372602082395124932743987)
                    ·
                      rfl

theorem cell23_8019399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_8019399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019399 prefixEnd_8019399 := by exact prefixLift 8019399
  have htrace : WordTrace (prefixWord ++ tailWord_8019399) baseStart_8019399 baseEnd_8019399 := by
    simpa [prefixWord, tailWord_8019399, baseEnd_8019399] using wordTrace_append hprefix tailTrace_8019399
  have hstable : (prefixWord ++ tailWord_8019399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019399).length < 2 ^ (prefixWord ++ tailWord_8019399).sum := by decide
  have hdescent : baseEnd_8019399 < baseStart_8019399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019416 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 2, 5]
def baseStart_8019416 : Nat := 118140960795 + 8019416 * 2 ^ 59
def prefixEnd_8019416 : Nat := 4983230072969 + 3 ^ 40 * 8019416 * 2
def baseEnd_8019416 : Nat := 1372604992118833743906461

theorem tailTrace_8019416 : CollatzResearch.WordTrace tailWord_8019416 prefixEnd_8019416 1372604992118833743906461 := by
  unfold tailWord_8019416
  simp only [CollatzResearch.WordTrace]
  refine ⟨146246065357516457028955051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194994753810021942705273401 146246065357516457028955051)
  ·
    refine ⟨219369098036274685543432577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146246065357516457028955051 219369098036274685543432577)
    ·
      refine ⟨164526823527206014157574433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219369098036274685543432577 164526823527206014157574433)
      ·
        refine ⟨123395117645404510618180825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164526823527206014157574433 123395117645404510618180825)
        ·
          refine ⟨92546338234053382963635619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123395117645404510618180825 92546338234053382963635619)
          ·
            refine ⟨138819507351080074445453429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92546338234053382963635619 138819507351080074445453429)
            ·
              refine ⟨13014328814163756979261259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138819507351080074445453429 13014328814163756979261259)
              ·
                refine ⟨19521493221245635468891889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13014328814163756979261259 19521493221245635468891889)
                ·
                  refine ⟨14641119915934226601668917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19521493221245635468891889 14641119915934226601668917)
                  ·
                    refine ⟨1372604992118833743906461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14641119915934226601668917 1372604992118833743906461)
                    ·
                      rfl

theorem cell23_8019416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_8019416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019416 prefixEnd_8019416 := by exact prefixLift 8019416
  have htrace : WordTrace (prefixWord ++ tailWord_8019416) baseStart_8019416 baseEnd_8019416 := by
    simpa [prefixWord, tailWord_8019416, baseEnd_8019416] using wordTrace_append hprefix tailTrace_8019416
  have hstable : (prefixWord ++ tailWord_8019416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019416).length < 2 ^ (prefixWord ++ tailWord_8019416).sum := by decide
  have hdescent : baseEnd_8019416 < baseStart_8019416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019439 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_8019439 : Nat := 118140960795 + 8019439 * 2 ^ 59
def prefixEnd_8019439 : Nat := 4983230072969 + 3 ^ 40 * 8019439 * 2
def baseEnd_8019439 : Nat := 4117826786411554641731777

theorem tailTrace_8019439 : CollatzResearch.WordTrace tailWord_8019439 prefixEnd_8019439 4117826786411554641731777 := by
  unfold tailWord_8019439
  simp only [CollatzResearch.WordTrace]
  refine ⟨292492969593949588985997371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194995313062633059323998247 292492969593949588985997371)
  ·
    refine ⟨438739454390924383478996057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292492969593949588985997371 438739454390924383478996057)
    ·
      refine ⟨329054590793193287609247043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438739454390924383478996057 329054590793193287609247043)
      ·
        refine ⟨493581886189789931413870565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329054590793193287609247043 493581886189789931413870565)
        ·
          refine ⟨92546603660585612140100731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493581886189789931413870565 92546603660585612140100731)
          ·
            refine ⟨138819905490878418210151097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92546603660585612140100731 138819905490878418210151097)
            ·
              refine ⟨104114929118158813657613323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138819905490878418210151097 104114929118158813657613323)
              ·
                refine ⟨156172393677238220486419985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104114929118158813657613323 156172393677238220486419985)
                ·
                  refine ⟨117129295257928665364814989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156172393677238220486419985 117129295257928665364814989)
                  ·
                    refine ⟨43923485721723249511805621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117129295257928665364814989 43923485721723249511805621)
                    ·
                      refine ⟨4117826786411554641731777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43923485721723249511805621 4117826786411554641731777)
                      ·
                        rfl

theorem cell23_8019439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_8019439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019439 prefixEnd_8019439 := by exact prefixLift 8019439
  have htrace : WordTrace (prefixWord ++ tailWord_8019439) baseStart_8019439 baseEnd_8019439 := by
    simpa [prefixWord, tailWord_8019439, baseEnd_8019439] using wordTrace_append hprefix tailTrace_8019439
  have hstable : (prefixWord ++ tailWord_8019439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019439).length < 2 ^ (prefixWord ++ tailWord_8019439).sum := by decide
  have hdescent : baseEnd_8019439 < baseStart_8019439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019449 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_8019449 : Nat := 118140960795 + 8019449 * 2 ^ 59
def prefixEnd_8019449 : Nat := 4983230072969 + 3 ^ 40 * 8019449 * 2
def baseEnd_8019449 : Nat := 4117831921218099602606731

theorem tailTrace_8019449 : CollatzResearch.WordTrace tailWord_8019449 prefixEnd_8019449 4117831921218099602606731 := by
  unfold tailWord_8019449
  simp only [CollatzResearch.WordTrace]
  refine ⟨292493334323913360693861401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194995556215942240462574267 292493334323913360693861401)
  ·
    refine ⟨219370000742935020520396051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292493334323913360693861401 219370000742935020520396051)
    ·
      refine ⟨329055001114402530780594077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219370000742935020520396051 329055001114402530780594077)
      ·
        refine ⟨123395625417900949042722779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329055001114402530780594077 123395625417900949042722779)
        ·
          refine ⟨185093438126851423564084169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123395625417900949042722779 185093438126851423564084169)
          ·
            refine ⟨138820078595138567673063127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185093438126851423564084169 138820078595138567673063127)
            ·
              refine ⟨208230117892707851509594691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138820078595138567673063127 208230117892707851509594691)
              ·
                refine ⟨312345176839061777264392037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208230117892707851509594691 312345176839061777264392037)
                ·
                  refine ⟨58564720657324083237073507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312345176839061777264392037 58564720657324083237073507)
                  ·
                    refine ⟨87847080985986124855610261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58564720657324083237073507 87847080985986124855610261)
                    ·
                      refine ⟨4117831921218099602606731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87847080985986124855610261 4117831921218099602606731)
                      ·
                        rfl

theorem cell23_8019449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_8019449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019449 prefixEnd_8019449 := by exact prefixLift 8019449
  have htrace : WordTrace (prefixWord ++ tailWord_8019449) baseStart_8019449 baseEnd_8019449 := by
    simpa [prefixWord, tailWord_8019449, baseEnd_8019449] using wordTrace_append hprefix tailTrace_8019449
  have hstable : (prefixWord ++ tailWord_8019449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019449).length < 2 ^ (prefixWord ++ tailWord_8019449).sum := by decide
  have hdescent : baseEnd_8019449 < baseStart_8019449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019453 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_8019453 : Nat := 118140960795 + 8019453 * 2 ^ 59
def prefixEnd_8019453 : Nat := 4983230072969 + 3 ^ 40 * 8019453 * 2
def baseEnd_8019453 : Nat := 4117833975140717586956713

theorem tailTrace_8019453 : CollatzResearch.WordTrace tailWord_8019453 prefixEnd_8019453 4117833975140717586956713 := by
  unfold tailWord_8019453
  simp only [CollatzResearch.WordTrace]
  refine ⟨292493480215898869377007013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194995653477265912918004675 292493480215898869377007013)
  ·
    refine ⟨54842527540481038008188815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292493480215898869377007013 54842527540481038008188815)
    ·
      refine ⟨82263791310721557012283223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54842527540481038008188815 82263791310721557012283223)
      ·
        refine ⟨123395686966082335518424835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82263791310721557012283223 123395686966082335518424835)
        ·
          refine ⟨185093530449123503277637253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123395686966082335518424835 185093530449123503277637253)
          ·
            refine ⟨34705036959210656864556985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185093530449123503277637253 34705036959210656864556985)
            ·
              refine ⟨26028777719407992648417739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34705036959210656864556985 26028777719407992648417739)
              ·
                refine ⟨39043166579111988972626609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26028777719407992648417739 39043166579111988972626609)
                ·
                  refine ⟨29282374934333991729469957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39043166579111988972626609 29282374934333991729469957)
                  ·
                    refine ⟨5490445300187623449275617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29282374934333991729469957 5490445300187623449275617)
                    ·
                      refine ⟨4117833975140717586956713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5490445300187623449275617 4117833975140717586956713)
                      ·
                        rfl

theorem cell23_8019453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_8019453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019453 prefixEnd_8019453 := by exact prefixLift 8019453
  have htrace : WordTrace (prefixWord ++ tailWord_8019453) baseStart_8019453 baseEnd_8019453 := by
    simpa [prefixWord, tailWord_8019453, baseEnd_8019453] using wordTrace_append hprefix tailTrace_8019453
  have hstable : (prefixWord ++ tailWord_8019453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019453).length < 2 ^ (prefixWord ++ tailWord_8019453).sum := by decide
  have hdescent : baseEnd_8019453 < baseStart_8019453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019463 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 3, 4]
def baseStart_8019463 : Nat := 118140960795 + 8019463 * 2 ^ 59
def prefixEnd_8019463 : Nat := 4983230072969 + 3 ^ 40 * 8019463 * 2
def baseEnd_8019463 : Nat := 1372613036649087515943889

theorem tailTrace_8019463 : CollatzResearch.WordTrace tailWord_8019463 prefixEnd_8019463 1372613036649087515943889 := by
  unfold tailWord_8019463
  simp only [CollatzResearch.WordTrace]
  refine ⟨292493844945862641084871043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194995896630575094056580695 292493844945862641084871043)
  ·
    refine ⟨438740767418793961627306565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292493844945862641084871043 438740767418793961627306565)
    ·
      refine ⟨82263893891023867805119981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438740767418793961627306565 82263893891023867805119981)
      ·
        refine ⟨30848960209133950426919993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82263893891023867805119981 30848960209133950426919993)
        ·
          refine ⟨23136720156850462820189995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30848960209133950426919993 23136720156850462820189995)
          ·
            refine ⟨34705080235275694230284993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23136720156850462820189995 34705080235275694230284993)
            ·
              refine ⟨26028810176456770672713745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34705080235275694230284993 26028810176456770672713745)
              ·
                refine ⟨19521607632342578004535309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26028810176456770672713745 19521607632342578004535309)
                ·
                  refine ⟨7320602862128466751700741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19521607632342578004535309 7320602862128466751700741)
                  ·
                    refine ⟨1372613036649087515943889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320602862128466751700741 1372613036649087515943889)
                    ·
                      rfl

theorem cell23_8019463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_8019463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019463 prefixEnd_8019463 := by exact prefixLift 8019463
  have htrace : WordTrace (prefixWord ++ tailWord_8019463) baseStart_8019463 baseEnd_8019463 := by
    simpa [prefixWord, tailWord_8019463, baseEnd_8019463] using wordTrace_append hprefix tailTrace_8019463
  have hstable : (prefixWord ++ tailWord_8019463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019463).length < 2 ^ (prefixWord ++ tailWord_8019463).sum := by decide
  have hdescent : baseEnd_8019463 < baseStart_8019463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019499 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7]
def baseStart_8019499 : Nat := 118140960795 + 8019499 * 2 ^ 59
def prefixEnd_8019499 : Nat := 4983230072969 + 3 ^ 40 * 8019499 * 2
def baseEnd_8019499 : Nat := 4117857595250824406981501

theorem tailTrace_8019499 : CollatzResearch.WordTrace tailWord_8019499 prefixEnd_8019499 4117857595250824406981501 := by
  unfold tailWord_8019499
  simp only [CollatzResearch.WordTrace]
  refine ⟨292495157973732219233181551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194996771982488146155454367 292495157973732219233181551)
  ·
    refine ⟨438742736960598328849772327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292495157973732219233181551 438742736960598328849772327)
    ·
      refine ⟨658114105440897493274658491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438742736960598328849772327 658114105440897493274658491)
      ·
        refine ⟨987171158161346239911987737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658114105440897493274658491 987171158161346239911987737)
        ·
          refine ⟨740378368621009679933990803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987171158161346239911987737 740378368621009679933990803)
          ·
            refine ⟨1110567552931514519900986205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740378368621009679933990803 1110567552931514519900986205)
            ·
              refine ⟨416462832349317944962869827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1110567552931514519900986205 416462832349317944962869827)
              ·
                refine ⟨624694248523976917444304741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416462832349317944962869827 624694248523976917444304741)
                ·
                  refine ⟨117130171598245672020807139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624694248523976917444304741 117130171598245672020807139)
                  ·
                    refine ⟨175695257397368508031210709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117130171598245672020807139 175695257397368508031210709)
                    ·
                      refine ⟨4117857595250824406981501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175695257397368508031210709 4117857595250824406981501)
                      ·
                        rfl

theorem cell23_8019499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_8019499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019499 prefixEnd_8019499 := by exact prefixLift 8019499
  have htrace : WordTrace (prefixWord ++ tailWord_8019499) baseStart_8019499 baseEnd_8019499 := by
    simpa [prefixWord, tailWord_8019499, baseEnd_8019499] using wordTrace_append hprefix tailTrace_8019499
  have hstable : (prefixWord ++ tailWord_8019499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019499).length < 2 ^ (prefixWord ++ tailWord_8019499).sum := by decide
  have hdescent : baseEnd_8019499 < baseStart_8019499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019506 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_8019506 : Nat := 118140960795 + 8019506 * 2 ^ 59
def prefixEnd_8019506 : Nat := 4983230072969 + 3 ^ 40 * 8019506 * 2
def baseEnd_8019506 : Nat := 1372620396538468626531323

theorem tailTrace_8019506 : CollatzResearch.WordTrace tailWord_8019506 prefixEnd_8019506 1372620396538468626531323 := by
  unfold tailWord_8019506
  simp only [CollatzResearch.WordTrace]
  refine ⟨73123853321176714857171593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194996942189804572952457581 73123853321176714857171593)
  ·
    refine ⟨54842889990882536142878695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73123853321176714857171593 54842889990882536142878695)
    ·
      refine ⟨82264334986323804214318043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54842889990882536142878695 82264334986323804214318043)
      ·
        refine ⟨123396502479485706321477065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82264334986323804214318043 123396502479485706321477065)
        ·
          refine ⟨92547376859614279741107799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123396502479485706321477065 92547376859614279741107799)
          ·
            refine ⟨138821065289421419611661699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92547376859614279741107799 138821065289421419611661699)
            ·
              refine ⟨208231597934132129417492549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138821065289421419611661699 208231597934132129417492549)
              ·
                refine ⟨39043424612649774265779853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208231597934132129417492549 39043424612649774265779853)
                ·
                  refine ⟨14641284229743665349667445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39043424612649774265779853 14641284229743665349667445)
                  ·
                    refine ⟨1372620396538468626531323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14641284229743665349667445 1372620396538468626531323)
                    ·
                      rfl

theorem cell23_8019506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_8019506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019506 prefixEnd_8019506 := by exact prefixLift 8019506
  have htrace : WordTrace (prefixWord ++ tailWord_8019506) baseStart_8019506 baseEnd_8019506 := by
    simpa [prefixWord, tailWord_8019506, baseEnd_8019506] using wordTrace_append hprefix tailTrace_8019506
  have hstable : (prefixWord ++ tailWord_8019506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019506).length < 2 ^ (prefixWord ++ tailWord_8019506).sum := by decide
  have hdescent : baseEnd_8019506 < baseStart_8019506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019510 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_8019510 : Nat := 118140960795 + 8019510 * 2 ^ 59
def prefixEnd_8019510 : Nat := 4983230072969 + 3 ^ 40 * 8019510 * 2
def baseEnd_8019510 : Nat := 457540360393113762660439

theorem tailTrace_8019510 : CollatzResearch.WordTrace tailWord_8019510 prefixEnd_8019510 457540360393113762660439 := by
  unfold tailWord_8019510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280972448543273006989499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194997039451128245407887989 18280972448543273006989499)
  ·
    refine ⟨27421458672814909510484249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18280972448543273006989499 27421458672814909510484249)
    ·
      refine ⟨20566094004611182132863187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27421458672814909510484249 20566094004611182132863187)
      ·
        refine ⟨30849141006916773199294781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20566094004611182132863187 30849141006916773199294781)
        ·
          refine ⟨11568427877593789949735543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30849141006916773199294781 11568427877593789949735543)
          ·
            refine ⟨17352641816390684924603315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11568427877593789949735543 17352641816390684924603315)
            ·
              refine ⟨26028962724586027386904973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17352641816390684924603315 26028962724586027386904973)
              ·
                refine ⟨9760861021719760270089365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26028962724586027386904973 9760861021719760270089365)
                ·
                  refine ⟨457540360393113762660439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9760861021719760270089365 457540360393113762660439)
                  ·
                    rfl

theorem cell23_8019510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_8019510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019510 prefixEnd_8019510 := by exact prefixLift 8019510
  have htrace : WordTrace (prefixWord ++ tailWord_8019510) baseStart_8019510 baseEnd_8019510 := by
    simpa [prefixWord, tailWord_8019510, baseEnd_8019510] using wordTrace_append hprefix tailTrace_8019510
  have hstable : (prefixWord ++ tailWord_8019510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019510).length < 2 ^ (prefixWord ++ tailWord_8019510).sum := by decide
  have hdescent : baseEnd_8019510 < baseStart_8019510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019530 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_8019530 : Nat := 118140960795 + 8019530 * 2 ^ 59
def prefixEnd_8019530 : Nat := 4983230072969 + 3 ^ 40 * 8019530 * 2
def baseEnd_8019530 : Nat := 4117873513151113785693859

theorem tailTrace_8019530 : CollatzResearch.WordTrace tailWord_8019530 prefixEnd_8019530 4117873513151113785693859 := by
  unfold tailWord_8019530
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124072159154977881890011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194997525757746607685040029 73124072159154977881890011)
  ·
    refine ⟨109686108238732466822835017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73124072159154977881890011 109686108238732466822835017)
    ·
      refine ⟨82264581179049350117126263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109686108238732466822835017 82264581179049350117126263)
      ·
        refine ⟨123396871768574025175689395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82264581179049350117126263 123396871768574025175689395)
        ·
          refine ⟨185095307652861037763534093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123396871768574025175689395 185095307652861037763534093)
          ·
            refine ⟨69410740369822889161325285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185095307652861037763534093 69410740369822889161325285)
            ·
              refine ⟨13014513819341791717748491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69410740369822889161325285 13014513819341791717748491)
              ·
                refine ⟨19521770729012687576622737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13014513819341791717748491 19521770729012687576622737)
                ·
                  refine ⟨14641328046759515682467053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19521770729012687576622737 14641328046759515682467053)
                  ·
                    refine ⟨5490498017534818380925145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14641328046759515682467053 5490498017534818380925145)
                    ·
                      refine ⟨4117873513151113785693859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5490498017534818380925145 4117873513151113785693859)
                      ·
                        rfl

theorem cell23_8019530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_8019530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019530 prefixEnd_8019530 := by exact prefixLift 8019530
  have htrace : WordTrace (prefixWord ++ tailWord_8019530) baseStart_8019530 baseEnd_8019530 := by
    simpa [prefixWord, tailWord_8019530, baseEnd_8019530] using wordTrace_append hprefix tailTrace_8019530
  have hstable : (prefixWord ++ tailWord_8019530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019530).length < 2 ^ (prefixWord ++ tailWord_8019530).sum := by decide
  have hdescent : baseEnd_8019530 < baseStart_8019530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019536 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 1, 6]
def baseStart_8019536 : Nat := 118140960795 + 8019536 * 2 ^ 59
def prefixEnd_8019536 : Nat := 4983230072969 + 3 ^ 40 * 8019536 * 2
def baseEnd_8019536 : Nat := 1372625531345013587406277

theorem tailTrace_8019536 : CollatzResearch.WordTrace tailWord_8019536 prefixEnd_8019536 1372625531345013587406277 := by
  unfold tailWord_8019536
  simp only [CollatzResearch.WordTrace]
  refine ⟨146248253737299087276139231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194997671649732116368185641 146248253737299087276139231)
  ·
    refine ⟨219372380605948630914208847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146248253737299087276139231 219372380605948630914208847)
    ·
      refine ⟨329058570908922946371313271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219372380605948630914208847 329058570908922946371313271)
      ·
        refine ⟨493587856363384419556969907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329058570908922946371313271 493587856363384419556969907)
        ·
          refine ⟨740381784545076629335454861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493587856363384419556969907 740381784545076629335454861)
          ·
            refine ⟨277643169204403736000795573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740381784545076629335454861 277643169204403736000795573)
            ·
              refine ⟨26029047112912850250074585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277643169204403736000795573 26029047112912850250074585)
              ·
                refine ⟨19521785334684637687555939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26029047112912850250074585 19521785334684637687555939)
                ·
                  refine ⟨29282678002026956531333909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19521785334684637687555939 29282678002026956531333909)
                  ·
                    refine ⟨1372625531345013587406277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29282678002026956531333909 1372625531345013587406277)
                    ·
                      rfl

theorem cell23_8019536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_8019536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019536 prefixEnd_8019536 := by exact prefixLift 8019536
  have htrace : WordTrace (prefixWord ++ tailWord_8019536) baseStart_8019536 baseEnd_8019536 := by
    simpa [prefixWord, tailWord_8019536, baseEnd_8019536] using wordTrace_append hprefix tailTrace_8019536
  have hstable : (prefixWord ++ tailWord_8019536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019536).length < 2 ^ (prefixWord ++ tailWord_8019536).sum := by decide
  have hdescent : baseEnd_8019536 < baseStart_8019536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019540 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_8019540 : Nat := 118140960795 + 8019540 * 2 ^ 59
def prefixEnd_8019540 : Nat := 4983230072969 + 3 ^ 40 * 8019540 * 2
def baseEnd_8019540 : Nat := 1372626215985886248856271

theorem tailTrace_8019540 : CollatzResearch.WordTrace tailWord_8019540 prefixEnd_8019540 1372626215985886248856271 := by
  unfold tailWord_8019540
  simp only [CollatzResearch.WordTrace]
  refine ⟨146248326683291841617712037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194997768911055788823616049 146248326683291841617712037)
  ·
    refine ⟨27421561253117220303321007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146248326683291841617712037 27421561253117220303321007)
    ·
      refine ⟨41132341879675830454981511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27421561253117220303321007 41132341879675830454981511)
      ·
        refine ⟨61698512819513745682472267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41132341879675830454981511 61698512819513745682472267)
        ·
          refine ⟨92547769229270618523708401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61698512819513745682472267 92547769229270618523708401)
          ·
            refine ⟨69410826921952963892781301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92547769229270618523708401 69410826921952963892781301)
            ·
              refine ⟨6507265023933090364948247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69410826921952963892781301 6507265023933090364948247)
              ·
                refine ⟨9760897535899635547422371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507265023933090364948247 9760897535899635547422371)
                ·
                  refine ⟨14641346303849453321133557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760897535899635547422371 14641346303849453321133557)
                  ·
                    refine ⟨1372626215985886248856271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14641346303849453321133557 1372626215985886248856271)
                    ·
                      rfl

theorem cell23_8019540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_8019540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019540 prefixEnd_8019540 := by exact prefixLift 8019540
  have htrace : WordTrace (prefixWord ++ tailWord_8019540) baseStart_8019540 baseEnd_8019540 := by
    simpa [prefixWord, tailWord_8019540, baseEnd_8019540] using wordTrace_append hprefix tailTrace_8019540
  have hstable : (prefixWord ++ tailWord_8019540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019540).length < 2 ^ (prefixWord ++ tailWord_8019540).sum := by decide
  have hdescent : baseEnd_8019540 < baseStart_8019540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019570 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_8019570 : Nat := 118140960795 + 8019570 * 2 ^ 59
def prefixEnd_8019570 : Nat := 4983230072969 + 3 ^ 40 * 8019570 * 2
def baseEnd_8019570 : Nat := 1372631350792431209731225

theorem tailTrace_8019570 : CollatzResearch.WordTrace tailWord_8019570 prefixEnd_8019570 1372631350792431209731225 := by
  unfold tailWord_8019570
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124436889118749589754041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194998498370983332239344109 73124436889118749589754041)
  ·
    refine ⟨54843327666839062192315531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73124436889118749589754041 54843327666839062192315531)
    ·
      refine ⟨82264991500258593288473297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54843327666839062192315531 82264991500258593288473297)
      ·
        refine ⟨61698743625193944966354973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82264991500258593288473297 61698743625193944966354973)
        ·
          refine ⟨23137028859447729362383115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61698743625193944966354973 23137028859447729362383115)
          ·
            refine ⟨34705543289171594043574673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23137028859447729362383115 34705543289171594043574673)
            ·
              refine ⟨26029157466878695532681005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34705543289171594043574673 26029157466878695532681005)
              ·
                refine ⟨9760934050079510824755377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26029157466878695532681005 9760934050079510824755377)
                ·
                  refine ⟨7320700537559633118566533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9760934050079510824755377 7320700537559633118566533)
                  ·
                    refine ⟨1372631350792431209731225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320700537559633118566533 1372631350792431209731225)
                    ·
                      rfl

theorem cell23_8019570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_8019570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019570 prefixEnd_8019570 := by exact prefixLift 8019570
  have htrace : WordTrace (prefixWord ++ tailWord_8019570) baseStart_8019570 baseEnd_8019570 := by
    simpa [prefixWord, tailWord_8019570, baseEnd_8019570] using wordTrace_append hprefix tailTrace_8019570
  have hstable : (prefixWord ++ tailWord_8019570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019570).length < 2 ^ (prefixWord ++ tailWord_8019570).sum := by decide
  have hdescent : baseEnd_8019570 < baseStart_8019570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019593 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 3]
def baseStart_8019593 : Nat := 118140960795 + 8019593 * 2 ^ 59
def prefixEnd_8019593 : Nat := 4983230072969 + 3 ^ 40 * 8019593 * 2
def baseEnd_8019593 : Nat := 4117905862432347039206069

theorem tailTrace_8019593 : CollatzResearch.WordTrace tailWord_8019593 prefixEnd_8019593 4117905862432347039206069 := by
  unfold tailWord_8019593
  simp only [CollatzResearch.WordTrace]
  refine ⟨292498586435391673287103433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194999057623594448858068955 292498586435391673287103433)
  ·
    refine ⟨219373939826543754965327575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292498586435391673287103433 219373939826543754965327575)
    ·
      refine ⟨329060909739815632447991363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219373939826543754965327575 329060909739815632447991363)
      ·
        refine ⟨493591364609723448671987045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329060909739815632447991363 493591364609723448671987045)
        ·
          refine ⟨92548380864323146625997571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493591364609723448671987045 92548380864323146625997571)
          ·
            refine ⟨138822571296484719938996357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92548380864323146625997571 138822571296484719938996357)
            ·
              refine ⟨26029232118090884988561817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138822571296484719938996357 26029232118090884988561817)
              ·
                refine ⟨19521924088568163741421363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26029232118090884988561817 19521924088568163741421363)
                ·
                  refine ⟨29282886132852245612132045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19521924088568163741421363 29282886132852245612132045)
                  ·
                    refine ⟨10981082299819592104549517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29282886132852245612132045 10981082299819592104549517)
                    ·
                      refine ⟨4117905862432347039206069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981082299819592104549517 4117905862432347039206069)
                      ·
                        rfl

theorem cell23_8019593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_8019593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019593 prefixEnd_8019593 := by exact prefixLift 8019593
  have htrace : WordTrace (prefixWord ++ tailWord_8019593) baseStart_8019593 baseEnd_8019593 := by
    simpa [prefixWord, tailWord_8019593, baseEnd_8019593] using wordTrace_append hprefix tailTrace_8019593
  have hstable : (prefixWord ++ tailWord_8019593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019593).length < 2 ^ (prefixWord ++ tailWord_8019593).sum := by decide
  have hdescent : baseEnd_8019593 < baseStart_8019593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019594 : List Nat := [3, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_8019594 : Nat := 118140960795 + 8019594 * 2 ^ 59
def prefixEnd_8019594 : Nat := 4983230072969 + 3 ^ 40 * 8019594 * 2
def baseEnd_8019594 : Nat := 4117906375913001535293565

theorem tailTrace_8019594 : CollatzResearch.WordTrace tailWord_8019594 prefixEnd_8019594 4117906375913001535293565 := by
  unfold tailWord_8019594
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124655727097012614472459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194999081938925366971926557 73124655727097012614472459)
  ·
    refine ⟨109686983590645518921708689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73124655727097012614472459 109686983590645518921708689)
    ·
      refine ⟨82265237692984139191281517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109686983590645518921708689 82265237692984139191281517)
      ·
        refine ⟨30849464134869052196730569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82265237692984139191281517 30849464134869052196730569)
        ·
          refine ⟨23137098101151789147547927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30849464134869052196730569 23137098101151789147547927)
          ·
            refine ⟨34705647151727683721321891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23137098101151789147547927 34705647151727683721321891)
            ·
              refine ⟨52058470727591525581982837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34705647151727683721321891 52058470727591525581982837)
              ·
                refine ⟨4880481630711705523310891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52058470727591525581982837 4880481630711705523310891)
                ·
                  refine ⟨7320722446067558284966337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880481630711705523310891 7320722446067558284966337)
                  ·
                    refine ⟨5490541834550668713724753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7320722446067558284966337 5490541834550668713724753)
                    ·
                      refine ⟨4117906375913001535293565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5490541834550668713724753 4117906375913001535293565)
                      ·
                        rfl

theorem cell23_8019594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_8019594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019594 prefixEnd_8019594 := by exact prefixLift 8019594
  have htrace : WordTrace (prefixWord ++ tailWord_8019594) baseStart_8019594 baseEnd_8019594 := by
    simpa [prefixWord, tailWord_8019594, baseEnd_8019594] using wordTrace_append hprefix tailTrace_8019594
  have hstable : (prefixWord ++ tailWord_8019594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019594).length < 2 ^ (prefixWord ++ tailWord_8019594).sum := by decide
  have hdescent : baseEnd_8019594 < baseStart_8019594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019604 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_8019604 : Nat := 118140960795 + 8019604 * 2 ^ 59
def prefixEnd_8019604 : Nat := 4983230072969 + 3 ^ 40 * 8019604 * 2
def baseEnd_8019604 : Nat := 1372637170239848832056173

theorem tailTrace_8019604 : CollatzResearch.WordTrace tailWord_8019604 prefixEnd_8019604 1372637170239848832056173 := by
  unfold tailWord_8019604
  simp only [CollatzResearch.WordTrace]
  refine ⟨146249493819175911082876933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194999325092234548110502577 146249493819175911082876933)
  ·
    refine ⟨27421780091095483328039425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146249493819175911082876933 27421780091095483328039425)
    ·
      refine ⟨20566335068321612496029569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27421780091095483328039425 20566335068321612496029569)
      ·
        refine ⟨15424751301241209372022177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20566335068321612496029569 15424751301241209372022177)
        ·
          refine ⟨11568563475930907029016633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15424751301241209372022177 11568563475930907029016633)
          ·
            refine ⟨8676422606948180271762475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11568563475930907029016633 8676422606948180271762475)
            ·
              refine ⟨13014633910422270407643713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676422606948180271762475 13014633910422270407643713)
              ·
                refine ⟨9760975432816702805732785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13014633910422270407643713 9760975432816702805732785)
                ·
                  refine ⟨7320731574612527104299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9760975432816702805732785 7320731574612527104299589)
                  ·
                    refine ⟨1372637170239848832056173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320731574612527104299589 1372637170239848832056173)
                    ·
                      rfl

theorem cell23_8019604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_8019604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019604 prefixEnd_8019604 := by exact prefixLift 8019604
  have htrace : WordTrace (prefixWord ++ tailWord_8019604) baseStart_8019604 baseEnd_8019604 := by
    simpa [prefixWord, tailWord_8019604, baseEnd_8019604] using wordTrace_append hprefix tailTrace_8019604
  have hstable : (prefixWord ++ tailWord_8019604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019604).length < 2 ^ (prefixWord ++ tailWord_8019604).sum := by decide
  have hdescent : baseEnd_8019604 < baseStart_8019604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019673 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 7]
def baseStart_8019673 : Nat := 118140960795 + 8019673 * 2 ^ 59
def prefixEnd_8019673 : Nat := 4983230072969 + 3 ^ 40 * 8019673 * 2
def baseEnd_8019673 : Nat := 457549660098300747356189

theorem tailTrace_8019673 : CollatzResearch.WordTrace tailWord_8019673 prefixEnd_8019673 457549660098300747356189 := by
  unfold tailWord_8019673
  simp only [CollatzResearch.WordTrace]
  refine ⟨292501504275101846950015673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195001002850067897966677115 292501504275101846950015673)
  ·
    refine ⟨219376128206326385212511755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292501504275101846950015673 219376128206326385212511755)
    ·
      refine ⟨329064192309489577818767633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219376128206326385212511755 329064192309489577818767633)
      ·
        refine ⟨246798144232117183364075725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329064192309489577818767633 246798144232117183364075725)
        ·
          refine ⟨92549304087043943761528397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246798144232117183364075725 92549304087043943761528397)
          ·
            refine ⟨34705989032641478910573149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92549304087043943761528397 34705989032641478910573149)
            ·
              refine ⟨13014745887240554591464931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34705989032641478910573149 13014745887240554591464931)
              ·
                refine ⟨19522118830860831887197397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13014745887240554591464931 19522118830860831887197397)
                ·
                  refine ⟨457549660098300747356189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19522118830860831887197397 457549660098300747356189)
                  ·
                    rfl

theorem cell23_8019673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 7].length) (baseStart_8019673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019673 prefixEnd_8019673 := by exact prefixLift 8019673
  have htrace : WordTrace (prefixWord ++ tailWord_8019673) baseStart_8019673 baseEnd_8019673 := by
    simpa [prefixWord, tailWord_8019673, baseEnd_8019673] using wordTrace_append hprefix tailTrace_8019673
  have hstable : (prefixWord ++ tailWord_8019673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019673).length < 2 ^ (prefixWord ++ tailWord_8019673).sum := by decide
  have hdescent : baseEnd_8019673 < baseStart_8019673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019703 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 2, 5]
def baseStart_8019703 : Nat := 118140960795 + 8019703 * 2 ^ 59
def prefixEnd_8019703 : Nat := 4983230072969 + 3 ^ 40 * 8019703 * 2
def baseEnd_8019703 : Nat := 1372654115101447202943521

theorem tailTrace_8019703 : CollatzResearch.WordTrace tailWord_8019703 prefixEnd_8019703 1372654115101447202943521 := by
  unfold tailWord_8019703
  simp only [CollatzResearch.WordTrace]
  refine ⟨292502598464993162073607763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195001732309995441382405175 292502598464993162073607763)
  ·
    refine ⟨438753897697489743110411645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292502598464993162073607763 438753897697489743110411645)
    ·
      refine ⟨164532711636558653666404367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438753897697489743110411645 164532711636558653666404367)
      ·
        refine ⟨246799067454837980499606551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164532711636558653666404367 246799067454837980499606551)
        ·
          refine ⟨370198601182256970749409827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246799067454837980499606551 370198601182256970749409827)
          ·
            refine ⟨555297901773385456124114741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370198601182256970749409827 555297901773385456124114741)
            ·
              refine ⟨52059178291254886511635757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 555297901773385456124114741 52059178291254886511635757)
              ·
                refine ⟨19522191859220582441863409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52059178291254886511635757 19522191859220582441863409)
                ·
                  refine ⟨14641643894415436831397557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19522191859220582441863409 14641643894415436831397557)
                  ·
                    refine ⟨1372654115101447202943521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14641643894415436831397557 1372654115101447202943521)
                    ·
                      rfl

theorem cell23_8019703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_8019703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019703 prefixEnd_8019703 := by exact prefixLift 8019703
  have htrace : WordTrace (prefixWord ++ tailWord_8019703) baseStart_8019703 baseEnd_8019703 := by
    simpa [prefixWord, tailWord_8019703, baseEnd_8019703] using wordTrace_append hprefix tailTrace_8019703
  have hstable : (prefixWord ++ tailWord_8019703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019703).length < 2 ^ (prefixWord ++ tailWord_8019703).sum := by decide
  have hdescent : baseEnd_8019703 < baseStart_8019703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019713 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_8019713 : Nat := 118140960795 + 8019713 * 2 ^ 59
def prefixEnd_8019713 : Nat := 4983230072969 + 3 ^ 40 * 8019713 * 2
def baseEnd_8019713 : Nat := 4117967480110886569705517

theorem tailTrace_8019713 : CollatzResearch.WordTrace tailWord_8019713 prefixEnd_8019713 4117967480110886569705517 := by
  unfold tailWord_8019713
  simp only [CollatzResearch.WordTrace]
  refine ⟨292502963194956933781471793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195001975463304622520981195 292502963194956933781471793)
  ·
    refine ⟨219377222396217700336103845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292502963194956933781471793 219377222396217700336103845)
    ·
      refine ⟨41133229199290818813019471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219377222396217700336103845 41133229199290818813019471)
      ·
        refine ⟨61699843798936228219529207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41133229199290818813019471 61699843798936228219529207)
        ·
          refine ⟨92549765698404342329293811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61699843798936228219529207 92549765698404342329293811)
          ·
            refine ⟨138824648547606513493940717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92549765698404342329293811 138824648547606513493940717)
            ·
              refine ⟨52059243205352442560227769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138824648547606513493940717 52059243205352442560227769)
              ·
                refine ⟨39044432404014331920170827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52059243205352442560227769 39044432404014331920170827)
                ·
                  refine ⟨58566648606021497880256241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39044432404014331920170827 58566648606021497880256241)
                  ·
                    refine ⟨43924986454516123410192181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58566648606021497880256241 43924986454516123410192181)
                    ·
                      refine ⟨4117967480110886569705517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43924986454516123410192181 4117967480110886569705517)
                      ·
                        rfl

theorem cell23_8019713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_8019713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019713 prefixEnd_8019713 := by exact prefixLift 8019713
  have htrace : WordTrace (prefixWord ++ tailWord_8019713) baseStart_8019713 baseEnd_8019713 := by
    simpa [prefixWord, tailWord_8019713, baseEnd_8019713] using wordTrace_append hprefix tailTrace_8019713
  have hstable : (prefixWord ++ tailWord_8019713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019713).length < 2 ^ (prefixWord ++ tailWord_8019713).sum := by decide
  have hdescent : baseEnd_8019713 < baseStart_8019713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019783 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_8019783 : Nat := 118140960795 + 8019783 * 2 ^ 59
def prefixEnd_8019783 : Nat := 4983230072969 + 3 ^ 40 * 8019783 * 2
def baseEnd_8019783 : Nat := 4118003423756701295830195

theorem tailTrace_8019783 : CollatzResearch.WordTrace tailWord_8019783 prefixEnd_8019783 4118003423756701295830195 := by
  unfold tailWord_8019783
  simp only [CollatzResearch.WordTrace]
  refine ⟨292505516304703335736520003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195003677536468890491013335 292505516304703335736520003)
  ·
    refine ⟨438758274457055003604780005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292505516304703335736520003 438758274457055003604780005)
    ·
      refine ⟨82267176460697813175896251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438758274457055003604780005 82267176460697813175896251)
      ·
        refine ⟨123400764691046719763844377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82267176460697813175896251 123400764691046719763844377)
        ·
          refine ⟨92550573518285039822883283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123400764691046719763844377 92550573518285039822883283)
          ·
            refine ⟨138825860277427559734324925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92550573518285039822883283 138825860277427559734324925)
            ·
              refine ⟨52059697604035334900371847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138825860277427559734324925 52059697604035334900371847)
              ·
                refine ⟨78089546406053002350557771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52059697604035334900371847 78089546406053002350557771)
                ·
                  refine ⟨117134319609079503525836657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78089546406053002350557771 117134319609079503525836657)
                  ·
                    refine ⟨87850739706809627644377493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117134319609079503525836657 87850739706809627644377493)
                    ·
                      refine ⟨4118003423756701295830195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87850739706809627644377493 4118003423756701295830195)
                      ·
                        rfl

theorem cell23_8019783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_8019783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019783 prefixEnd_8019783 := by exact prefixLift 8019783
  have htrace : WordTrace (prefixWord ++ tailWord_8019783) baseStart_8019783 baseEnd_8019783 := by
    simpa [prefixWord, tailWord_8019783, baseEnd_8019783] using wordTrace_append hprefix tailTrace_8019783
  have hstable : (prefixWord ++ tailWord_8019783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019783).length < 2 ^ (prefixWord ++ tailWord_8019783).sum := by decide
  have hdescent : baseEnd_8019783 < baseStart_8019783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019797 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 6]
def baseStart_8019797 : Nat := 118140960795 + 8019797 * 2 ^ 59
def prefixEnd_8019797 : Nat := 4983230072969 + 3 ^ 40 * 8019797 * 2
def baseEnd_8019797 : Nat := 457556734720651582339459

theorem tailTrace_8019797 : CollatzResearch.WordTrace tailWord_8019797 prefixEnd_8019797 457556734720651582339459 := by
  unfold tailWord_8019797
  simp only [CollatzResearch.WordTrace]
  refine ⟨292506026926652616127529645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195004017951101744085019763 292506026926652616127529645)
  ·
    refine ⟨109689760097494731047823617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292506026926652616127529645 109689760097494731047823617)
    ·
      refine ⟨82267320073121048285867713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109689760097494731047823617 82267320073121048285867713)
      ·
        refine ⟨61700490054840786214400785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82267320073121048285867713 61700490054840786214400785)
        ·
          refine ⟨46275367541130589660800589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61700490054840786214400785 46275367541130589660800589)
          ·
            refine ⟨17353262827923971122800221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46275367541130589660800589 17353262827923971122800221)
            ·
              refine ⟨6507473560471489171050083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17353262827923971122800221 6507473560471489171050083)
              ·
                refine ⟨9761210340707233756575125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507473560471489171050083 9761210340707233756575125)
                ·
                  refine ⟨457556734720651582339459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9761210340707233756575125 457556734720651582339459)
                  ·
                    rfl

theorem cell23_8019797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_8019797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019797 prefixEnd_8019797 := by exact prefixLift 8019797
  have htrace : WordTrace (prefixWord ++ tailWord_8019797) baseStart_8019797 baseEnd_8019797 := by
    simpa [prefixWord, tailWord_8019797, baseEnd_8019797] using wordTrace_append hprefix tailTrace_8019797
  have hstable : (prefixWord ++ tailWord_8019797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019797).length < 2 ^ (prefixWord ++ tailWord_8019797).sum := by decide
  have hdescent : baseEnd_8019797 < baseStart_8019797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019807 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 3]
def baseStart_8019807 : Nat := 118140960795 + 8019807 * 2 ^ 59
def prefixEnd_8019807 : Nat := 4983230072969 + 3 ^ 40 * 8019807 * 2
def baseEnd_8019807 : Nat := 4118015747292409201930085

theorem tailTrace_8019807 : CollatzResearch.WordTrace tailWord_8019807 prefixEnd_8019807 4118015747292409201930085 := by
  unfold tailWord_8019807
  simp only [CollatzResearch.WordTrace]
  refine ⟨292506391656616387835393675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195004261104410925223595783 292506391656616387835393675)
  ·
    refine ⟨438759587484924581753090513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292506391656616387835393675 438759587484924581753090513)
    ·
      refine ⟨329069690613693436314817885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438759587484924581753090513 329069690613693436314817885)
      ·
        refine ⟨123401133980135038618056707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329069690613693436314817885 123401133980135038618056707)
        ·
          refine ⟨185101700970202557927085061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123401133980135038618056707 185101700970202557927085061)
          ·
            refine ⟨34706568931912979611328449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185101700970202557927085061 34706568931912979611328449)
            ·
              refine ⟨26029926698934734708496337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34706568931912979611328449 26029926698934734708496337)
              ·
                refine ⟨19522445024201051031372253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26029926698934734708496337 19522445024201051031372253)
                ·
                  refine ⟨7320916884075394136764595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19522445024201051031372253 7320916884075394136764595)
                  ·
                    refine ⟨10981375326113091205146893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7320916884075394136764595 10981375326113091205146893)
                    ·
                      refine ⟨4118015747292409201930085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981375326113091205146893 4118015747292409201930085)
                      ·
                        rfl

theorem cell23_8019807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_8019807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019807 prefixEnd_8019807 := by exact prefixLift 8019807
  have htrace : WordTrace (prefixWord ++ tailWord_8019807) baseStart_8019807 baseEnd_8019807 := by
    simpa [prefixWord, tailWord_8019807, baseEnd_8019807] using wordTrace_append hprefix tailTrace_8019807
  have hstable : (prefixWord ++ tailWord_8019807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019807).length < 2 ^ (prefixWord ++ tailWord_8019807).sum := by decide
  have hdescent : baseEnd_8019807 < baseStart_8019807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019818 : List Nat := [3, 1, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_8019818 : Nat := 118140960795 + 8019818 * 2 ^ 59
def prefixEnd_8019818 : Nat := 4983230072969 + 3 ^ 40 * 8019818 * 2
def baseEnd_8019818 : Nat := 1372673798526536219630845

theorem tailTrace_8019818 : CollatzResearch.WordTrace tailWord_8019818 prefixEnd_8019818 1372673798526536219630845 := by
  unfold tailWord_8019818
  simp only [CollatzResearch.WordTrace]
  refine ⟨73126698214894134178511027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195004528573051024476029405 73126698214894134178511027)
  ·
    refine ⟨109690047322341201267766541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73126698214894134178511027 109690047322341201267766541)
    ·
      refine ⟨41133767745877950475412453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109690047322341201267766541 41133767745877950475412453)
      ·
        refine ⟨7712581452352115714139835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41133767745877950475412453 7712581452352115714139835)
        ·
          refine ⟨11568872178528173571209753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712581452352115714139835 11568872178528173571209753)
          ·
            refine ⟨8676654133896130178407315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11568872178528173571209753 8676654133896130178407315)
            ·
              refine ⟨13014981200844195267610973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676654133896130178407315 13014981200844195267610973)
              ·
                refine ⟨4880617950316573225354115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13014981200844195267610973 4880617950316573225354115)
                ·
                  refine ⟨7320926925474859838031173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880617950316573225354115 7320926925474859838031173)
                  ·
                    refine ⟨1372673798526536219630845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320926925474859838031173 1372673798526536219630845)
                    ·
                      rfl

theorem cell23_8019818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_8019818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019818 prefixEnd_8019818 := by exact prefixLift 8019818
  have htrace : WordTrace (prefixWord ++ tailWord_8019818) baseStart_8019818 baseEnd_8019818 := by
    simpa [prefixWord, tailWord_8019818, baseEnd_8019818] using wordTrace_append hprefix tailTrace_8019818
  have hstable : (prefixWord ++ tailWord_8019818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019818).length < 2 ^ (prefixWord ++ tailWord_8019818).sum := by decide
  have hdescent : baseEnd_8019818 < baseStart_8019818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019840 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 4, 4]
def baseStart_8019840 : Nat := 118140960795 + 8019840 * 2 ^ 59
def prefixEnd_8019840 : Nat := 4983230072969 + 3 ^ 40 * 8019840 * 2
def baseEnd_8019840 : Nat := 1372677564051335857605811

theorem tailTrace_8019840 : CollatzResearch.WordTrace tailWord_8019840 prefixEnd_8019840 1372677564051335857605811 := by
  unfold tailWord_8019840
  simp only [CollatzResearch.WordTrace]
  refine ⟨146253797632748417235672487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195005063510331222980896649 146253797632748417235672487)
  ·
    refine ⟨219380696449122625853508731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146253797632748417235672487 219380696449122625853508731)
    ·
      refine ⟨329071044673683938780263097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219380696449122625853508731 329071044673683938780263097)
      ·
        refine ⟨246803283505262954085197323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329071044673683938780263097 246803283505262954085197323)
        ·
          refine ⟨370204925257894431127795985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246803283505262954085197323 370204925257894431127795985)
          ·
            refine ⟨277653693943420823345846989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370204925257894431127795985 277653693943420823345846989)
            ·
              refine ⟨104120135228782808754692621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277653693943420823345846989 104120135228782808754692621)
              ·
                refine ⟨39045050710793553283009733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104120135228782808754692621 39045050710793553283009733)
                ·
                  refine ⟨7320947008273791240564325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39045050710793553283009733 7320947008273791240564325)
                  ·
                    refine ⟨1372677564051335857605811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320947008273791240564325 1372677564051335857605811)
                    ·
                      rfl

theorem cell23_8019840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_8019840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019840 prefixEnd_8019840 := by exact prefixLift 8019840
  have htrace : WordTrace (prefixWord ++ tailWord_8019840) baseStart_8019840 baseEnd_8019840 := by
    simpa [prefixWord, tailWord_8019840, baseEnd_8019840] using wordTrace_append hprefix tailTrace_8019840
  have hstable : (prefixWord ++ tailWord_8019840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019840).length < 2 ^ (prefixWord ++ tailWord_8019840).sum := by decide
  have hdescent : baseEnd_8019840 < baseStart_8019840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019864 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_8019864 : Nat := 118140960795 + 8019864 * 2 ^ 59
def prefixEnd_8019864 : Nat := 4983230072969 + 3 ^ 40 * 8019864 * 2
def baseEnd_8019864 : Nat := 4118045015689715478917323

theorem tailTrace_8019864 : CollatzResearch.WordTrace tailWord_8019864 prefixEnd_8019864 4118045015689715478917323 := by
  unfold tailWord_8019864
  simp only [CollatzResearch.WordTrace]
  refine ⟨146254235308704943285109323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195005647078273257713479097 146254235308704943285109323)
  ·
    refine ⟨219381352963057414927663985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146254235308704943285109323 219381352963057414927663985)
    ·
      refine ⟨164536014722293061195747989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219381352963057414927663985 164536014722293061195747989)
      ·
        refine ⟨7712625690107487243550687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164536014722293061195747989 7712625690107487243550687)
        ·
          refine ⟨11568938535161230865326031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712625690107487243550687 11568938535161230865326031)
          ·
            refine ⟨17353407802741846297989047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11568938535161230865326031 17353407802741846297989047)
            ·
              refine ⟨26030111704112769446983571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17353407802741846297989047 26030111704112769446983571)
              ·
                refine ⟨39045167556169154170475357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26030111704112769446983571 39045167556169154170475357)
                ·
                  refine ⟨14641937833563432813928259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39045167556169154170475357 14641937833563432813928259)
                  ·
                    refine ⟨21962906750345149220892389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14641937833563432813928259 21962906750345149220892389)
                    ·
                      refine ⟨4118045015689715478917323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21962906750345149220892389 4118045015689715478917323)
                      ·
                        rfl

theorem cell23_8019864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_8019864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019864 prefixEnd_8019864 := by exact prefixLift 8019864
  have htrace : WordTrace (prefixWord ++ tailWord_8019864) baseStart_8019864 baseEnd_8019864 := by
    simpa [prefixWord, tailWord_8019864, baseEnd_8019864] using wordTrace_append hprefix tailTrace_8019864
  have hstable : (prefixWord ++ tailWord_8019864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019864).length < 2 ^ (prefixWord ++ tailWord_8019864).sum := by decide
  have hdescent : baseEnd_8019864 < baseStart_8019864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019883 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 9]
def baseStart_8019883 : Nat := 118140960795 + 8019883 * 2 ^ 59
def prefixEnd_8019883 : Nat := 4983230072969 + 3 ^ 40 * 8019883 * 2
def baseEnd_8019883 : Nat := 1372684923940716968193245

theorem tailTrace_8019883 : CollatzResearch.WordTrace tailWord_8019883 prefixEnd_8019883 1372684923940716968193245 := by
  unfold tailWord_8019883
  simp only [CollatzResearch.WordTrace]
  refine ⟨292509163604341052815160303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195006109069560701876773535 292509163604341052815160303)
  ·
    refine ⟨438763745406511579222740455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292509163604341052815160303 438763745406511579222740455)
    ·
      refine ⟨658145618109767368834110683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438763745406511579222740455 658145618109767368834110683)
      ·
        refine ⟨987218427164651053251166025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658145618109767368834110683 987218427164651053251166025)
        ·
          refine ⟨740413820373488289938374519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987218427164651053251166025 740413820373488289938374519)
          ·
            refine ⟨1110620730560232434907561779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740413820373488289938374519 1110620730560232434907561779)
            ·
              refine ⟨1665931095840348652361342669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110620730560232434907561779 1665931095840348652361342669)
              ·
                refine ⟨624724160940130744635503501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1665931095840348652361342669 624724160940130744635503501)
                ·
                  refine ⟨234271560352549029238313813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624724160940130744635503501 234271560352549029238313813)
                  ·
                    refine ⟨1372684923940716968193245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234271560352549029238313813 1372684923940716968193245)
                    ·
                      rfl

theorem cell23_8019883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_8019883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019883 prefixEnd_8019883 := by exact prefixLift 8019883
  have htrace : WordTrace (prefixWord ++ tailWord_8019883) baseStart_8019883 baseEnd_8019883 := by
    simpa [prefixWord, tailWord_8019883, baseEnd_8019883] using wordTrace_append hprefix tailTrace_8019883
  have hstable : (prefixWord ++ tailWord_8019883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019883).length < 2 ^ (prefixWord ++ tailWord_8019883).sum := by decide
  have hdescent : baseEnd_8019883 < baseStart_8019883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019892 : List Nat := [2, 5, 2, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_8019892 : Nat := 118140960795 + 8019892 * 2 ^ 59
def prefixEnd_8019892 : Nat := 4983230072969 + 3 ^ 40 * 8019892 * 2
def baseEnd_8019892 : Nat := 4118059393148041369367195

theorem tailTrace_8019892 : CollatzResearch.WordTrace tailWord_8019892 prefixEnd_8019892 4118059393148041369367195 := by
  unfold tailWord_8019892
  simp only [CollatzResearch.WordTrace]
  refine ⟨146254745930654223676118965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195006327907538964901491953 146254745930654223676118965)
  ·
    refine ⟨13711382430998833469636153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146254745930654223676118965 13711382430998833469636153)
    ·
      refine ⟨10283536823249125102227115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13711382430998833469636153 10283536823249125102227115)
      ·
        refine ⟨15425305234873687653340673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283536823249125102227115 15425305234873687653340673)
        ·
          refine ⟨11568978926155265740005505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15425305234873687653340673 11568978926155265740005505)
          ·
            refine ⟨8676734194616449305004129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11568978926155265740005505 8676734194616449305004129)
            ·
              refine ⟨6507550645962336978753097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8676734194616449305004129 6507550645962336978753097)
              ·
                refine ⟨4880662984471752734064823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6507550645962336978753097 4880662984471752734064823)
                ·
                  refine ⟨7320994476707629101097235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880662984471752734064823 7320994476707629101097235)
                  ·
                    refine ⟨10981491715061443651645853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7320994476707629101097235 10981491715061443651645853)
                    ·
                      refine ⟨4118059393148041369367195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981491715061443651645853 4118059393148041369367195)
                      ·
                        rfl

theorem cell23_8019892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_8019892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019892 prefixEnd_8019892 := by exact prefixLift 8019892
  have htrace : WordTrace (prefixWord ++ tailWord_8019892) baseStart_8019892 baseEnd_8019892 := by
    simpa [prefixWord, tailWord_8019892, baseEnd_8019892] using wordTrace_append hprefix tailTrace_8019892
  have hstable : (prefixWord ++ tailWord_8019892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019892).length < 2 ^ (prefixWord ++ tailWord_8019892).sum := by decide
  have hdescent : baseEnd_8019892 < baseStart_8019892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019914 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_8019914 : Nat := 118140960795 + 8019914 * 2 ^ 59
def prefixEnd_8019914 : Nat := 4983230072969 + 3 ^ 40 * 8019914 * 2
def baseEnd_8019914 : Nat := 4118070689722440283292093

theorem tailTrace_8019914 : CollatzResearch.WordTrace tailWord_8019914 prefixEnd_8019914 4118070689722440283292093 := by
  unfold tailWord_8019914
  simp only [CollatzResearch.WordTrace]
  refine ⟨73127573566807186277384699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195006862844819163406359197 73127573566807186277384699)
  ·
    refine ⟨109691360350210779416077049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73127573566807186277384699 109691360350210779416077049)
    ·
      refine ⟨82268520262658084562057787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109691360350210779416077049 82268520262658084562057787)
      ·
        refine ⟨123402780393987126843086681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82268520262658084562057787 123402780393987126843086681)
        ·
          refine ⟨92552085295490345132315011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123402780393987126843086681 92552085295490345132315011)
          ·
            refine ⟨138828127943235517698472517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92552085295490345132315011 138828127943235517698472517)
            ·
              refine ⟨26030273989356659568463597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138828127943235517698472517 26030273989356659568463597)
              ·
                refine ⟨9761352746008747338173849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26030273989356659568463597 9761352746008747338173849)
                ·
                  refine ⟨7321014559506560503630387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9761352746008747338173849 7321014559506560503630387)
                  ·
                    refine ⟨10981521839259840755445581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321014559506560503630387 10981521839259840755445581)
                    ·
                      refine ⟨4118070689722440283292093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981521839259840755445581 4118070689722440283292093)
                      ·
                        rfl

theorem cell23_8019914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_8019914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019914 prefixEnd_8019914 := by exact prefixLift 8019914
  have htrace : WordTrace (prefixWord ++ tailWord_8019914) baseStart_8019914 baseEnd_8019914 := by
    simpa [prefixWord, tailWord_8019914, baseEnd_8019914] using wordTrace_append hprefix tailTrace_8019914
  have hstable : (prefixWord ++ tailWord_8019914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019914).length < 2 ^ (prefixWord ++ tailWord_8019914).sum := by decide
  have hdescent : baseEnd_8019914 < baseStart_8019914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019924 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_8019924 : Nat := 118140960795 + 8019924 * 2 ^ 59
def prefixEnd_8019924 : Nat := 4983230072969 + 3 ^ 40 * 8019924 * 2
def baseEnd_8019924 : Nat := 4118075824528985244167047

theorem tailTrace_8019924 : CollatzResearch.WordTrace tailWord_8019924 prefixEnd_8019924 4118075824528985244167047 := by
  unfold tailWord_8019924
  simp only [CollatzResearch.WordTrace]
  refine ⟨146255329498596258408701413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195007105998128344544935217 146255329498596258408701413)
  ·
    refine ⟨27422874280986798451631515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146255329498596258408701413 27422874280986798451631515)
    ·
      refine ⟨41134311421480197677447273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27422874280986798451631515 41134311421480197677447273)
      ·
        refine ⟨30850733566110148258085455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41134311421480197677447273 30850733566110148258085455)
        ·
          refine ⟨46276100349165222387128183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30850733566110148258085455 46276100349165222387128183)
          ·
            refine ⟨69414150523747833580692275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46276100349165222387128183 69414150523747833580692275)
            ·
              refine ⟨104121225785621750371038413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69414150523747833580692275 104121225785621750371038413)
              ·
                refine ⟨39045459669608156389139405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104121225785621750371038413 39045459669608156389139405)
                ·
                  refine ⟨14642047376103058645927277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39045459669608156389139405 14642047376103058645927277)
                  ·
                    refine ⟨5490767766038646992222729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14642047376103058645927277 5490767766038646992222729)
                    ·
                      refine ⟨4118075824528985244167047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5490767766038646992222729 4118075824528985244167047)
                      ·
                        rfl

theorem cell23_8019924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_8019924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019924 prefixEnd_8019924 := by exact prefixLift 8019924
  have htrace : WordTrace (prefixWord ++ tailWord_8019924) baseStart_8019924 baseEnd_8019924 := by
    simpa [prefixWord, tailWord_8019924, baseEnd_8019924] using wordTrace_append hprefix tailTrace_8019924
  have hstable : (prefixWord ++ tailWord_8019924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019924).length < 2 ^ (prefixWord ++ tailWord_8019924).sum := by decide
  have hdescent : baseEnd_8019924 < baseStart_8019924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019932 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_8019932 : Nat := 118140960795 + 8019932 * 2 ^ 59
def prefixEnd_8019932 : Nat := 4983230072969 + 3 ^ 40 * 8019932 * 2
def baseEnd_8019932 : Nat := 4118079932374221212867011

theorem tailTrace_8019932 : CollatzResearch.WordTrace tailWord_8019932 prefixEnd_8019932 4118079932374221212867011 := by
  unfold tailWord_8019932
  simp only [CollatzResearch.WordTrace]
  refine ⟨146255475390581767091847025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195007300520775689455796033 146255475390581767091847025)
  ·
    refine ⟨109691606542936325318885269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146255475390581767091847025 109691606542936325318885269)
    ·
      refine ⟨5141794056700140249322747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109691606542936325318885269 5141794056700140249322747)
      ·
        refine ⟨7712691085050210373984121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141794056700140249322747 7712691085050210373984121)
        ·
          refine ⟨5784518313787657780488091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7712691085050210373984121 5784518313787657780488091)
          ·
            refine ⟨8676777470681486670732137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784518313787657780488091 8676777470681486670732137)
            ·
              refine ⟨6507583103011115003049103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8676777470681486670732137 6507583103011115003049103)
              ·
                refine ⟨9761374654516672504573655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507583103011115003049103 9761374654516672504573655)
                ·
                  refine ⟨14642061981775008756860483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9761374654516672504573655 14642061981775008756860483)
                  ·
                    refine ⟨21963092972662513135290725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14642061981775008756860483 21963092972662513135290725)
                    ·
                      refine ⟨4118079932374221212867011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21963092972662513135290725 4118079932374221212867011)
                      ·
                        rfl

theorem cell23_8019932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_8019932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019932 prefixEnd_8019932 := by exact prefixLift 8019932
  have htrace : WordTrace (prefixWord ++ tailWord_8019932) baseStart_8019932 baseEnd_8019932 := by
    simpa [prefixWord, tailWord_8019932, baseEnd_8019932] using wordTrace_append hprefix tailTrace_8019932
  have hstable : (prefixWord ++ tailWord_8019932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019932).length < 2 ^ (prefixWord ++ tailWord_8019932).sum := by decide
  have hdescent : baseEnd_8019932 < baseStart_8019932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019940 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_8019940 : Nat := 118140960795 + 8019940 * 2 ^ 59
def prefixEnd_8019940 : Nat := 4983230072969 + 3 ^ 40 * 8019940 * 2
def baseEnd_8019940 : Nat := 4118084040219457181566973

theorem tailTrace_8019940 : CollatzResearch.WordTrace tailWord_8019940 prefixEnd_8019940 4118084040219457181566973 := by
  unfold tailWord_8019940
  simp only [CollatzResearch.WordTrace]
  refine ⟨146255621282567275774992637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195007495043423034366656849 146255621282567275774992637)
  ·
    refine ⟨54845857980962728415622239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146255621282567275774992637 54845857980962728415622239)
    ·
      refine ⟨82268786971444092623433359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54845857980962728415622239 82268786971444092623433359)
      ·
        refine ⟨123403180457166138935150039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82268786971444092623433359 123403180457166138935150039)
        ·
          refine ⟨185104770685749208402725059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123403180457166138935150039 185104770685749208402725059)
          ·
            refine ⟨277657156028623812604087589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185104770685749208402725059 277657156028623812604087589)
            ·
              refine ⟨52060716755366964863266423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277657156028623812604087589 52060716755366964863266423)
              ·
                refine ⟨78091075133050447294899635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52060716755366964863266423 78091075133050447294899635)
                ·
                  refine ⟨117136612699575670942349453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78091075133050447294899635 117136612699575670942349453)
                  ·
                    refine ⟨43926229762340876603381045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117136612699575670942349453 43926229762340876603381045)
                    ·
                      refine ⟨4118084040219457181566973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43926229762340876603381045 4118084040219457181566973)
                      ·
                        rfl

theorem cell23_8019940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_8019940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019940 prefixEnd_8019940 := by exact prefixLift 8019940
  have htrace : WordTrace (prefixWord ++ tailWord_8019940) baseStart_8019940 baseEnd_8019940 := by
    simpa [prefixWord, tailWord_8019940, baseEnd_8019940] using wordTrace_append hprefix tailTrace_8019940
  have hstable : (prefixWord ++ tailWord_8019940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019940).length < 2 ^ (prefixWord ++ tailWord_8019940).sum := by decide
  have hdescent : baseEnd_8019940 < baseStart_8019940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019960 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 7]
def baseStart_8019960 : Nat := 118140960795 + 8019960 * 2 ^ 59
def prefixEnd_8019960 : Nat := 4983230072969 + 3 ^ 40 * 8019960 * 2
def baseEnd_8019960 : Nat := 457566034425838567035209

theorem tailTrace_8019960 : CollatzResearch.WordTrace tailWord_8019960 prefixEnd_8019960 457566034425838567035209 := by
  unfold tailWord_8019960
  simp only [CollatzResearch.WordTrace]
  refine ⟨146255986012531047482856667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195007981350041396643808889 146255986012531047482856667)
  ·
    refine ⟨219383979018796571224285001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146255986012531047482856667 219383979018796571224285001)
    ·
      refine ⟨164537984264097428418213751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219383979018796571224285001 164537984264097428418213751)
      ·
        refine ⟨246806976396146142627320627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164537984264097428418213751 246806976396146142627320627)
        ·
          refine ⟨370210464594219213940980941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246806976396146142627320627 370210464594219213940980941)
          ·
            refine ⟨138828924222832205227867853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370210464594219213940980941 138828924222832205227867853)
            ·
              refine ⟨52060846583562076960450445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138828924222832205227867853 52060846583562076960450445)
              ·
                refine ⟨19522817468835778860168917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52060846583562076960450445 19522817468835778860168917)
                ·
                  refine ⟨457566034425838567035209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19522817468835778860168917 457566034425838567035209)
                  ·
                    rfl

theorem cell23_8019960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 7].length) (baseStart_8019960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019960 prefixEnd_8019960 := by exact prefixLift 8019960
  have htrace : WordTrace (prefixWord ++ tailWord_8019960) baseStart_8019960 baseEnd_8019960 := by
    simpa [prefixWord, tailWord_8019960, baseEnd_8019960] using wordTrace_append hprefix tailTrace_8019960
  have hstable : (prefixWord ++ tailWord_8019960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019960).length < 2 ^ (prefixWord ++ tailWord_8019960).sum := by decide
  have hdescent : baseEnd_8019960 < baseStart_8019960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8019994 : List Nat := [3, 1, 1, 3, 1, 3, 3, 3, 5]
def baseStart_8019994 : Nat := 118140960795 + 8019994 * 2 ^ 59
def prefixEnd_8019994 : Nat := 4983230072969 + 3 ^ 40 * 8019994 * 2
def baseEnd_8019994 : Nat := 457567974241644441143525

theorem tailTrace_8019994 : CollatzResearch.WordTrace tailWord_8019994 prefixEnd_8019994 457567974241644441143525 := by
  unfold tailWord_8019994
  simp only [CollatzResearch.WordTrace]
  refine ⟨73128303026734729693112759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195008808071292612514967357 73128303026734729693112759)
  ·
    refine ⟨109692454540102094539669139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73128303026734729693112759 109692454540102094539669139)
    ·
      refine ⟨164538681810153141809503709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109692454540102094539669139 164538681810153141809503709)
      ·
        refine ⟨61702005678807428178563891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164538681810153141809503709 61702005678807428178563891)
        ·
          refine ⟨92553008518211142267845837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61702005678807428178563891 92553008518211142267845837)
          ·
            refine ⟨34707378194329178350442189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92553008518211142267845837 34707378194329178350442189)
            ·
              refine ⟨13015266822873441881415821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34707378194329178350442189 13015266822873441881415821)
              ·
                refine ⟨4880725058577540705530933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13015266822873441881415821 4880725058577540705530933)
                ·
                  refine ⟨457567974241644441143525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4880725058577540705530933 457567974241644441143525)
                  ·
                    rfl

theorem cell23_8019994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_8019994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8019994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8019994 prefixEnd_8019994 := by exact prefixLift 8019994
  have htrace : WordTrace (prefixWord ++ tailWord_8019994) baseStart_8019994 baseEnd_8019994 := by
    simpa [prefixWord, tailWord_8019994, baseEnd_8019994] using wordTrace_append hprefix tailTrace_8019994
  have hstable : (prefixWord ++ tailWord_8019994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8019994).length < 2 ^ (prefixWord ++ tailWord_8019994).sum := by decide
  have hdescent : baseEnd_8019994 < baseStart_8019994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8019994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020017 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_8020017 : Nat := 118140960795 + 8020017 * 2 ^ 59
def prefixEnd_8020017 : Nat := 4983230072969 + 3 ^ 40 * 8020017 * 2
def baseEnd_8020017 : Nat := 4118123578229853380304119

theorem tailTrace_8020017 : CollatzResearch.WordTrace tailWord_8020017 prefixEnd_8020017 4118123578229853380304119 := by
  unfold tailWord_8020017
  simp only [CollatzResearch.WordTrace]
  refine ⟨292514050985855593700538305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195009367323903729133692203 292514050985855593700538305)
  ·
    refine ⟨219385538239391695275403729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292514050985855593700538305 219385538239391695275403729)
    ·
      refine ⟨164539153679543771456552797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219385538239391695275403729 164539153679543771456552797)
      ·
        refine ⟨61702182629828914296207299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164539153679543771456552797 61702182629828914296207299)
        ·
          refine ⟨92553273944743371444310949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61702182629828914296207299 92553273944743371444310949)
          ·
            refine ⟨17353738864639382145808303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92553273944743371444310949 17353738864639382145808303)
            ·
              refine ⟨26030608296959073218712455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17353738864639382145808303 26030608296959073218712455)
              ·
                refine ⟨39045912445438609828068683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26030608296959073218712455 39045912445438609828068683)
                ·
                  refine ⟨58568868668157914742103025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39045912445438609828068683 58568868668157914742103025)
                  ·
                    refine ⟨43926651501118436056577269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58568868668157914742103025 43926651501118436056577269)
                    ·
                      refine ⟨4118123578229853380304119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43926651501118436056577269 4118123578229853380304119)
                      ·
                        rfl

theorem cell23_8020017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_8020017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020017 prefixEnd_8020017 := by exact prefixLift 8020017
  have htrace : WordTrace (prefixWord ++ tailWord_8020017) baseStart_8020017 baseEnd_8020017 := by
    simpa [prefixWord, tailWord_8020017, baseEnd_8020017] using wordTrace_append hprefix tailTrace_8020017
  have hstable : (prefixWord ++ tailWord_8020017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020017).length < 2 ^ (prefixWord ++ tailWord_8020017).sum := by decide
  have hdescent : baseEnd_8020017 < baseStart_8020017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020037 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_8020037 : Nat := 118140960795 + 8020037 * 2 ^ 59
def prefixEnd_8020037 : Nat := 4983230072969 + 3 ^ 40 * 8020037 * 2
def baseEnd_8020037 : Nat := 1372711282614314434018009

theorem tailTrace_8020037 : CollatzResearch.WordTrace tailWord_8020037 prefixEnd_8020037 1372711282614314434018009 := by
  unfold tailWord_8020037
  simp only [CollatzResearch.WordTrace]
  refine ⟨292514780445783137116266365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195009853630522091410844243 292514780445783137116266365)
  ·
    refine ⟨109693042667168676418599887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292514780445783137116266365 109693042667168676418599887)
    ·
      refine ⟨164539564000753014627899831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109693042667168676418599887 164539564000753014627899831)
      ·
        refine ⟨246809346001129521941849747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164539564000753014627899831 246809346001129521941849747)
        ·
          refine ⟨370214019001694282912774621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246809346001129521941849747 370214019001694282912774621)
          ·
            refine ⟨138830257125635356092290483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370214019001694282912774621 138830257125635356092290483)
            ·
              refine ⟨208245385688453034138435725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138830257125635356092290483 208245385688453034138435725)
              ·
                refine ⟨78092019633169887801913397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208245385688453034138435725 78092019633169887801913397)
                ·
                  refine ⟨7321126840609676981429381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78092019633169887801913397 7321126840609676981429381)
                  ·
                    refine ⟨1372711282614314434018009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7321126840609676981429381 1372711282614314434018009)
                    ·
                      rfl

theorem cell23_8020037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_8020037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020037 prefixEnd_8020037 := by exact prefixLift 8020037
  have htrace : WordTrace (prefixWord ++ tailWord_8020037) baseStart_8020037 baseEnd_8020037 := by
    simpa [prefixWord, tailWord_8020037, baseEnd_8020037] using wordTrace_append hprefix tailTrace_8020037
  have hstable : (prefixWord ++ tailWord_8020037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020037).length < 2 ^ (prefixWord ++ tailWord_8020037).sum := by decide
  have hdescent : baseEnd_8020037 < baseStart_8020037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020047 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 3]
def baseStart_8020047 : Nat := 118140960795 + 8020047 * 2 ^ 59
def prefixEnd_8020047 : Nat := 4983230072969 + 3 ^ 40 * 8020047 * 2
def baseEnd_8020047 : Nat := 4118138982649488262928981

theorem tailTrace_8020047 : CollatzResearch.WordTrace tailWord_8020047 prefixEnd_8020047 4118138982649488262928981 := by
  unfold tailWord_8020047
  simp only [CollatzResearch.WordTrace]
  refine ⟨292515145175746908824130395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195010096783831272549420263 292515145175746908824130395)
  ·
    refine ⟨438772717763620363236195593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292515145175746908824130395 438772717763620363236195593)
    ·
      refine ⟨329079538322715272427146695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438772717763620363236195593 329079538322715272427146695)
      ·
        refine ⟨493619307484072908640720043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329079538322715272427146695 493619307484072908640720043)
        ·
          refine ⟨740428961226109362961080065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493619307484072908640720043 740428961226109362961080065)
          ·
            refine ⟨555321720919582022220810049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740428961226109362961080065 555321720919582022220810049)
            ·
              refine ⟨416491290689686516665607537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555321720919582022220810049 416491290689686516665607537)
              ·
                refine ⟨312368468017264887499205653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416491290689686516665607537 312368468017264887499205653)
                ·
                  refine ⟨14642271938309291601525265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312368468017264887499205653 14642271938309291601525265)
                  ·
                    refine ⟨10981703953731968701143949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14642271938309291601525265 10981703953731968701143949)
                    ·
                      refine ⟨4118138982649488262928981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981703953731968701143949 4118138982649488262928981)
                      ·
                        rfl

theorem cell23_8020047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_8020047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020047 prefixEnd_8020047 := by exact prefixLift 8020047
  have htrace : WordTrace (prefixWord ++ tailWord_8020047) baseStart_8020047 baseEnd_8020047 := by
    simpa [prefixWord, tailWord_8020047, baseEnd_8020047] using wordTrace_append hprefix tailTrace_8020047
  have hstable : (prefixWord ++ tailWord_8020047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020047).length < 2 ^ (prefixWord ++ tailWord_8020047).sum := by decide
  have hdescent : baseEnd_8020047 < baseStart_8020047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020061 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_8020061 : Nat := 118140960795 + 8020061 * 2 ^ 59
def prefixEnd_8020061 : Nat := 4983230072969 + 3 ^ 40 * 8020061 * 2
def baseEnd_8020061 : Nat := 4118146171378651208153917

theorem tailTrace_8020061 : CollatzResearch.WordTrace tailWord_8020061 prefixEnd_8020061 4118146171378651208153917 := by
  unfold tailWord_8020061
  simp only [CollatzResearch.WordTrace]
  refine ⟨292515655797696189215140037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195010437198464126143426691 292515655797696189215140037)
  ·
    refine ⟨54846685462068035477838757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292515655797696189215140037 54846685462068035477838757)
    ·
      refine ⟨10283753524137756652094767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54846685462068035477838757 10283753524137756652094767)
      ·
        refine ⟨15425630286206634978142151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283753524137756652094767 15425630286206634978142151)
        ·
          refine ⟨23138445429309952467213227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15425630286206634978142151 23138445429309952467213227)
          ·
            refine ⟨34707668143964928700819841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23138445429309952467213227 34707668143964928700819841)
            ·
              refine ⟨26030751107973696525614881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34707668143964928700819841 26030751107973696525614881)
              ·
                refine ⟨19523063330980272394211161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26030751107973696525614881 19523063330980272394211161)
                ·
                  refine ⟨14642297498235204295658371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19523063330980272394211161 14642297498235204295658371)
                  ·
                    refine ⟨21963446247352806443487557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14642297498235204295658371 21963446247352806443487557)
                    ·
                      refine ⟨4118146171378651208153917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21963446247352806443487557 4118146171378651208153917)
                      ·
                        rfl

theorem cell23_8020061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_8020061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020061 prefixEnd_8020061 := by exact prefixLift 8020061
  have htrace : WordTrace (prefixWord ++ tailWord_8020061) baseStart_8020061 baseEnd_8020061 := by
    simpa [prefixWord, tailWord_8020061, baseEnd_8020061] using wordTrace_append hprefix tailTrace_8020061
  have hstable : (prefixWord ++ tailWord_8020061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020061).length < 2 ^ (prefixWord ++ tailWord_8020061).sum := by decide
  have hdescent : baseEnd_8020061 < baseStart_8020061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020062 : List Nat := [4, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_8020062 : Nat := 118140960795 + 8020062 * 2 ^ 59
def prefixEnd_8020062 : Nat := 4983230072969 + 3 ^ 40 * 8020062 * 2
def baseEnd_8020062 : Nat := 457571853873256189360157

theorem tailTrace_8020062 : CollatzResearch.WordTrace tailWord_8020062 prefixEnd_8020062 457571853873256189360157 := by
  unfold tailWord_8020062
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564461533836570798240805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195010461513795044257284293 36564461533836570798240805)
  ·
    refine ⟨6855836537594357024670151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36564461533836570798240805 6855836537594357024670151)
    ·
      refine ⟨10283754806391535537005227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6855836537594357024670151 10283754806391535537005227)
      ·
        refine ⟨15425632209587303305507841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283754806391535537005227 15425632209587303305507841)
        ·
          refine ⟨11569224157190477479130881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15425632209587303305507841 11569224157190477479130881)
          ·
            refine ⟨8676918117892858109348161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11569224157190477479130881 8676918117892858109348161)
            ·
              refine ⟨6507688588419643582011121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8676918117892858109348161 6507688588419643582011121)
              ·
                refine ⟨4880766441314732686508341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6507688588419643582011121 4880766441314732686508341)
                ·
                  refine ⟨457571853873256189360157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4880766441314732686508341 457571853873256189360157)
                  ·
                    rfl

theorem cell23_8020062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_8020062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020062 prefixEnd_8020062 := by exact prefixLift 8020062
  have htrace : WordTrace (prefixWord ++ tailWord_8020062) baseStart_8020062 baseEnd_8020062 := by
    simpa [prefixWord, tailWord_8020062, baseEnd_8020062] using wordTrace_append hprefix tailTrace_8020062
  have hstable : (prefixWord ++ tailWord_8020062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020062).length < 2 ^ (prefixWord ++ tailWord_8020062).sum := by decide
  have hdescent : baseEnd_8020062 < baseStart_8020062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020064 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3]
def baseStart_8020064 : Nat := 118140960795 + 8020064 * 2 ^ 59
def prefixEnd_8020064 : Nat := 4983230072969 + 3 ^ 40 * 8020064 * 2
def baseEnd_8020064 : Nat := 4118147711820614696416403

theorem tailTrace_8020064 : CollatzResearch.WordTrace tailWord_8020064 prefixEnd_8020064 4118147711820614696416403 := by
  unfold tailWord_8020064
  simp only [CollatzResearch.WordTrace]
  refine ⟨146257882608342660363749623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195010510144456880484999497 146257882608342660363749623)
  ·
    refine ⟨219386823912513990545624435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146257882608342660363749623 219386823912513990545624435)
    ·
      refine ⟨329080235868770985818436653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219386823912513990545624435 329080235868770985818436653)
      ·
        refine ⟨123405088450789119681913745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329080235868770985818436653 123405088450789119681913745)
        ·
          refine ⟨92553816338091839761435309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123405088450789119681913745 92553816338091839761435309)
          ·
            refine ⟨34707681126784439910538241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92553816338091839761435309 34707681126784439910538241)
            ·
              refine ⟨26030760845088329932903681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34707681126784439910538241 26030760845088329932903681)
              ·
                refine ⟨19523070633816247449677761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26030760845088329932903681 19523070633816247449677761)
                ·
                  refine ⟨14642302975362185587258321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19523070633816247449677761 14642302975362185587258321)
                  ·
                    refine ⟨10981727231521639190443741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14642302975362185587258321 10981727231521639190443741)
                    ·
                      refine ⟨4118147711820614696416403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981727231521639190443741 4118147711820614696416403)
                      ·
                        rfl

theorem cell23_8020064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_8020064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020064 prefixEnd_8020064 := by exact prefixLift 8020064
  have htrace : WordTrace (prefixWord ++ tailWord_8020064) baseStart_8020064 baseEnd_8020064 := by
    simpa [prefixWord, tailWord_8020064, baseEnd_8020064] using wordTrace_append hprefix tailTrace_8020064
  have hstable : (prefixWord ++ tailWord_8020064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020064).length < 2 ^ (prefixWord ++ tailWord_8020064).sum := by decide
  have hdescent : baseEnd_8020064 < baseStart_8020064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020067 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 6]
def baseStart_8020067 : Nat := 118140960795 + 8020067 * 2 ^ 59
def prefixEnd_8020067 : Nat := 4983230072969 + 3 ^ 40 * 8020067 * 2
def baseEnd_8020067 : Nat := 457572139140286464964321

theorem tailTrace_8020067 : CollatzResearch.WordTrace tailWord_8020067 prefixEnd_8020067 457572139140286464964321 := by
  unfold tailWord_8020067
  simp only [CollatzResearch.WordTrace]
  refine ⟨292515874635674452239858455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195010583090449634826572303 292515874635674452239858455)
  ·
    refine ⟨438773811953511678359787683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292515874635674452239858455 438773811953511678359787683)
    ·
      refine ⟨658160717930267517539681525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438773811953511678359787683 658160717930267517539681525)
      ·
        refine ⟨61702567305962579769345143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 658160717930267517539681525 61702567305962579769345143)
        ·
          refine ⟨92553850958943869654017715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61702567305962579769345143 92553850958943869654017715)
          ·
            refine ⟨138830776438415804481026573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92553850958943869654017715 138830776438415804481026573)
            ·
              refine ⟨52061541164405926680384965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138830776438415804481026573 52061541164405926680384965)
              ·
                refine ⟨9761538968326111252572181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52061541164405926680384965 9761538968326111252572181)
                ·
                  refine ⟨457572139140286464964321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9761538968326111252572181 457572139140286464964321)
                  ·
                    rfl

theorem cell23_8020067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 6].length) (baseStart_8020067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020067 prefixEnd_8020067 := by exact prefixLift 8020067
  have htrace : WordTrace (prefixWord ++ tailWord_8020067) baseStart_8020067 baseEnd_8020067 := by
    simpa [prefixWord, tailWord_8020067, baseEnd_8020067] using wordTrace_append hprefix tailTrace_8020067
  have hstable : (prefixWord ++ tailWord_8020067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020067).length < 2 ^ (prefixWord ++ tailWord_8020067).sum := by decide
  have hdescent : baseEnd_8020067 < baseStart_8020067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020071 : List Nat := [1, 1, 5, 1, 1, 2, 3, 4, 1, 4]
def baseStart_8020071 : Nat := 118140960795 + 8020071 * 2 ^ 59
def prefixEnd_8020071 : Nat := 4983230072969 + 3 ^ 40 * 8020071 * 2
def baseEnd_8020071 : Nat := 1372717102061732056342957

theorem tailTrace_8020071 : CollatzResearch.WordTrace tailWord_8020071 prefixEnd_8020071 1372717102061732056342957 := by
  unfold tailWord_8020071
  simp only [CollatzResearch.WordTrace]
  refine ⟨292516020527659960923004067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195010680351773307282002711 292516020527659960923004067)
  ·
    refine ⟨438774030791489941384506101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292516020527659960923004067 438774030791489941384506101)
    ·
      refine ⟨41135065386702182004797447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438774030791489941384506101 41135065386702182004797447)
      ·
        refine ⟨61702598080053273007196171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41135065386702182004797447 61702598080053273007196171)
        ·
          refine ⟨92553897120079909510794257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61702598080053273007196171 92553897120079909510794257)
          ·
            refine ⟨69415422840059932133095693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92553897120079909510794257 69415422840059932133095693)
            ·
              refine ⟨26030783565022474549910885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69415422840059932133095693 26030783565022474549910885)
              ·
                refine ⟨4880771918441713978108291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26030783565022474549910885 4880771918441713978108291)
                ·
                  refine ⟨7321157877662570967162437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880771918441713978108291 7321157877662570967162437)
                  ·
                    refine ⟨1372717102061732056342957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7321157877662570967162437 1372717102061732056342957)
                    ·
                      rfl

theorem cell23_8020071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_8020071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020071 prefixEnd_8020071 := by exact prefixLift 8020071
  have htrace : WordTrace (prefixWord ++ tailWord_8020071) baseStart_8020071 baseEnd_8020071 := by
    simpa [prefixWord, tailWord_8020071, baseEnd_8020071] using wordTrace_append hprefix tailTrace_8020071
  have hstable : (prefixWord ++ tailWord_8020071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020071).length < 2 ^ (prefixWord ++ tailWord_8020071).sum := by decide
  have hdescent : baseEnd_8020071 < baseStart_8020071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020128 : List Nat := [2, 1, 1, 4, 2, 2, 2, 4, 1, 1, 3]
def baseStart_8020128 : Nat := 118140960795 + 8020128 * 2 ^ 59
def prefixEnd_8020128 : Nat := 4983230072969 + 3 ^ 40 * 8020128 * 2
def baseEnd_8020128 : Nat := 4118180574582502446016109

theorem tailTrace_8020128 : CollatzResearch.WordTrace tailWord_8020128 prefixEnd_8020128 4118180574582502446016109 := by
  unfold tailWord_8020128
  simp only [CollatzResearch.WordTrace]
  refine ⟨146259049744226729828914519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195012066325635639771886025 146259049744226729828914519)
  ·
    refine ⟨219388574616340094743371779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146259049744226729828914519 219388574616340094743371779)
    ·
      refine ⟨329082861924510142115057669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219388574616340094743371779 329082861924510142115057669)
      ·
        refine ⟨61703036610845651646573313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329082861924510142115057669 61703036610845651646573313)
        ·
          refine ⟨46277277458134238734929985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61703036610845651646573313 46277277458134238734929985)
          ·
            refine ⟨34707958093600679051197489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46277277458134238734929985 34707958093600679051197489)
            ·
              refine ⟨26030968570200509288398117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34707958093600679051197489 26030968570200509288398117)
              ·
                refine ⟨4880806606912595491574647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26030968570200509288398117 4880806606912595491574647)
                ·
                  refine ⟨7321209910368893237361971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880806606912595491574647 7321209910368893237361971)
                  ·
                    refine ⟨10981814865553339856042957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321209910368893237361971 10981814865553339856042957)
                    ·
                      refine ⟨4118180574582502446016109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981814865553339856042957 4118180574582502446016109)
                      ·
                        rfl

theorem cell23_8020128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_8020128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020128 prefixEnd_8020128 := by exact prefixLift 8020128
  have htrace : WordTrace (prefixWord ++ tailWord_8020128) baseStart_8020128 baseEnd_8020128 := by
    simpa [prefixWord, tailWord_8020128, baseEnd_8020128] using wordTrace_append hprefix tailTrace_8020128
  have hstable : (prefixWord ++ tailWord_8020128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020128).length < 2 ^ (prefixWord ++ tailWord_8020128).sum := by decide
  have hdescent : baseEnd_8020128 < baseStart_8020128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020151 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_8020151 : Nat := 118140960795 + 8020151 * 2 ^ 59
def prefixEnd_8020151 : Nat := 4983230072969 + 3 ^ 40 * 8020151 * 2
def baseEnd_8020151 : Nat := 4118192384637555856028503

theorem tailTrace_8020151 : CollatzResearch.WordTrace tailWord_8020151 prefixEnd_8020151 4118192384637555856028503 := by
  unfold tailWord_8020151
  simp only [CollatzResearch.WordTrace]
  refine ⟨292518938367370134585916307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195012625578246756390610871 292518938367370134585916307)
  ·
    refine ⟨438778407551055201878874461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292518938367370134585916307 438778407551055201878874461)
    ·
      refine ⟨164541902831645700704577923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438778407551055201878874461 164541902831645700704577923)
      ·
        refine ⟨246812854247468551056866885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164541902831645700704577923 246812854247468551056866885)
        ·
          refine ⟨46277410171400353323162541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246812854247468551056866885 46277410171400353323162541)
          ·
            refine ⟨17354028814275132496185953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46277410171400353323162541 17354028814275132496185953)
            ·
              refine ⟨13015521610706349372139465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17354028814275132496185953 13015521610706349372139465)
              ·
                refine ⟨9761641208029762029104599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13015521610706349372139465 9761641208029762029104599)
                ·
                  refine ⟨14642461812044643043656899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9761641208029762029104599 14642461812044643043656899)
                  ·
                    refine ⟨21963692718066964565485349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14642461812044643043656899 21963692718066964565485349)
                    ·
                      refine ⟨4118192384637555856028503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21963692718066964565485349 4118192384637555856028503)
                      ·
                        rfl

theorem cell23_8020151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_8020151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020151 prefixEnd_8020151 := by exact prefixLift 8020151
  have htrace : WordTrace (prefixWord ++ tailWord_8020151) baseStart_8020151 baseEnd_8020151 := by
    simpa [prefixWord, tailWord_8020151, baseEnd_8020151] using wordTrace_append hprefix tailTrace_8020151
  have hstable : (prefixWord ++ tailWord_8020151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020151).length < 2 ^ (prefixWord ++ tailWord_8020151).sum := by decide
  have hdescent : baseEnd_8020151 < baseStart_8020151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020154 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_8020154 : Nat := 118140960795 + 8020154 * 2 ^ 59
def prefixEnd_8020154 : Nat := 4983230072969 + 3 ^ 40 * 8020154 * 2
def baseEnd_8020154 : Nat := 4118193925079519344290989

theorem tailTrace_8020154 : CollatzResearch.WordTrace tailWord_8020154 prefixEnd_8020154 4118193925079519344290989 := by
  unfold tailWord_8020154
  simp only [CollatzResearch.WordTrace]
  refine ⟨73129761946589816524568879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195012698524239510732183677 73129761946589816524568879)
  ·
    refine ⟨109694642919884724786853319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73129761946589816524568879 109694642919884724786853319)
    ·
      refine ⟨164541964379827087180279979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109694642919884724786853319 164541964379827087180279979)
      ·
        refine ⟨246812946569740630770419969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164541964379827087180279979 246812946569740630770419969)
        ·
          refine ⟨185109709927305473077814977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246812946569740630770419969 185109709927305473077814977)
          ·
            refine ⟨138832282445479104808361233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185109709927305473077814977 138832282445479104808361233)
            ·
              refine ⟨104124211834109328606270925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138832282445479104808361233 104124211834109328606270925)
              ·
                refine ⟨39046579437790998227351597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104124211834109328606270925 39046579437790998227351597)
                ·
                  refine ⟨14642467289171624335256849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39046579437790998227351597 14642467289171624335256849)
                  ·
                    refine ⟨10981850466878718251442637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14642467289171624335256849 10981850466878718251442637)
                    ·
                      refine ⟨4118193925079519344290989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981850466878718251442637 4118193925079519344290989)
                      ·
                        rfl

theorem cell23_8020154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_8020154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020154 prefixEnd_8020154 := by exact prefixLift 8020154
  have htrace : WordTrace (prefixWord ++ tailWord_8020154) baseStart_8020154 baseEnd_8020154 := by
    simpa [prefixWord, tailWord_8020154, baseEnd_8020154] using wordTrace_append hprefix tailTrace_8020154
  have hstable : (prefixWord ++ tailWord_8020154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020154).length < 2 ^ (prefixWord ++ tailWord_8020154).sum := by decide
  have hdescent : baseEnd_8020154 < baseStart_8020154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020174 : List Nat := [4, 1, 1, 1, 4, 3, 9]
def baseStart_8020174 : Nat := 118140960795 + 8020174 * 2 ^ 59
def prefixEnd_8020174 : Nat := 4983230072969 + 3 ^ 40 * 8020174 * 2
def baseEnd_8020174 : Nat := 50842027094970484765937

theorem tailTrace_8020174 : CollatzResearch.WordTrace tailWord_8020174 prefixEnd_8020174 50842027094970484765937 := by
  unfold tailWord_8020174
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564972155785851189250447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195013184830857873009335717 36564972155785851189250447)
  ·
    refine ⟨54847458233678776783875671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36564972155785851189250447 54847458233678776783875671)
    ·
      refine ⟨82271187350518165175813507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54847458233678776783875671 82271187350518165175813507)
      ·
        refine ⟨123406781025777247763720261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82271187350518165175813507 123406781025777247763720261)
        ·
          refine ⟨23138771442333233955697549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123406781025777247763720261 23138771442333233955697549)
          ·
            refine ⟨8677039290874962733386581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23138771442333233955697549 8677039290874962733386581)
            ·
              refine ⟨50842027094970484765937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8677039290874962733386581 50842027094970484765937)
              ·
                rfl

theorem cell23_8020174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 9].length) (baseStart_8020174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020174 prefixEnd_8020174 := by exact prefixLift 8020174
  have htrace : WordTrace (prefixWord ++ tailWord_8020174) baseStart_8020174 baseEnd_8020174 := by
    simpa [prefixWord, tailWord_8020174, baseEnd_8020174] using wordTrace_append hprefix tailTrace_8020174
  have hstable : (prefixWord ++ tailWord_8020174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020174).length < 2 ^ (prefixWord ++ tailWord_8020174).sum := by decide
  have hdescent : baseEnd_8020174 < baseStart_8020174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020201 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 3]
def baseStart_8020201 : Nat := 118140960795 + 8020201 * 2 ^ 59
def prefixEnd_8020201 : Nat := 4983230072969 + 3 ^ 40 * 8020201 * 2
def baseEnd_8020201 : Nat := 4118218058670280660403273

theorem tailTrace_8020201 : CollatzResearch.WordTrace tailWord_8020201 prefixEnd_8020201 4118218058670280660403273 := by
  unfold tailWord_8020201
  simp only [CollatzResearch.WordTrace]
  refine ⟨292520762017188993125236457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195013841344792662083490971 292520762017188993125236457)
  ·
    refine ⟨219390571512891744843927343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292520762017188993125236457 219390571512891744843927343)
    ·
      refine ⟨329085857269337617265891015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219390571512891744843927343 329085857269337617265891015)
      ·
        refine ⟨493628785904006425898836523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329085857269337617265891015 493628785904006425898836523)
        ·
          refine ⟨740443178856009638848254785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493628785904006425898836523 740443178856009638848254785)
          ·
            refine ⟨555332384142007229136191089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740443178856009638848254785 555332384142007229136191089)
            ·
              refine ⟨416499288106505421852143317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555332384142007229136191089 416499288106505421852143317)
              ·
                refine ⟨9761702064996220824659609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 416499288106505421852143317 9761702064996220824659609)
                ·
                  refine ⟨7321276548747165618494707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9761702064996220824659609 7321276548747165618494707)
                  ·
                    refine ⟨10981914823120748427742061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321276548747165618494707 10981914823120748427742061)
                    ·
                      refine ⟨4118218058670280660403273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981914823120748427742061 4118218058670280660403273)
                      ·
                        rfl

theorem cell23_8020201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 3].length) (baseStart_8020201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020201 prefixEnd_8020201 := by exact prefixLift 8020201
  have htrace : WordTrace (prefixWord ++ tailWord_8020201) baseStart_8020201 baseEnd_8020201 := by
    simpa [prefixWord, tailWord_8020201, baseEnd_8020201] using wordTrace_append hprefix tailTrace_8020201
  have hstable : (prefixWord ++ tailWord_8020201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020201).length < 2 ^ (prefixWord ++ tailWord_8020201).sum := by decide
  have hdescent : baseEnd_8020201 < baseStart_8020201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020205 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_8020205 : Nat := 118140960795 + 8020205 * 2 ^ 59
def prefixEnd_8020205 : Nat := 4983230072969 + 3 ^ 40 * 8020205 * 2
def baseEnd_8020205 : Nat := 4118220112592898644753255

theorem tailTrace_8020205 : CollatzResearch.WordTrace tailWord_8020205 prefixEnd_8020205 4118220112592898644753255 := by
  unfold tailWord_8020205
  simp only [CollatzResearch.WordTrace]
  refine ⟨292520907909174501808382069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195013938606116334538921379 292520907909174501808382069)
  ·
    refine ⟨27423835116485109544535819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292520907909174501808382069 27423835116485109544535819)
    ·
      refine ⟨41135752674727664316803729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27423835116485109544535819 41135752674727664316803729)
      ·
        refine ⟨30851814506045748237602797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41135752674727664316803729 30851814506045748237602797)
        ·
          refine ⟨11569430439767155589101049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30851814506045748237602797 11569430439767155589101049)
          ·
            refine ⟨8677072829825366691825787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11569430439767155589101049 8677072829825366691825787)
            ·
              refine ⟨13015609244738050037738681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677072829825366691825787 13015609244738050037738681)
              ·
                refine ⟨9761706933553537528304011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13015609244738050037738681 9761706933553537528304011)
                ·
                  refine ⟨14642560400330306292456017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9761706933553537528304011 14642560400330306292456017)
                  ·
                    refine ⟨10981920300247729719342013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14642560400330306292456017 10981920300247729719342013)
                    ·
                      refine ⟨4118220112592898644753255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981920300247729719342013 4118220112592898644753255)
                      ·
                        rfl

theorem cell23_8020205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_8020205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020205 prefixEnd_8020205 := by exact prefixLift 8020205
  have htrace : WordTrace (prefixWord ++ tailWord_8020205) baseStart_8020205 baseEnd_8020205 := by
    simpa [prefixWord, tailWord_8020205, baseEnd_8020205] using wordTrace_append hprefix tailTrace_8020205
  have hstable : (prefixWord ++ tailWord_8020205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020205).length < 2 ^ (prefixWord ++ tailWord_8020205).sum := by decide
  have hdescent : baseEnd_8020205 < baseStart_8020205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020211 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 3, 3, 2]
def baseStart_8020211 : Nat := 118140960795 + 8020211 * 2 ^ 59
def prefixEnd_8020211 : Nat := 4983230072969 + 3 ^ 40 * 8020211 * 2
def baseEnd_8020211 : Nat := 4118223193476825621278227

theorem tailTrace_8020211 : CollatzResearch.WordTrace tailWord_8020211 prefixEnd_8020211 4118223193476825621278227 := by
  unfold tailWord_8020211
  simp only [CollatzResearch.WordTrace]
  refine ⟨292521126747152764833100487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195014084498101843222066991 292521126747152764833100487)
  ·
    refine ⟨438781690120729147249650731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292521126747152764833100487 438781690120729147249650731)
    ·
      refine ⟨658172535181093720874476097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438781690120729147249650731 658172535181093720874476097)
      ·
        refine ⟨493629401385820290655857073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658172535181093720874476097 493629401385820290655857073)
        ·
          refine ⟨370222051039365217991892805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493629401385820290655857073 370222051039365217991892805)
          ·
            refine ⟨69416634569880978373479901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370222051039365217991892805 69416634569880978373479901)
            ·
              refine ⟨26031237963705366890054963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69416634569880978373479901 26031237963705366890054963)
              ·
                refine ⟨39046856945558050335082445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26031237963705366890054963 39046856945558050335082445)
                ·
                  refine ⟨14642571354584268875655917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39046856945558050335082445 14642571354584268875655917)
                  ·
                    refine ⟨5490964257969100828370969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14642571354584268875655917 5490964257969100828370969)
                    ·
                      refine ⟨4118223193476825621278227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5490964257969100828370969 4118223193476825621278227)
                      ·
                        rfl

theorem cell23_8020211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3, 2].length) (baseStart_8020211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020211 prefixEnd_8020211 := by exact prefixLift 8020211
  have htrace : WordTrace (prefixWord ++ tailWord_8020211) baseStart_8020211 baseEnd_8020211 := by
    simpa [prefixWord, tailWord_8020211, baseEnd_8020211] using wordTrace_append hprefix tailTrace_8020211
  have hstable : (prefixWord ++ tailWord_8020211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020211).length < 2 ^ (prefixWord ++ tailWord_8020211).sum := by decide
  have hdescent : baseEnd_8020211 < baseStart_8020211 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020214 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_8020214 : Nat := 118140960795 + 8020214 * 2 ^ 59
def prefixEnd_8020214 : Nat := 4983230072969 + 3 ^ 40 * 8020214 * 2
def baseEnd_8020214 : Nat := 4118224733918789109540713

theorem tailTrace_8020214 : CollatzResearch.WordTrace tailWord_8020214 prefixEnd_8020214 4118224733918789109540713 := by
  unfold tailWord_8020214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282577260383868521591231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195014157444094597563639797 18282577260383868521591231)
  ·
    refine ⟨27423865890575802782386847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18282577260383868521591231 27423865890575802782386847)
    ·
      refine ⟨41135798835863704173580271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27423865890575802782386847 41135798835863704173580271)
      ·
        refine ⟨61703698253795556260370407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41135798835863704173580271 61703698253795556260370407)
        ·
          refine ⟨92555547380693334390555611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61703698253795556260370407 92555547380693334390555611)
          ·
            refine ⟨138833321071040001585833417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92555547380693334390555611 138833321071040001585833417)
            ·
              refine ⟨104124990803280001189375063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138833321071040001585833417 104124990803280001189375063)
              ·
                refine ⟨156187486204920001784062595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104124990803280001189375063 156187486204920001784062595)
                ·
                  refine ⟨234281229307380002676093893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156187486204920001784062595 234281229307380002676093893)
                  ·
                    refine ⟨43927730495133750501767605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234281229307380002676093893 43927730495133750501767605)
                    ·
                      refine ⟨4118224733918789109540713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43927730495133750501767605 4118224733918789109540713)
                      ·
                        rfl

theorem cell23_8020214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_8020214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020214 prefixEnd_8020214 := by exact prefixLift 8020214
  have htrace : WordTrace (prefixWord ++ tailWord_8020214) baseStart_8020214 baseEnd_8020214 := by
    simpa [prefixWord, tailWord_8020214, baseEnd_8020214] using wordTrace_append hprefix tailTrace_8020214
  have hstable : (prefixWord ++ tailWord_8020214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020214).length < 2 ^ (prefixWord ++ tailWord_8020214).sum := by decide
  have hdescent : baseEnd_8020214 < baseStart_8020214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020217 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 3, 8]
def baseStart_8020217 : Nat := 118140960795 + 8020217 * 2 ^ 59
def prefixEnd_8020217 : Nat := 4983230072969 + 3 ^ 40 * 8020217 * 2
def baseEnd_8020217 : Nat := 1372742091453584199267733

theorem tailTrace_8020217 : CollatzResearch.WordTrace tailWord_8020217 prefixEnd_8020217 1372742091453584199267733 := by
  unfold tailWord_8020217
  simp only [CollatzResearch.WordTrace]
  refine ⟨292521345585131027857818905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195014230390087351905212603 292521345585131027857818905)
  ·
    refine ⟨219391009188848270893364179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292521345585131027857818905 219391009188848270893364179)
    ·
      refine ⟨329086513783272406340046269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219391009188848270893364179 329086513783272406340046269)
      ·
        refine ⟨123407442668727152377517351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329086513783272406340046269 123407442668727152377517351)
        ·
          refine ⟨185111164003090728566276027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123407442668727152377517351 185111164003090728566276027)
          ·
            refine ⟨277666746004636092849414041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185111164003090728566276027 277666746004636092849414041)
            ·
              refine ⟨208250059503477069637060531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277666746004636092849414041 208250059503477069637060531)
              ·
                refine ⟨312375089255215604455590797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208250059503477069637060531 312375089255215604455590797)
                ·
                  refine ⟨117140658470705851670846549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312375089255215604455590797 117140658470705851670846549)
                  ·
                    refine ⟨1372742091453584199267733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117140658470705851670846549 1372742091453584199267733)
                    ·
                      rfl

theorem cell23_8020217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_8020217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020217 prefixEnd_8020217 := by exact prefixLift 8020217
  have htrace : WordTrace (prefixWord ++ tailWord_8020217) baseStart_8020217 baseEnd_8020217 := by
    simpa [prefixWord, tailWord_8020217, baseEnd_8020217] using wordTrace_append hprefix tailTrace_8020217
  have hstable : (prefixWord ++ tailWord_8020217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020217).length < 2 ^ (prefixWord ++ tailWord_8020217).sum := by decide
  have hdescent : baseEnd_8020217 < baseStart_8020217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020258 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_8020258 : Nat := 118140960795 + 8020258 * 2 ^ 59
def prefixEnd_8020258 : Nat := 4983230072969 + 3 ^ 40 * 8020258 * 2
def baseEnd_8020258 : Nat := 4118247327067586937390511

theorem tailTrace_8020258 : CollatzResearch.WordTrace tailWord_8020258 prefixEnd_8020258 4118247327067586937390511 := by
  unfold tailWord_8020258
  simp only [CollatzResearch.WordTrace]
  refine ⟨73130710244495622965015357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195015227318654994573374285 73130710244495622965015357)
  ·
    refine ⟨27424016341685858611880759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73130710244495622965015357 27424016341685858611880759)
    ·
      refine ⟨41136024512528787917821139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27424016341685858611880759 41136024512528787917821139)
      ·
        refine ⟨61704036768793181876731709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41136024512528787917821139 61704036768793181876731709)
        ·
          refine ⟨23139013788297443203774391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61704036768793181876731709 23139013788297443203774391)
          ·
            refine ⟨34708520682446164805661587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23139013788297443203774391 34708520682446164805661587)
            ·
              refine ⟨52062781023669247208492381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34708520682446164805661587 52062781023669247208492381)
              ·
                refine ⟨19523542883875967703184643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52062781023669247208492381 19523542883875967703184643)
                ·
                  refine ⟨29285314325813951554776965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19523542883875967703184643 29285314325813951554776965)
                  ·
                    refine ⟨5490996436090115916520681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29285314325813951554776965 5490996436090115916520681)
                    ·
                      refine ⟨4118247327067586937390511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5490996436090115916520681 4118247327067586937390511)
                      ·
                        rfl

theorem cell23_8020258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_8020258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020258 prefixEnd_8020258 := by exact prefixLift 8020258
  have htrace : WordTrace (prefixWord ++ tailWord_8020258) baseStart_8020258 baseEnd_8020258 := by
    simpa [prefixWord, tailWord_8020258, baseEnd_8020258] using wordTrace_append hprefix tailTrace_8020258
  have hstable : (prefixWord ++ tailWord_8020258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020258).length < 2 ^ (prefixWord ++ tailWord_8020258).sum := by decide
  have hdescent : baseEnd_8020258 < baseStart_8020258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020292 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_8020292 : Nat := 118140960795 + 8020292 * 2 ^ 59
def prefixEnd_8020292 : Nat := 4983230072969 + 3 ^ 40 * 8020292 * 2
def baseEnd_8020292 : Nat := 4118264785409839804365355

theorem tailTrace_8020292 : CollatzResearch.WordTrace tailWord_8020292 prefixEnd_8020292 4118264785409839804365355 := by
  unfold tailWord_8020292
  simp only [CollatzResearch.WordTrace]
  refine ⟨146262040529929657833399565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195016054039906210444532753 146262040529929657833399565)
  ·
    refine ⟨54848265198723621687524837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146262040529929657833399565 54848265198723621687524837)
    ·
      refine ⟨10284049724760679066410907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54848265198723621687524837 10284049724760679066410907)
      ·
        refine ⟨15426074587141018599616361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284049724760679066410907 15426074587141018599616361)
        ·
          refine ⟨11569555940355763949712271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15426074587141018599616361 11569555940355763949712271)
          ·
            refine ⟨17354333910533645924568407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569555940355763949712271 17354333910533645924568407)
            ·
              refine ⟨26031500865800468886852611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17354333910533645924568407 26031500865800468886852611)
              ·
                refine ⟨39047251298700703330278917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26031500865800468886852611 39047251298700703330278917)
                ·
                  refine ⟨7321359618506381874427297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39047251298700703330278917 7321359618506381874427297)
                  ·
                    refine ⟨5491019713879786405820473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7321359618506381874427297 5491019713879786405820473)
                    ·
                      refine ⟨4118264785409839804365355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491019713879786405820473 4118264785409839804365355)
                      ·
                        rfl

theorem cell23_8020292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_8020292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020292 prefixEnd_8020292 := by exact prefixLift 8020292
  have htrace : WordTrace (prefixWord ++ tailWord_8020292) baseStart_8020292 baseEnd_8020292 := by
    simpa [prefixWord, tailWord_8020292, baseEnd_8020292] using wordTrace_append hprefix tailTrace_8020292
  have hstable : (prefixWord ++ tailWord_8020292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020292).length < 2 ^ (prefixWord ++ tailWord_8020292).sum := by decide
  have hdescent : baseEnd_8020292 < baseStart_8020292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020324 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_8020324 : Nat := 118140960795 + 8020324 * 2 ^ 59
def prefixEnd_8020324 : Nat := 4983230072969 + 3 ^ 40 * 8020324 * 2
def baseEnd_8020324 : Nat := 1372760405596927893055069

theorem tailTrace_8020324 : CollatzResearch.WordTrace tailWord_8020324 prefixEnd_8020324 1372760405596927893055069 := by
  unfold tailWord_8020324
  simp only [CollatzResearch.WordTrace]
  refine ⟨146262624097871692565982013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195016832130495590087976017 146262624097871692565982013)
  ·
    refine ⟨54848484036701884712243255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146262624097871692565982013 54848484036701884712243255)
    ·
      refine ⟨82272726055052827068364883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54848484036701884712243255 82272726055052827068364883)
      ·
        refine ⟨123409089082579240602547325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82272726055052827068364883 123409089082579240602547325)
        ·
          refine ⟨46278408405967215225955247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123409089082579240602547325 46278408405967215225955247)
          ·
            refine ⟨69417612608950822838932871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46278408405967215225955247 69417612608950822838932871)
            ·
              refine ⟨104126418913426234258399307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69417612608950822838932871 104126418913426234258399307)
              ·
                refine ⟨156189628370139351387598961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104126418913426234258399307 156189628370139351387598961)
                ·
                  refine ⟨117142221277604513540699221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156189628370139351387598961 117142221277604513540699221)
                  ·
                    refine ⟨1372760405596927893055069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117142221277604513540699221 1372760405596927893055069)
                    ·
                      rfl

theorem cell23_8020324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_8020324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020324 prefixEnd_8020324 := by exact prefixLift 8020324
  have htrace : WordTrace (prefixWord ++ tailWord_8020324) baseStart_8020324 baseEnd_8020324 := by
    simpa [prefixWord, tailWord_8020324, baseEnd_8020324] using wordTrace_append hprefix tailTrace_8020324
  have hstable : (prefixWord ++ tailWord_8020324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020324).length < 2 ^ (prefixWord ++ tailWord_8020324).sum := by decide
  have hdescent : baseEnd_8020324 < baseStart_8020324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020351 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 3]
def baseStart_8020351 : Nat := 118140960795 + 8020351 * 2 ^ 59
def prefixEnd_8020351 : Nat := 4983230072969 + 3 ^ 40 * 8020351 * 2
def baseEnd_8020351 : Nat := 4118295080768455073527583

theorem tailTrace_8020351 : CollatzResearch.WordTrace tailWord_8020351 prefixEnd_8020351 4118295080768455073527583 := by
  unfold tailWord_8020351
  simp only [CollatzResearch.WordTrace]
  refine ⟨292526232966645568743196907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195017488644430379162131271 292526232966645568743196907)
  ·
    refine ⟨438789349449968353114795361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292526232966645568743196907 438789349449968353114795361)
    ·
      refine ⟨329092012087476264836096521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438789349449968353114795361 329092012087476264836096521)
      ·
        refine ⟨246819009065607198627072391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329092012087476264836096521 246819009065607198627072391)
        ·
          refine ⟨370228513598410797940608587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246819009065607198627072391 370228513598410797940608587)
          ·
            refine ⟨555342770397616196910912881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370228513598410797940608587 555342770397616196910912881)
            ·
              refine ⟨416507077798212147683184661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555342770397616196910912881 416507077798212147683184661)
              ·
                refine ⟨19523769271791194422649281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 416507077798212147683184661 19523769271791194422649281)
                ·
                  refine ⟨14642826953843395816986961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19523769271791194422649281 14642826953843395816986961)
                  ·
                    refine ⟨10982120215382546862740221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14642826953843395816986961 10982120215382546862740221)
                    ·
                      refine ⟨4118295080768455073527583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10982120215382546862740221 4118295080768455073527583)
                      ·
                        rfl

theorem cell23_8020351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_8020351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020351 prefixEnd_8020351 := by exact prefixLift 8020351
  have htrace : WordTrace (prefixWord ++ tailWord_8020351) baseStart_8020351 baseEnd_8020351 := by
    simpa [prefixWord, tailWord_8020351, baseEnd_8020351] using wordTrace_append hprefix tailTrace_8020351
  have hstable : (prefixWord ++ tailWord_8020351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020351).length < 2 ^ (prefixWord ++ tailWord_8020351).sum := by decide
  have hdescent : baseEnd_8020351 < baseStart_8020351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020431 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 6, 4]
def baseStart_8020431 : Nat := 118140960795 + 8020431 * 2 ^ 59
def prefixEnd_8020431 : Nat := 4983230072969 + 3 ^ 40 * 8020431 * 2
def baseEnd_8020431 : Nat := 1372778719740271586842405

theorem tailTrace_8020431 : CollatzResearch.WordTrace tailWord_8020431 prefixEnd_8020431 1372778719740271586842405 := by
  unfold tailWord_8020431
  simp only [CollatzResearch.WordTrace]
  refine ⟨292529150806355742406109147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195019433870903828270739431 292529150806355742406109147)
  ·
    refine ⟨438793726209533613609163721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292529150806355742406109147 438793726209533613609163721)
    ·
      refine ⟨329095294657150210206872791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438793726209533613609163721 329095294657150210206872791)
      ·
        refine ⟨493642941985725315310309187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329095294657150210206872791 493642941985725315310309187)
        ·
          refine ⟨740464412978587972965463781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493642941985725315310309187 740464412978587972965463781)
          ·
            refine ⟨138837077433485244931024459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 740464412978587972965463781 138837077433485244931024459)
            ·
              refine ⟨208255616150227867396536689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138837077433485244931024459 208255616150227867396536689)
              ·
                refine ⟨156191712112670900547402517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208255616150227867396536689 156191712112670900547402517)
                ·
                  refine ⟨7321486505281448463159493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156191712112670900547402517 7321486505281448463159493)
                  ·
                    refine ⟨1372778719740271586842405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7321486505281448463159493 1372778719740271586842405)
                    ·
                      rfl

theorem cell23_8020431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_8020431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020431 prefixEnd_8020431 := by exact prefixLift 8020431
  have htrace : WordTrace (prefixWord ++ tailWord_8020431) baseStart_8020431 baseEnd_8020431 := by
    simpa [prefixWord, tailWord_8020431, baseEnd_8020431] using wordTrace_append hprefix tailTrace_8020431
  have hstable : (prefixWord ++ tailWord_8020431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020431).length < 2 ^ (prefixWord ++ tailWord_8020431).sum := by decide
  have hdescent : baseEnd_8020431 < baseStart_8020431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020455 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_8020455 : Nat := 118140960795 + 8020455 * 2 ^ 59
def prefixEnd_8020455 : Nat := 4983230072969 + 3 ^ 40 * 8020455 * 2
def baseEnd_8020455 : Nat := 4118348482756522666627105

theorem tailTrace_8020455 : CollatzResearch.WordTrace tailWord_8020455 prefixEnd_8020455 4118348482756522666627105 := by
  unfold tailWord_8020455
  simp only [CollatzResearch.WordTrace]
  refine ⟨292530026158268794504982819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195020017438845863003321879 292530026158268794504982819)
  ·
    refine ⟨438795039237403191757474229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292530026158268794504982819 438795039237403191757474229)
    ·
      refine ⟨41137034928506549227263209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438795039237403191757474229 41137034928506549227263209)
      ·
        refine ⟨30852776196379911920447407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41137034928506549227263209 30852776196379911920447407)
        ·
          refine ⟨46279164294569867880671111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30852776196379911920447407 46279164294569867880671111)
          ·
            refine ⟨69418746441854801821006667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46279164294569867880671111 69418746441854801821006667)
            ·
              refine ⟨104128119662782202731510001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69418746441854801821006667 104128119662782202731510001)
              ·
                refine ⟨78096089747086652048632501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104128119662782202731510001 78096089747086652048632501)
                ·
                  refine ⟨7321508413789373629559297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78096089747086652048632501 7321508413789373629559297)
                  ·
                    refine ⟨5491131310342030222169473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7321508413789373629559297 5491131310342030222169473)
                    ·
                      refine ⟨4118348482756522666627105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491131310342030222169473 4118348482756522666627105)
                      ·
                        rfl

theorem cell23_8020455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_8020455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020455 prefixEnd_8020455 := by exact prefixLift 8020455
  have htrace : WordTrace (prefixWord ++ tailWord_8020455) baseStart_8020455 baseEnd_8020455 := by
    simpa [prefixWord, tailWord_8020455, baseEnd_8020455] using wordTrace_append hprefix tailTrace_8020455
  have hstable : (prefixWord ++ tailWord_8020455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020455).length < 2 ^ (prefixWord ++ tailWord_8020455).sum := by decide
  have hdescent : baseEnd_8020455 < baseStart_8020455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020472 : List Nat := [2, 1, 2, 1, 1, 4, 1, 6, 1, 2, 2]
def baseStart_8020472 : Nat := 118140960795 + 8020472 * 2 ^ 59
def prefixEnd_8020472 : Nat := 4983230072969 + 3 ^ 40 * 8020472 * 2
def baseEnd_8020472 : Nat := 4118357211927649100114527

theorem tailTrace_8020472 : CollatzResearch.WordTrace tailWord_8020472 prefixEnd_8020472 4118357211927649100114527 := by
  unfold tailWord_8020472
  simp only [CollatzResearch.WordTrace]
  refine ⟨146265323099603603204175835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195020430799471470938901113 146265323099603603204175835)
  ·
    refine ⟨219397984649405404806263753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146265323099603603204175835 219397984649405404806263753)
    ·
      refine ⟨164548488487054053604697815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219397984649405404806263753 164548488487054053604697815)
      ·
        refine ⟨246822732730581080407046723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164548488487054053604697815 246822732730581080407046723)
        ·
          refine ⟨370234099095871620610570085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246822732730581080407046723 370234099095871620610570085)
          ·
            refine ⟨69418893580475928864481891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370234099095871620610570085 69418893580475928864481891)
            ·
              refine ⟨104128340370713893296722837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69418893580475928864481891 104128340370713893296722837)
              ·
                refine ⟨4881015954877213748283883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104128340370713893296722837 4881015954877213748283883)
                ·
                  refine ⟨7321523932315820622425825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881015954877213748283883 7321523932315820622425825)
                  ·
                    refine ⟨5491142949236865466819369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7321523932315820622425825 5491142949236865466819369)
                    ·
                      refine ⟨4118357211927649100114527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491142949236865466819369 4118357211927649100114527)
                      ·
                        rfl

theorem cell23_8020472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_8020472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020472 prefixEnd_8020472 := by exact prefixLift 8020472
  have htrace : WordTrace (prefixWord ++ tailWord_8020472) baseStart_8020472 baseEnd_8020472 := by
    simpa [prefixWord, tailWord_8020472, baseEnd_8020472] using wordTrace_append hprefix tailTrace_8020472
  have hstable : (prefixWord ++ tailWord_8020472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020472).length < 2 ^ (prefixWord ++ tailWord_8020472).sum := by decide
  have hdescent : baseEnd_8020472 < baseStart_8020472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020482 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_8020482 : Nat := 118140960795 + 8020482 * 2 ^ 59
def prefixEnd_8020482 : Nat := 4983230072969 + 3 ^ 40 * 8020482 * 2
def baseEnd_8020482 : Nat := 1372787448911398020329827

theorem tailTrace_8020482 : CollatzResearch.WordTrace tailWord_8020482 prefixEnd_8020482 1372787448911398020329827 := by
  unfold tailWord_8020482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73132752732292744529053925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195020673952780652077477133 73132752732292744529053925)
  ·
    refine ⟨13712391137304889599197611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73132752732292744529053925 13712391137304889599197611)
    ·
      refine ⟨20568586705957334398796417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13712391137304889599197611 20568586705957334398796417)
      ·
        refine ⟨15426440029468000799097313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20568586705957334398796417 15426440029468000799097313)
        ·
          refine ⟨11569830022101000599322985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15426440029468000799097313 11569830022101000599322985)
          ·
            refine ⟨8677372516575750449492239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11569830022101000599322985 8677372516575750449492239)
            ·
              refine ⟨13016058774863625674238359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677372516575750449492239 13016058774863625674238359)
              ·
                refine ⟨19524088162295438511357539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13016058774863625674238359 19524088162295438511357539)
                ·
                  refine ⟨29286132243443157767036309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19524088162295438511357539 29286132243443157767036309)
                  ·
                    refine ⟨1372787448911398020329827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29286132243443157767036309 1372787448911398020329827)
                    ·
                      rfl

theorem cell23_8020482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_8020482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020482 prefixEnd_8020482 := by exact prefixLift 8020482
  have htrace : WordTrace (prefixWord ++ tailWord_8020482) baseStart_8020482 baseEnd_8020482 := by
    simpa [prefixWord, tailWord_8020482, baseEnd_8020482] using wordTrace_append hprefix tailTrace_8020482
  have hstable : (prefixWord ++ tailWord_8020482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020482).length < 2 ^ (prefixWord ++ tailWord_8020482).sum := by decide
  have hdescent : baseEnd_8020482 < baseStart_8020482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020501 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_8020501 : Nat := 118140960795 + 8020501 * 2 ^ 59
def prefixEnd_8020501 : Nat := 4983230072969 + 3 ^ 40 * 8020501 * 2
def baseEnd_8020501 : Nat := 4118372102866629486651893

theorem tailTrace_8020501 : CollatzResearch.WordTrace tailWord_8020501 prefixEnd_8020501 4118372102866629486651893 := by
  unfold tailWord_8020501
  simp only [CollatzResearch.WordTrace]
  refine ⟨292531703916102144361157357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195021135944068096240771571 292531703916102144361157357)
  ·
    refine ⟨109699388968538304135434009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292531703916102144361157357 109699388968538304135434009)
    ·
      refine ⟨82274541726403728101575507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109699388968538304135434009 82274541726403728101575507)
      ·
        refine ⟨123411812589605592152363261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82274541726403728101575507 123411812589605592152363261)
        ·
          refine ⟨46279429721102097057136223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123411812589605592152363261 46279429721102097057136223)
          ·
            refine ⟨69419144581653145585704335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46279429721102097057136223 69419144581653145585704335)
            ·
              refine ⟨104128716872479718378556503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69419144581653145585704335 104128716872479718378556503)
              ·
                refine ⟨156193075308719577567834755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104128716872479718378556503 156193075308719577567834755)
                ·
                  refine ⟨234289612963079366351752133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156193075308719577567834755 234289612963079366351752133)
                  ·
                    refine ⟨43929302430577381190953525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234289612963079366351752133 43929302430577381190953525)
                    ·
                      refine ⟨4118372102866629486651893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43929302430577381190953525 4118372102866629486651893)
                      ·
                        rfl

theorem cell23_8020501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_8020501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020501 prefixEnd_8020501 := by exact prefixLift 8020501
  have htrace : WordTrace (prefixWord ++ tailWord_8020501) baseStart_8020501 baseEnd_8020501 := by
    simpa [prefixWord, tailWord_8020501, baseEnd_8020501] using wordTrace_append hprefix tailTrace_8020501
  have hstable : (prefixWord ++ tailWord_8020501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020501).length < 2 ^ (prefixWord ++ tailWord_8020501).sum := by decide
  have hdescent : baseEnd_8020501 < baseStart_8020501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020511 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_8020511 : Nat := 118140960795 + 8020511 * 2 ^ 59
def prefixEnd_8020511 : Nat := 4983230072969 + 3 ^ 40 * 8020511 * 2
def baseEnd_8020511 : Nat := 4118377237673174447526847

theorem tailTrace_8020511 : CollatzResearch.WordTrace tailWord_8020511 prefixEnd_8020511 4118377237673174447526847 := by
  unfold tailWord_8020511
  simp only [CollatzResearch.WordTrace]
  refine ⟨292532068646065916069021387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195021379097377277379347591 292532068646065916069021387)
  ·
    refine ⟨438798102969098874103532081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292532068646065916069021387 438798102969098874103532081)
    ·
      refine ⟨329098577226824155577649061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438798102969098874103532081 329098577226824155577649061)
      ·
        refine ⟨61705983230029529170809199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329098577226824155577649061 61705983230029529170809199)
        ·
          refine ⟨92558974845044293756213799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61705983230029529170809199 92558974845044293756213799)
          ·
            refine ⟨138838462267566440634320699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92558974845044293756213799 138838462267566440634320699)
            ·
              refine ⟨208257693401349660951481049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138838462267566440634320699 208257693401349660951481049)
              ·
                refine ⟨156193270051012245713610787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208257693401349660951481049 156193270051012245713610787)
                ·
                  refine ⟨234289905076518368570416181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156193270051012245713610787 234289905076518368570416181)
                  ·
                    refine ⟨21964678600923597053476517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234289905076518368570416181 21964678600923597053476517)
                    ·
                      refine ⟨4118377237673174447526847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21964678600923597053476517 4118377237673174447526847)
                      ·
                        rfl

theorem cell23_8020511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_8020511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020511 prefixEnd_8020511 := by exact prefixLift 8020511
  have htrace : WordTrace (prefixWord ++ tailWord_8020511) baseStart_8020511 baseEnd_8020511 := by
    simpa [prefixWord, tailWord_8020511, baseEnd_8020511] using wordTrace_append hprefix tailTrace_8020511
  have hstable : (prefixWord ++ tailWord_8020511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020511).length < 2 ^ (prefixWord ++ tailWord_8020511).sum := by decide
  have hdescent : baseEnd_8020511 < baseStart_8020511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020531 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5]
def baseStart_8020531 : Nat := 118140960795 + 8020531 * 2 ^ 59
def prefixEnd_8020531 : Nat := 4983230072969 + 3 ^ 40 * 8020531 * 2
def baseEnd_8020531 : Nat := 4118387507286264369276755

theorem tailTrace_8020531 : CollatzResearch.WordTrace tailWord_8020531 prefixEnd_8020531 4118387507286264369276755 := by
  unfold tailWord_8020531
  simp only [CollatzResearch.WordTrace]
  refine ⟨292532798105993459484749447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195021865403995639656499631 292532798105993459484749447)
  ·
    refine ⟨438799197158990189227124171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292532798105993459484749447 438799197158990189227124171)
    ·
      refine ⟨658198795738485283840686257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438799197158990189227124171 658198795738485283840686257)
      ·
        refine ⟨493649096803863962880514693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658198795738485283840686257 493649096803863962880514693)
        ·
          refine ⟨92559205650724493040096505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493649096803863962880514693 92559205650724493040096505)
          ·
            refine ⟨69419404238043369780072379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92559205650724493040096505 69419404238043369780072379)
            ·
              refine ⟨104129106357065054670108569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69419404238043369780072379 104129106357065054670108569)
              ·
                refine ⟨78096829767798791002581427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104129106357065054670108569 78096829767798791002581427)
                ·
                  refine ⟨117145244651698186503872141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78096829767798791002581427 117145244651698186503872141)
                  ·
                    refine ⟨43929466744386819938952053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117145244651698186503872141 43929466744386819938952053)
                    ·
                      refine ⟨4118387507286264369276755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43929466744386819938952053 4118387507286264369276755)
                      ·
                        rfl

theorem cell23_8020531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_8020531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020531 prefixEnd_8020531 := by exact prefixLift 8020531
  have htrace : WordTrace (prefixWord ++ tailWord_8020531) baseStart_8020531 baseEnd_8020531 := by
    simpa [prefixWord, tailWord_8020531, baseEnd_8020531] using wordTrace_append hprefix tailTrace_8020531
  have hstable : (prefixWord ++ tailWord_8020531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020531).length < 2 ^ (prefixWord ++ tailWord_8020531).sum := by decide
  have hdescent : baseEnd_8020531 < baseStart_8020531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020574 : List Nat := [4, 4, 1, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_8020574 : Nat := 118140960795 + 8020574 * 2 ^ 59
def prefixEnd_8020574 : Nat := 4983230072969 + 3 ^ 40 * 8020574 * 2
def baseEnd_8020574 : Nat := 4118409586954407701039059

theorem tailTrace_8020574 : CollatzResearch.WordTrace tailWord_8020574 prefixEnd_8020574 4118409586954407701039059 := by
  unfold tailWord_8020574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36566795805604709728570597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195022910963225118552376517 36566795805604709728570597)
  ·
    refine ⟨6856274213550883074106987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36566795805604709728570597 6856274213550883074106987)
    ·
      refine ⟨10284411320326324611160481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856274213550883074106987 10284411320326324611160481)
      ·
        refine ⟨7713308490244743458370361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10284411320326324611160481 7713308490244743458370361)
        ·
          refine ⟨5784981367683557593777771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7713308490244743458370361 5784981367683557593777771)
          ·
            refine ⟨8677472051525336390666657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784981367683557593777771 8677472051525336390666657)
            ·
              refine ⟨6508104038644002292999993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8677472051525336390666657 6508104038644002292999993)
              ·
                refine ⟨4881078028983001719749995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6508104038644002292999993 4881078028983001719749995)
                ·
                  refine ⟨7321617043474502579624993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881078028983001719749995 7321617043474502579624993)
                  ·
                    refine ⟨5491212782605876934718745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7321617043474502579624993 5491212782605876934718745)
                    ·
                      refine ⟨4118409586954407701039059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491212782605876934718745 4118409586954407701039059)
                      ·
                        rfl

theorem cell23_8020574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_8020574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020574 prefixEnd_8020574 := by exact prefixLift 8020574
  have htrace : WordTrace (prefixWord ++ tailWord_8020574) baseStart_8020574 baseEnd_8020574 := by
    simpa [prefixWord, tailWord_8020574, baseEnd_8020574] using wordTrace_append hprefix tailTrace_8020574
  have hstable : (prefixWord ++ tailWord_8020574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020574).length < 2 ^ (prefixWord ++ tailWord_8020574).sum := by decide
  have hdescent : baseEnd_8020574 < baseStart_8020574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020722 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_8020722 : Nat := 118140960795 + 8020722 * 2 ^ 59
def prefixEnd_8020722 : Nat := 4983230072969 + 3 ^ 40 * 8020722 * 2
def baseEnd_8020722 : Nat := 1372828527363757707329459

theorem tailTrace_8020722 : CollatzResearch.WordTrace tailWord_8020722 prefixEnd_8020722 1372828527363757707329459 := by
  unfold tailWord_8020722
  simp only [CollatzResearch.WordTrace]
  refine ⟨73134941112075374776238105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195026509632200999403301613 73134941112075374776238105)
  ·
    refine ⟨54851205834056531082178579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73134941112075374776238105 54851205834056531082178579)
    ·
      refine ⟨82276808751084796623267869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54851205834056531082178579 82276808751084796623267869)
      ·
        refine ⟨30853803281656798733725451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82276808751084796623267869 30853803281656798733725451)
        ·
          refine ⟨46280704922485198100588177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30853803281656798733725451 46280704922485198100588177)
          ·
            refine ⟨34710528691863898575441133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46280704922485198100588177 34710528691863898575441133)
            ·
              refine ⟨13016448259448961965790425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34710528691863898575441133 13016448259448961965790425)
              ·
                refine ⟨9762336194586721474342819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13016448259448961965790425 9762336194586721474342819)
                ·
                  refine ⟨14643504291880082211514229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9762336194586721474342819 14643504291880082211514229)
                  ·
                    refine ⟨1372828527363757707329459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14643504291880082211514229 1372828527363757707329459)
                    ·
                      rfl

theorem cell23_8020722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_8020722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020722 prefixEnd_8020722 := by exact prefixLift 8020722
  have htrace : WordTrace (prefixWord ++ tailWord_8020722) baseStart_8020722 baseEnd_8020722 := by
    simpa [prefixWord, tailWord_8020722, baseEnd_8020722] using wordTrace_append hprefix tailTrace_8020722
  have hstable : (prefixWord ++ tailWord_8020722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020722).length < 2 ^ (prefixWord ++ tailWord_8020722).sum := by decide
  have hdescent : baseEnd_8020722 < baseStart_8020722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020745 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 5]
def baseStart_8020745 : Nat := 118140960795 + 8020745 * 2 ^ 59
def prefixEnd_8020745 : Nat := 4983230072969 + 3 ^ 40 * 8020745 * 2
def baseEnd_8020745 : Nat := 4118497392146326532000771

theorem tailTrace_8020745 : CollatzResearch.WordTrace tailWord_8020745 prefixEnd_8020745 4118497392146326532000771 := by
  unfold tailWord_8020745
  simp only [CollatzResearch.WordTrace]
  refine ⟨292540603327218174033039689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195027068884812116022026459 292540603327218174033039689)
  ·
    refine ⟨219405452495413630524779767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292540603327218174033039689 219405452495413630524779767)
    ·
      refine ⟨329108178743120445787169651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219405452495413630524779767 329108178743120445787169651)
      ·
        refine ⟨493662268114680668680754477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329108178743120445787169651 493662268114680668680754477)
        ·
          refine ⟨185123350543005250755282929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493662268114680668680754477 185123350543005250755282929)
          ·
            refine ⟨138842512907253938066462197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185123350543005250755282929 138842512907253938066462197)
            ·
              refine ⟨13016485585055056693730831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138842512907253938066462197 13016485585055056693730831)
              ·
                refine ⟨19524728377582585040596247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13016485585055056693730831 19524728377582585040596247)
                ·
                  refine ⟨29287092566373877560894371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19524728377582585040596247 29287092566373877560894371)
                  ·
                    refine ⟨43930638849560816341341557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29287092566373877560894371 43930638849560816341341557)
                    ·
                      refine ⟨4118497392146326532000771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43930638849560816341341557 4118497392146326532000771)
                      ·
                        rfl

theorem cell23_8020745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_8020745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020745 prefixEnd_8020745 := by exact prefixLift 8020745
  have htrace : WordTrace (prefixWord ++ tailWord_8020745) baseStart_8020745 baseEnd_8020745 := by
    simpa [prefixWord, tailWord_8020745, baseEnd_8020745] using wordTrace_append hprefix tailTrace_8020745
  have hstable : (prefixWord ++ tailWord_8020745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020745).length < 2 ^ (prefixWord ++ tailWord_8020745).sum := by decide
  have hdescent : baseEnd_8020745 < baseStart_8020745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020792 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_8020792 : Nat := 118140960795 + 8020792 * 2 ^ 59
def prefixEnd_8020792 : Nat := 4983230072969 + 3 ^ 40 * 8020792 * 2
def baseEnd_8020792 : Nat := 4118521525737087848113055

theorem tailTrace_8020792 : CollatzResearch.WordTrace tailWord_8020792 prefixEnd_8020792 4118521525737087848113055 := by
  unfold tailWord_8020792
  simp only [CollatzResearch.WordTrace]
  refine ⟨146271158779023950530000315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195028211705365267373333753 146271158779023950530000315)
  ·
    refine ⟨219406738168535925795000473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146271158779023950530000315 219406738168535925795000473)
    ·
      refine ⟨164555053626401944346250355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219406738168535925795000473 164555053626401944346250355)
      ·
        refine ⟨246832580439602916519375533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164555053626401944346250355 246832580439602916519375533)
        ·
          refine ⟨92562217664851093694765825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246832580439602916519375533 92562217664851093694765825)
          ·
            refine ⟨69421663248638320271074369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92562217664851093694765825 69421663248638320271074369)
            ·
              refine ⟨52066247436478740203305777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69421663248638320271074369 52066247436478740203305777)
              ·
                refine ⟨39049685577359055152479333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52066247436478740203305777 39049685577359055152479333)
                ·
                  refine ⟨7321816045754822841089875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39049685577359055152479333 7321816045754822841089875)
                  ·
                    refine ⟨10982724068632234261634813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321816045754822841089875 10982724068632234261634813)
                    ·
                      refine ⟨4118521525737087848113055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10982724068632234261634813 4118521525737087848113055)
                      ·
                        rfl

theorem cell23_8020792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_8020792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020792 prefixEnd_8020792 := by exact prefixLift 8020792
  have htrace : WordTrace (prefixWord ++ tailWord_8020792) baseStart_8020792 baseEnd_8020792 := by
    simpa [prefixWord, tailWord_8020792, baseEnd_8020792] using wordTrace_append hprefix tailTrace_8020792
  have hstable : (prefixWord ++ tailWord_8020792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020792).length < 2 ^ (prefixWord ++ tailWord_8020792).sum := by decide
  have hdescent : baseEnd_8020792 < baseStart_8020792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020809 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 3]
def baseStart_8020809 : Nat := 118140960795 + 8020809 * 2 ^ 59
def prefixEnd_8020809 : Nat := 4983230072969 + 3 ^ 40 * 8020809 * 2
def baseEnd_8020809 : Nat := 4118530254908214281600477

theorem tailTrace_8020809 : CollatzResearch.WordTrace tailWord_8020809 prefixEnd_8020809 4118530254908214281600477 := by
  unfold tailWord_8020809
  simp only [CollatzResearch.WordTrace]
  refine ⟨292542937598986312963369481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195028625065990875308912987 292542937598986312963369481)
  ·
    refine ⟨219407203199239734722527111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292542937598986312963369481 219407203199239734722527111)
    ·
      refine ⟨329110804798859602083790667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219407203199239734722527111 329110804798859602083790667)
      ·
        refine ⟨493666207198289403125686001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329110804798859602083790667 493666207198289403125686001)
        ·
          refine ⟨370249655398717052344264501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493666207198289403125686001 370249655398717052344264501)
          ·
            refine ⟨34710905193629723657274797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370249655398717052344264501 34710905193629723657274797)
            ·
              refine ⟨13016589447611146371478049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34710905193629723657274797 13016589447611146371478049)
              ·
                refine ⟨9762442085708359778608537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13016589447611146371478049 9762442085708359778608537)
                ·
                  refine ⟨7321831564281269833956403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9762442085708359778608537 7321831564281269833956403)
                  ·
                    refine ⟨10982747346421904750934605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321831564281269833956403 10982747346421904750934605)
                    ·
                      refine ⟨4118530254908214281600477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10982747346421904750934605 4118530254908214281600477)
                      ·
                        rfl

theorem cell23_8020809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 3].length) (baseStart_8020809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020809 prefixEnd_8020809 := by exact prefixLift 8020809
  have htrace : WordTrace (prefixWord ++ tailWord_8020809) baseStart_8020809 baseEnd_8020809 := by
    simpa [prefixWord, tailWord_8020809, baseEnd_8020809] using wordTrace_append hprefix tailTrace_8020809
  have hstable : (prefixWord ++ tailWord_8020809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020809).length < 2 ^ (prefixWord ++ tailWord_8020809).sum := by decide
  have hdescent : baseEnd_8020809 < baseStart_8020809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020825 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 2, 6]
def baseStart_8020825 : Nat := 118140960795 + 8020825 * 2 ^ 59
def prefixEnd_8020825 : Nat := 4983230072969 + 3 ^ 40 * 8020825 * 2
def baseEnd_8020825 : Nat := 1372846156866228739666801

theorem tailTrace_8020825 : CollatzResearch.WordTrace tailWord_8020825 prefixEnd_8020825 1372846156866228739666801 := by
  unfold tailWord_8020825
  simp only [CollatzResearch.WordTrace]
  refine ⟨292543521166928347695951929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195029014111285565130634619 292543521166928347695951929)
  ·
    refine ⟨219407640875196260771963947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292543521166928347695951929 219407640875196260771963947)
    ·
      refine ⟨329111461312794391157945921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219407640875196260771963947 329111461312794391157945921)
      ·
        refine ⟨246833595984595793368459441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329111461312794391157945921 246833595984595793368459441)
        ·
          refine ⟨185125196988446845026344581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246833595984595793368459441 185125196988446845026344581)
          ·
            refine ⟨34710974435333783442439609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185125196988446845026344581 34710974435333783442439609)
            ·
              refine ⟨26033230826500337581829707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34710974435333783442439609 26033230826500337581829707)
              ·
                refine ⟨39049846239750506372744561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26033230826500337581829707 39049846239750506372744561)
                ·
                  refine ⟨29287384679812879779558421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39049846239750506372744561 29287384679812879779558421)
                  ·
                    refine ⟨1372846156866228739666801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29287384679812879779558421 1372846156866228739666801)
                    ·
                      rfl

theorem cell23_8020825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_8020825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020825 prefixEnd_8020825 := by exact prefixLift 8020825
  have htrace : WordTrace (prefixWord ++ tailWord_8020825) baseStart_8020825 baseEnd_8020825 := by
    simpa [prefixWord, tailWord_8020825, baseEnd_8020825] using wordTrace_append hprefix tailTrace_8020825
  have hstable : (prefixWord ++ tailWord_8020825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020825).length < 2 ^ (prefixWord ++ tailWord_8020825).sum := by decide
  have hdescent : baseEnd_8020825 < baseStart_8020825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020826 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3]
def baseStart_8020826 : Nat := 118140960795 + 8020826 * 2 ^ 59
def prefixEnd_8020826 : Nat := 4983230072969 + 3 ^ 40 * 8020826 * 2
def baseEnd_8020826 : Nat := 4118538984079340715087899

theorem tailTrace_8020826 : CollatzResearch.WordTrace tailWord_8020826 prefixEnd_8020826 4118538984079340715087899 := by
  unfold tailWord_8020826
  simp only [CollatzResearch.WordTrace]
  refine ⟨73135889409981181216684583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195029038426616483244492221 73135889409981181216684583)
  ·
    refine ⟨109703834114971771825026875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73135889409981181216684583 109703834114971771825026875)
    ·
      refine ⟨164555751172457657737540313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109703834114971771825026875 164555751172457657737540313)
      ·
        refine ⟨123416813379343243303155235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164555751172457657737540313 123416813379343243303155235)
        ·
          refine ⟨185125220069014864954732853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123416813379343243303155235 185125220069014864954732853)
          ·
            refine ⟨17355489381470143589506205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185125220069014864954732853 17355489381470143589506205)
            ·
              refine ⟨6508308518051303846064827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17355489381470143589506205 6508308518051303846064827)
              ·
                refine ⟨9762462777076955769097241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6508308518051303846064827 9762462777076955769097241)
                ·
                  refine ⟨7321847082807716826822931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9762462777076955769097241 7321847082807716826822931)
                  ·
                    refine ⟨10982770624211575240234397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321847082807716826822931 10982770624211575240234397)
                    ·
                      refine ⟨4118538984079340715087899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10982770624211575240234397 4118538984079340715087899)
                      ·
                        rfl

theorem cell23_8020826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_8020826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020826 prefixEnd_8020826 := by exact prefixLift 8020826
  have htrace : WordTrace (prefixWord ++ tailWord_8020826) baseStart_8020826 baseEnd_8020826 := by
    simpa [prefixWord, tailWord_8020826, baseEnd_8020826] using wordTrace_append hprefix tailTrace_8020826
  have hstable : (prefixWord ++ tailWord_8020826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020826).length < 2 ^ (prefixWord ++ tailWord_8020826).sum := by decide
  have hdescent : baseEnd_8020826 < baseStart_8020826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020836 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_8020836 : Nat := 118140960795 + 8020836 * 2 ^ 59
def prefixEnd_8020836 : Nat := 4983230072969 + 3 ^ 40 * 8020836 * 2
def baseEnd_8020836 : Nat := 4118544118885885675962853

theorem tailTrace_8020836 : CollatzResearch.WordTrace tailWord_8020836 prefixEnd_8020836 4118544118885885675962853 := by
  unfold tailWord_8020836
  simp only [CollatzResearch.WordTrace]
  refine ⟨146271961184944248287301181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195029281579925664383068241 146271961184944248287301181)
  ·
    refine ⟨54851985444354093107737943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146271961184944248287301181 54851985444354093107737943)
    ·
      refine ⟨82277978166531139661606915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54851985444354093107737943 82277978166531139661606915)
      ·
        refine ⟨123416967249796709492410373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82277978166531139661606915 123416967249796709492410373)
        ·
          refine ⟨23140681359336883029826945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123416967249796709492410373 23140681359336883029826945)
          ·
            refine ⟨17355511019502662272370209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23140681359336883029826945 17355511019502662272370209)
            ·
              refine ⟨13016633264626996704277657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17355511019502662272370209 13016633264626996704277657)
              ·
                refine ⟨9762474948470247528208243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13016633264626996704277657 9762474948470247528208243)
                ·
                  refine ⟨14643712422705371292312365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9762474948470247528208243 14643712422705371292312365)
                  ·
                    refine ⟨5491392158514514234617137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14643712422705371292312365 5491392158514514234617137)
                    ·
                      refine ⟨4118544118885885675962853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491392158514514234617137 4118544118885885675962853)
                      ·
                        rfl

theorem cell23_8020836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_8020836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020836 prefixEnd_8020836 := by exact prefixLift 8020836
  have htrace : WordTrace (prefixWord ++ tailWord_8020836) baseStart_8020836 baseEnd_8020836 := by
    simpa [prefixWord, tailWord_8020836, baseEnd_8020836] using wordTrace_append hprefix tailTrace_8020836
  have hstable : (prefixWord ++ tailWord_8020836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020836).length < 2 ^ (prefixWord ++ tailWord_8020836).sum := by decide
  have hdescent : baseEnd_8020836 < baseStart_8020836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020849 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 4, 2, 2]
def baseStart_8020849 : Nat := 118140960795 + 8020849 * 2 ^ 59
def prefixEnd_8020849 : Nat := 4983230072969 + 3 ^ 40 * 8020849 * 2
def baseEnd_8020849 : Nat := 4118550794134394125100293

theorem tailTrace_8020849 : CollatzResearch.WordTrace tailWord_8020849 prefixEnd_8020849 4118550794134394125100293 := by
  unfold tailWord_8020849
  simp only [CollatzResearch.WordTrace]
  refine ⟨292544396518841399794825601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195029597679227599863217067 292544396518841399794825601)
  ·
    refine ⟨219408297389131049846119201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292544396518841399794825601 219408297389131049846119201)
    ·
      refine ⟨164556223041848287384589401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219408297389131049846119201 164556223041848287384589401)
      ·
        refine ⟨123417167281386215538442051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164556223041848287384589401 123417167281386215538442051)
        ·
          refine ⟨185125750922079323307663077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123417167281386215538442051 185125750922079323307663077)
          ·
            refine ⟨34711078297889873120186827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185125750922079323307663077 34711078297889873120186827)
            ·
              refine ⟨52066617446834809680280241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34711078297889873120186827 52066617446834809680280241)
              ·
                refine ⟨39049963085126107260210181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52066617446834809680280241 39049963085126107260210181)
                ·
                  refine ⟨7321868078461145111289409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39049963085126107260210181 7321868078461145111289409)
                  ·
                    refine ⟨5491401058845858833467057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7321868078461145111289409 5491401058845858833467057)
                    ·
                      refine ⟨4118550794134394125100293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491401058845858833467057 4118550794134394125100293)
                      ·
                        rfl

theorem cell23_8020849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_8020849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020849 prefixEnd_8020849 := by exact prefixLift 8020849
  have htrace : WordTrace (prefixWord ++ tailWord_8020849) baseStart_8020849 baseEnd_8020849 := by
    simpa [prefixWord, tailWord_8020849, baseEnd_8020849] using wordTrace_append hprefix tailTrace_8020849
  have hstable : (prefixWord ++ tailWord_8020849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020849).length < 2 ^ (prefixWord ++ tailWord_8020849).sum := by decide
  have hdescent : baseEnd_8020849 < baseStart_8020849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020872 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 7]
def baseStart_8020872 : Nat := 118140960795 + 8020872 * 2 ^ 59
def prefixEnd_8020872 : Nat := 4983230072969 + 3 ^ 40 * 8020872 * 2
def baseEnd_8020872 : Nat := 457618067132160837234743

theorem tailTrace_8020872 : CollatzResearch.WordTrace tailWord_8020872 prefixEnd_8020872 457618067132160837234743 := by
  unfold tailWord_8020872
  simp only [CollatzResearch.WordTrace]
  refine ⟨146272617698879037361456435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195030156931838716481941913 146272617698879037361456435)
  ·
    refine ⟨219408926548318556042184653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146272617698879037361456435 219408926548318556042184653)
    ·
      refine ⟨82278347455619458515819245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219408926548318556042184653 82278347455619458515819245)
      ·
        refine ⟨30854380295857296943432217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82278347455619458515819245 30854380295857296943432217)
        ·
          refine ⟨23140785221892972707574163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30854380295857296943432217 23140785221892972707574163)
          ·
            refine ⟨34711177832839459061361245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23140785221892972707574163 34711177832839459061361245)
            ·
              refine ⟨13016691687314797148010467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34711177832839459061361245 13016691687314797148010467)
              ·
                refine ⟨19525037530972195722015701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13016691687314797148010467 19525037530972195722015701)
                ·
                  refine ⟨457618067132160837234743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19525037530972195722015701 457618067132160837234743)
                  ·
                    rfl

theorem cell23_8020872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 7].length) (baseStart_8020872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020872 prefixEnd_8020872 := by exact prefixLift 8020872
  have htrace : WordTrace (prefixWord ++ tailWord_8020872) baseStart_8020872 baseEnd_8020872 := by
    simpa [prefixWord, tailWord_8020872, baseEnd_8020872] using wordTrace_append hprefix tailTrace_8020872
  have hstable : (prefixWord ++ tailWord_8020872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020872).length < 2 ^ (prefixWord ++ tailWord_8020872).sum := by decide
  have hdescent : baseEnd_8020872 < baseStart_8020872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020886 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8020886 : Nat := 118140960795 + 8020886 * 2 ^ 59
def prefixEnd_8020886 : Nat := 4983230072969 + 3 ^ 40 * 8020886 * 2
def baseEnd_8020886 : Nat := 4118569792918610480337623

theorem tailTrace_8020886 : CollatzResearch.WordTrace tailWord_8020886 prefixEnd_8020886 4118569792918610480337623 := by
  unfold tailWord_8020886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18284109126231709694620157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195030497346471570075948341 18284109126231709694620157)
  ·
    refine ⟨6856540922336891135482559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18284109126231709694620157 6856540922336891135482559)
    ·
      refine ⟨10284811383505336703223839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856540922336891135482559 10284811383505336703223839)
      ·
        refine ⟨15427217075258005054835759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284811383505336703223839 15427217075258005054835759)
        ·
          refine ⟨23140825612887007582253639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15427217075258005054835759 23140825612887007582253639)
          ·
            refine ⟨34711238419330511373380459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23140825612887007582253639 34711238419330511373380459)
            ·
              refine ⟨52066857628995767060070689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34711238419330511373380459 52066857628995767060070689)
              ·
                refine ⟨39050143221746825295053017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52066857628995767060070689 39050143221746825295053017)
                ·
                  refine ⟨29287607416310118971289763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39050143221746825295053017 29287607416310118971289763)
                  ·
                    refine ⟨43931411124465178456934645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29287607416310118971289763 43931411124465178456934645)
                    ·
                      refine ⟨4118569792918610480337623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43931411124465178456934645 4118569792918610480337623)
                      ·
                        rfl

theorem cell23_8020886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8020886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020886 prefixEnd_8020886 := by exact prefixLift 8020886
  have htrace : WordTrace (prefixWord ++ tailWord_8020886) baseStart_8020886 baseEnd_8020886 := by
    simpa [prefixWord, tailWord_8020886, baseEnd_8020886] using wordTrace_append hprefix tailTrace_8020886
  have hstable : (prefixWord ++ tailWord_8020886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020886).length < 2 ^ (prefixWord ++ tailWord_8020886).sum := by decide
  have hdescent : baseEnd_8020886 < baseStart_8020886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020922 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_8020922 : Nat := 118140960795 + 8020922 * 2 ^ 59
def prefixEnd_8020922 : Nat := 4983230072969 + 3 ^ 40 * 8020922 * 2
def baseEnd_8020922 : Nat := 4118588278222172339487457

theorem tailTrace_8020922 : CollatzResearch.WordTrace tailWord_8020922 prefixEnd_8020922 4118588278222172339487457 := by
  unfold tailWord_8020922
  simp only [CollatzResearch.WordTrace]
  refine ⟨73136764761894233315558255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195031372698384622174822013 73136764761894233315558255)
  ·
    refine ⟨109705147142841349973337383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73136764761894233315558255 109705147142841349973337383)
    ·
      refine ⟨164557720714262024960006075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109705147142841349973337383 164557720714262024960006075)
      ·
        refine ⟨246836581071393037440009113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164557720714262024960006075 246836581071393037440009113)
        ·
          refine ⟨185127435803544778080006835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246836581071393037440009113 185127435803544778080006835)
          ·
            refine ⟨277691153705317167120010253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185127435803544778080006835 277691153705317167120010253)
            ·
              refine ⟨104134182639493937670003845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277691153705317167120010253 104134182639493937670003845)
              ·
                refine ⟨19525159244905113313125721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104134182639493937670003845 19525159244905113313125721)
                ·
                  refine ⟨14643869433678834984844291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19525159244905113313125721 14643869433678834984844291)
                  ·
                    refine ⟨21965804150518252477266437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14643869433678834984844291 21965804150518252477266437)
                    ·
                      refine ⟨4118588278222172339487457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21965804150518252477266437 4118588278222172339487457)
                      ·
                        rfl

theorem cell23_8020922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_8020922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020922 prefixEnd_8020922 := by exact prefixLift 8020922
  have htrace : WordTrace (prefixWord ++ tailWord_8020922) baseStart_8020922 baseEnd_8020922 := by
    simpa [prefixWord, tailWord_8020922, baseEnd_8020922] using wordTrace_append hprefix tailTrace_8020922
  have hstable : (prefixWord ++ tailWord_8020922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020922).length < 2 ^ (prefixWord ++ tailWord_8020922).sum := by decide
  have hdescent : baseEnd_8020922 < baseStart_8020922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020939 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 2, 4, 2]
def baseStart_8020939 : Nat := 118140960795 + 8020939 * 2 ^ 59
def prefixEnd_8020939 : Nat := 4983230072969 + 3 ^ 40 * 8020939 * 2
def baseEnd_8020939 : Nat := 4118597007393298772974879

theorem tailTrace_8020939 : CollatzResearch.WordTrace tailWord_8020939 prefixEnd_8020939 4118597007393298772974879 := by
  unfold tailWord_8020939
  simp only [CollatzResearch.WordTrace]
  refine ⟨292547679088515345165601871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195031786059010230110401247 292547679088515345165601871)
  ·
    refine ⟨438821518632773017748402807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292547679088515345165601871 438821518632773017748402807)
    ·
      refine ⟨658232277949159526622604211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438821518632773017748402807 658232277949159526622604211)
      ·
        refine ⟨987348416923739289933906317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658232277949159526622604211 987348416923739289933906317)
        ·
          refine ⟨370255656346402233725214869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 987348416923739289933906317 370255656346402233725214869)
          ·
            refine ⟨17355733891237604705869447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 370255656346402233725214869 17355733891237604705869447)
            ·
              refine ⟨26033600836856407058804171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17355733891237604705869447 26033600836856407058804171)
              ·
                refine ⟨39050401255284610588206257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26033600836856407058804171 39050401255284610588206257)
                ·
                  refine ⟨29287800941463457941154693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39050401255284610588206257 29287800941463457941154693)
                  ·
                    refine ⟨5491462676524398363966505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29287800941463457941154693 5491462676524398363966505)
                    ·
                      refine ⟨4118597007393298772974879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491462676524398363966505 4118597007393298772974879)
                      ·
                        rfl

theorem cell23_8020939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4, 2].length) (baseStart_8020939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020939 prefixEnd_8020939 := by exact prefixLift 8020939
  have htrace : WordTrace (prefixWord ++ tailWord_8020939) baseStart_8020939 baseEnd_8020939 := by
    simpa [prefixWord, tailWord_8020939, baseEnd_8020939] using wordTrace_append hprefix tailTrace_8020939
  have hstable : (prefixWord ++ tailWord_8020939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020939).length < 2 ^ (prefixWord ++ tailWord_8020939).sum := by decide
  have hdescent : baseEnd_8020939 < baseStart_8020939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020959 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 3]
def baseStart_8020959 : Nat := 118140960795 + 8020959 * 2 ^ 59
def prefixEnd_8020959 : Nat := 4983230072969 + 3 ^ 40 * 8020959 * 2
def baseEnd_8020959 : Nat := 4118607277006388694724787

theorem tailTrace_8020959 : CollatzResearch.WordTrace tailWord_8020959 prefixEnd_8020959 4118607277006388694724787 := by
  unfold tailWord_8020959
  simp only [CollatzResearch.WordTrace]
  refine ⟨292548408548442888581329931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195032272365628592387553287 292548408548442888581329931)
  ·
    refine ⟨438822612822664332871994897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292548408548442888581329931 438822612822664332871994897)
    ·
      refine ⟨329116959616998249653996173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438822612822664332871994897 329116959616998249653996173)
      ·
        refine ⟨123418859856374343620248565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329116959616998249653996173 123418859856374343620248565)
        ·
          refine ⟨11570518111535094714398303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123418859856374343620248565 11570518111535094714398303)
          ·
            refine ⟨17355777167302642071597455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11570518111535094714398303 17355777167302642071597455)
            ·
              refine ⟨26033665750953963107396183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17355777167302642071597455 26033665750953963107396183)
              ·
                refine ⟨39050498626430944661094275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26033665750953963107396183 39050498626430944661094275)
                ·
                  refine ⟨58575747939646416991641413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39050498626430944661094275 58575747939646416991641413)
                  ·
                    refine ⟨10982952738683703185932765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58575747939646416991641413 10982952738683703185932765)
                    ·
                      refine ⟨4118607277006388694724787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10982952738683703185932765 4118607277006388694724787)
                      ·
                        rfl

theorem cell23_8020959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_8020959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020959 prefixEnd_8020959 := by exact prefixLift 8020959
  have htrace : WordTrace (prefixWord ++ tailWord_8020959) baseStart_8020959 baseEnd_8020959 := by
    simpa [prefixWord, tailWord_8020959, baseEnd_8020959] using wordTrace_append hprefix tailTrace_8020959
  have hstable : (prefixWord ++ tailWord_8020959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020959).length < 2 ^ (prefixWord ++ tailWord_8020959).sum := by decide
  have hdescent : baseEnd_8020959 < baseStart_8020959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020999 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_8020999 : Nat := 118140960795 + 8020999 * 2 ^ 59
def prefixEnd_8020999 : Nat := 4983230072969 + 3 ^ 40 * 8020999 * 2
def baseEnd_8020999 : Nat := 4118627816232568538224603

theorem tailTrace_8020999 : CollatzResearch.WordTrace tailWord_8020999 prefixEnd_8020999 4118627816232568538224603 := by
  unfold tailWord_8020999
  simp only [CollatzResearch.WordTrace]
  refine ⟨292549867468297975412786051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195033244978865316941857367 292549867468297975412786051)
  ·
    refine ⟨438824801202446963119179077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292549867468297975412786051 438824801202446963119179077)
    ·
      refine ⟨82279650225458805584846077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438824801202446963119179077 82279650225458805584846077)
      ·
        refine ⟨30854868834547052094317279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82279650225458805584846077 30854868834547052094317279)
        ·
          refine ⟨46282303251820578141475919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30854868834547052094317279 46282303251820578141475919)
          ·
            refine ⟨69423454877730867212213879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46282303251820578141475919 69423454877730867212213879)
            ·
              refine ⟨104135182316596300818320819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69423454877730867212213879 104135182316596300818320819)
              ·
                refine ⟨156202773474894451227481229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104135182316596300818320819 156202773474894451227481229)
                ·
                  refine ⟨58576040053085419210305461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156202773474894451227481229 58576040053085419210305461)
                  ·
                    refine ⟨5491503754976758050966137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58576040053085419210305461 5491503754976758050966137)
                    ·
                      refine ⟨4118627816232568538224603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491503754976758050966137 4118627816232568538224603)
                      ·
                        rfl

theorem cell23_8020999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_8020999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020999 prefixEnd_8020999 := by exact prefixLift 8020999
  have htrace : WordTrace (prefixWord ++ tailWord_8020999) baseStart_8020999 baseEnd_8020999 := by
    simpa [prefixWord, tailWord_8020999, baseEnd_8020999] using wordTrace_append hprefix tailTrace_8020999
  have hstable : (prefixWord ++ tailWord_8020999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020999).length < 2 ^ (prefixWord ++ tailWord_8020999).sum := by decide
  have hdescent : baseEnd_8020999 < baseStart_8020999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021006 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_8021006 : Nat := 118140960795 + 8021006 * 2 ^ 59
def prefixEnd_8021006 : Nat := 4983230072969 + 3 ^ 40 * 8021006 * 2
def baseEnd_8021006 : Nat := 4118631410597150010837071

theorem tailTrace_8021006 : CollatzResearch.WordTrace tailWord_8021006 prefixEnd_8021006 4118631410597150010837071 := by
  unfold tailWord_8021006
  simp only [CollatzResearch.WordTrace]
  refine ⟨36568765347409076951036359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195033415186181743738860581 36568765347409076951036359)
  ·
    refine ⟨54853148021113615426554539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36568765347409076951036359 54853148021113615426554539)
    ·
      refine ⟨82279722031670423139831809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54853148021113615426554539 82279722031670423139831809)
      ·
        refine ⟨61709791523752817354873857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82279722031670423139831809 61709791523752817354873857)
        ·
          refine ⟨46282343642814613016155393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61709791523752817354873857 46282343642814613016155393)
          ·
            refine ⟨34711757732110959762116545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46282343642814613016155393 34711757732110959762116545)
            ·
              refine ⟨26033818299083219821587409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34711757732110959762116545 26033818299083219821587409)
              ·
                refine ⟨19525363724312414866190557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26033818299083219821587409 19525363724312414866190557)
                ·
                  refine ⟨7322011396617155574821459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19525363724312414866190557 7322011396617155574821459)
                  ·
                    refine ⟨10983017094925733362232189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7322011396617155574821459 10983017094925733362232189)
                    ·
                      refine ⟨4118631410597150010837071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10983017094925733362232189 4118631410597150010837071)
                      ·
                        rfl

theorem cell23_8021006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_8021006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021006 prefixEnd_8021006 := by exact prefixLift 8021006
  have htrace : WordTrace (prefixWord ++ tailWord_8021006) baseStart_8021006 baseEnd_8021006 := by
    simpa [prefixWord, tailWord_8021006, baseEnd_8021006] using wordTrace_append hprefix tailTrace_8021006
  have hstable : (prefixWord ++ tailWord_8021006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021006).length < 2 ^ (prefixWord ++ tailWord_8021006).sum := by decide
  have hdescent : baseEnd_8021006 < baseStart_8021006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021023 : List Nat := [1, 1, 2, 4, 1, 3, 3, 3, 1, 1, 3]
def baseStart_8021023 : Nat := 118140960795 + 8021023 * 2 ^ 59
def prefixEnd_8021023 : Nat := 4983230072969 + 3 ^ 40 * 8021023 * 2
def baseEnd_8021023 : Nat := 4118640139768276444324493

theorem tailTrace_8021023 : CollatzResearch.WordTrace tailWord_8021023 prefixEnd_8021023 4118640139768276444324493 := by
  unfold tailWord_8021023
  simp only [CollatzResearch.WordTrace]
  refine ⟨292550742820211027511659723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195033828546807351674439815 292550742820211027511659723)
  ·
    refine ⟨438826114230316541267489585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292550742820211027511659723 438826114230316541267489585)
    ·
      refine ⟨329119585672737405950617189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438826114230316541267489585 329119585672737405950617189)
      ·
        refine ⟨61709922313638263615740723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329119585672737405950617189 61709922313638263615740723)
        ·
          refine ⟨92564883470457395423611085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61709922313638263615740723 92564883470457395423611085)
          ·
            refine ⟨34711831301421523283854157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92564883470457395423611085 34711831301421523283854157)
            ·
              refine ⟨13016936738033071231445309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34711831301421523283854157 13016936738033071231445309)
              ·
                refine ⟨4881351276762401711791991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13016936738033071231445309 4881351276762401711791991)
                ·
                  refine ⟨7322026915143602567687987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881351276762401711791991 7322026915143602567687987)
                  ·
                    refine ⟨10983040372715403851531981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7322026915143602567687987 10983040372715403851531981)
                    ·
                      refine ⟨4118640139768276444324493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10983040372715403851531981 4118640139768276444324493)
                      ·
                        rfl

theorem cell23_8021023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_8021023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021023 prefixEnd_8021023 := by exact prefixLift 8021023
  have htrace : WordTrace (prefixWord ++ tailWord_8021023) baseStart_8021023 baseEnd_8021023 := by
    simpa [prefixWord, tailWord_8021023, baseEnd_8021023] using wordTrace_append hprefix tailTrace_8021023
  have hstable : (prefixWord ++ tailWord_8021023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021023).length < 2 ^ (prefixWord ++ tailWord_8021023).sum := by decide
  have hdescent : baseEnd_8021023 < baseStart_8021023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021029 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_8021029 : Nat := 118140960795 + 8021029 * 2 ^ 59
def prefixEnd_8021029 : Nat := 4983230072969 + 3 ^ 40 * 8021029 * 2
def baseEnd_8021029 : Nat := 4118643220652203420849465

theorem tailTrace_8021029 : CollatzResearch.WordTrace tailWord_8021029 prefixEnd_8021029 4118643220652203420849465 := by
  unfold tailWord_8021029
  simp only [CollatzResearch.WordTrace]
  refine ⟨292550961658189290536378141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195033974438792860357585427 292550961658189290536378141)
  ·
    refine ⟨109706610621820983951141803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292550961658189290536378141 109706610621820983951141803)
    ·
      refine ⟨164559915932731475926712705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109706610621820983951141803 164559915932731475926712705)
      ·
        refine ⟨123419936949548606945034529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164559915932731475926712705 123419936949548606945034529)
        ·
          refine ⟨92564952712161455208775897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123419936949548606945034529 92564952712161455208775897)
          ·
            refine ⟨69423714534121091406581923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92564952712161455208775897 69423714534121091406581923)
            ·
              refine ⟨104135571801181637109872885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69423714534121091406581923 104135571801181637109872885)
              ·
                refine ⟨9762709856360778479050583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104135571801181637109872885 9762709856360778479050583)
                ·
                  refine ⟨14644064784541167718575875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9762709856360778479050583 14644064784541167718575875)
                  ·
                    refine ⟨21966097176811751577863813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14644064784541167718575875 21966097176811751577863813)
                    ·
                      refine ⟨4118643220652203420849465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21966097176811751577863813 4118643220652203420849465)
                      ·
                        rfl

theorem cell23_8021029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_8021029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021029 prefixEnd_8021029 := by exact prefixLift 8021029
  have htrace : WordTrace (prefixWord ++ tailWord_8021029) baseStart_8021029 baseEnd_8021029 := by
    simpa [prefixWord, tailWord_8021029, baseEnd_8021029] using wordTrace_append hprefix tailTrace_8021029
  have hstable : (prefixWord ++ tailWord_8021029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021029).length < 2 ^ (prefixWord ++ tailWord_8021029).sum := by decide
  have hdescent : baseEnd_8021029 < baseStart_8021029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021042 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_8021042 : Nat := 118140960795 + 8021042 * 2 ^ 59
def prefixEnd_8021042 : Nat := 4983230072969 + 3 ^ 40 * 8021042 * 2
def baseEnd_8021042 : Nat := 4118649895900711869986905

theorem tailTrace_8021042 : CollatzResearch.WordTrace tailWord_8021042 prefixEnd_8021042 4118649895900711869986905 := by
  unfold tailWord_8021042
  simp only [CollatzResearch.WordTrace]
  refine ⟨73137858951785548439150345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195034290538094795837734253 73137858951785548439150345)
  ·
    refine ⟨54853394213839161329362759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73137858951785548439150345 54853394213839161329362759)
    ·
      refine ⟨82280091320758741994044139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54853394213839161329362759 82280091320758741994044139)
      ·
        refine ⟨123420136981138112991066209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82280091320758741994044139 123420136981138112991066209)
        ·
          refine ⟨92565102735853584743299657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123420136981138112991066209 92565102735853584743299657)
          ·
            refine ⟨69423827051890188557474743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92565102735853584743299657 69423827051890188557474743)
            ·
              refine ⟨104135740577835282836212115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69423827051890188557474743 104135740577835282836212115)
              ·
                refine ⟨156203610866752924254318173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104135740577835282836212115 156203610866752924254318173)
                ·
                  refine ⟨58576354075032346595369315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156203610866752924254318173 58576354075032346595369315)
                  ·
                    refine ⟨87864531112548519893053973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58576354075032346595369315 87864531112548519893053973)
                    ·
                      refine ⟨4118649895900711869986905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87864531112548519893053973 4118649895900711869986905)
                      ·
                        rfl

theorem cell23_8021042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_8021042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021042 prefixEnd_8021042 := by exact prefixLift 8021042
  have htrace : WordTrace (prefixWord ++ tailWord_8021042) baseStart_8021042 baseEnd_8021042 := by
    simpa [prefixWord, tailWord_8021042, baseEnd_8021042] using wordTrace_append hprefix tailTrace_8021042
  have hstable : (prefixWord ++ tailWord_8021042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021042).length < 2 ^ (prefixWord ++ tailWord_8021042).sum := by decide
  have hdescent : baseEnd_8021042 < baseStart_8021042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021049 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_8021049 : Nat := 118140960795 + 8021049 * 2 ^ 59
def prefixEnd_8021049 : Nat := 4983230072969 + 3 ^ 40 * 8021049 * 2
def baseEnd_8021049 : Nat := 4118653490265293342599373

theorem tailTrace_8021049 : CollatzResearch.WordTrace tailWord_8021049 prefixEnd_8021049 4118653490265293342599373 := by
  unfold tailWord_8021049
  simp only [CollatzResearch.WordTrace]
  refine ⟨292551691118116833952106201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195034460745411222634737467 292551691118116833952106201)
  ·
    refine ⟨219413768338587625464079651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292551691118116833952106201 219413768338587625464079651)
    ·
      refine ⟨329120652507881438196119477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219413768338587625464079651 329120652507881438196119477)
      ·
        refine ⟨30855061172613884830886201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329120652507881438196119477 30855061172613884830886201)
        ·
          refine ⟨23141295879460413623164651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30855061172613884830886201 23141295879460413623164651)
          ·
            refine ⟨34711943819190620434746977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23141295879460413623164651 34711943819190620434746977)
            ·
              refine ⟨26033957864392965326060233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34711943819190620434746977 26033957864392965326060233)
              ·
                refine ⟨19525468398294723994545175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26033957864392965326060233 19525468398294723994545175)
                ·
                  refine ⟨29288202597442085991817763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19525468398294723994545175 29288202597442085991817763)
                  ·
                    refine ⟨43932303896163128987726645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29288202597442085991817763 43932303896163128987726645)
                    ·
                      refine ⟨4118653490265293342599373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43932303896163128987726645 4118653490265293342599373)
                      ·
                        rfl

theorem cell23_8021049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_8021049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021049 prefixEnd_8021049 := by exact prefixLift 8021049
  have htrace : WordTrace (prefixWord ++ tailWord_8021049) baseStart_8021049 baseEnd_8021049 := by
    simpa [prefixWord, tailWord_8021049, baseEnd_8021049] using wordTrace_append hprefix tailTrace_8021049
  have hstable : (prefixWord ++ tailWord_8021049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021049).length < 2 ^ (prefixWord ++ tailWord_8021049).sum := by decide
  have hdescent : baseEnd_8021049 < baseStart_8021049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021052 : List Nat := [2, 2, 2, 2, 2, 2, 1, 10]
def baseStart_8021052 : Nat := 118140960795 + 8021052 * 2 ^ 59
def prefixEnd_8021052 : Nat := 4983230072969 + 3 ^ 40 * 8021052 * 2
def baseEnd_8021052 : Nat := 152542778915083586328217

theorem tailTrace_8021052 : CollatzResearch.WordTrace tailWord_8021052 prefixEnd_8021052 152542778915083586328217 := by
  unfold tailWord_8021052
  simp only [CollatzResearch.WordTrace]
  refine ⟨146275900268552982732232705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195034533691403976976310273 146275900268552982732232705)
  ·
    refine ⟨109706925201414737049174529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146275900268552982732232705 109706925201414737049174529)
    ·
      refine ⟨82280193901061052786880897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109706925201414737049174529 82280193901061052786880897)
      ·
        refine ⟨61710145425795789590160673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82280193901061052786880897 61710145425795789590160673)
        ·
          refine ⟨46282609069346842192620505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61710145425795789590160673 46282609069346842192620505)
          ·
            refine ⟨34711956802010131644465379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46282609069346842192620505 34711956802010131644465379)
            ·
              refine ⟨52067935203015197466698069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34711956802010131644465379 52067935203015197466698069)
              ·
                refine ⟨152542778915083586328217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52067935203015197466698069 152542778915083586328217)
                ·
                  rfl

theorem cell23_8021052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 10].length) (baseStart_8021052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021052 prefixEnd_8021052 := by exact prefixLift 8021052
  have htrace : WordTrace (prefixWord ++ tailWord_8021052) baseStart_8021052 baseEnd_8021052 := by
    simpa [prefixWord, tailWord_8021052, baseEnd_8021052] using wordTrace_append hprefix tailTrace_8021052
  have hstable : (prefixWord ++ tailWord_8021052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021052).length < 2 ^ (prefixWord ++ tailWord_8021052).sum := by decide
  have hdescent : baseEnd_8021052 < baseStart_8021052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021066 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_8021066 : Nat := 118140960795 + 8021066 * 2 ^ 59
def prefixEnd_8021066 : Nat := 4983230072969 + 3 ^ 40 * 8021066 * 2
def baseEnd_8021066 : Nat := 4118662219436419776086795

theorem tailTrace_8021066 : CollatzResearch.WordTrace tailWord_8021066 prefixEnd_8021066 4118662219436419776086795 := by
  unfold tailWord_8021066
  simp only [CollatzResearch.WordTrace]
  refine ⟨73138077789763811463868763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195034874106036830570316701 73138077789763811463868763)
  ·
    refine ⟨109707116684645717195803145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73138077789763811463868763 109707116684645717195803145)
    ·
      refine ⟨82280337513484287896852359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109707116684645717195803145 82280337513484287896852359)
      ·
        refine ⟨123420506270226431845278539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82280337513484287896852359 123420506270226431845278539)
        ·
          refine ⟨185130759405339647767917809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123420506270226431845278539 185130759405339647767917809)
          ·
            refine ⟨138848069554004735825938357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185130759405339647767917809 138848069554004735825938357)
            ·
              refine ⟨13017006520687943983681721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138848069554004735825938357 13017006520687943983681721)
              ·
                refine ⟨9762754890515957987761291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13017006520687943983681721 9762754890515957987761291)
                ·
                  refine ⟨14644132335773936981641937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9762754890515957987761291 14644132335773936981641937)
                  ·
                    refine ⟨10983099251830452736231453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14644132335773936981641937 10983099251830452736231453)
                    ·
                      refine ⟨4118662219436419776086795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10983099251830452736231453 4118662219436419776086795)
                      ·
                        rfl

theorem cell23_8021066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_8021066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021066 prefixEnd_8021066 := by exact prefixLift 8021066
  have htrace : WordTrace (prefixWord ++ tailWord_8021066) baseStart_8021066 baseEnd_8021066 := by
    simpa [prefixWord, tailWord_8021066, baseEnd_8021066] using wordTrace_append hprefix tailTrace_8021066
  have hstable : (prefixWord ++ tailWord_8021066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021066).length < 2 ^ (prefixWord ++ tailWord_8021066).sum := by decide
  have hdescent : baseEnd_8021066 < baseStart_8021066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021069 : List Nat := [1, 6, 1, 1, 1, 2, 2, 9]
def baseStart_8021069 : Nat := 118140960795 + 8021069 * 2 ^ 59
def prefixEnd_8021069 : Nat := 4983230072969 + 3 ^ 40 * 8021069 * 2
def baseEnd_8021069 : Nat := 152543102217717898679603

theorem tailTrace_8021069 : CollatzResearch.WordTrace tailWord_8021069 prefixEnd_8021069 152543102217717898679603 := by
  unfold tailWord_8021069
  simp only [CollatzResearch.WordTrace]
  refine ⟨292552420578044377367834261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195034947052029584911889507 292552420578044377367834261)
  ·
    refine ⟨13713394714595830189117231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292552420578044377367834261 13713394714595830189117231)
    ·
      refine ⟨20570092071893745283675847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13713394714595830189117231 20570092071893745283675847)
      ·
        refine ⟨30855138107840617925513771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20570092071893745283675847 30855138107840617925513771)
        ·
          refine ⟨46282707161760926888270657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30855138107840617925513771 46282707161760926888270657)
          ·
            refine ⟨34712030371320695166202993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46282707161760926888270657 34712030371320695166202993)
            ·
              refine ⟨26034022778490521374652245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34712030371320695166202993 26034022778490521374652245)
              ·
                refine ⟨152543102217717898679603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26034022778490521374652245 152543102217717898679603)
                ·
                  rfl

theorem cell23_8021069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 9].length) (baseStart_8021069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021069 prefixEnd_8021069 := by exact prefixLift 8021069
  have htrace : WordTrace (prefixWord ++ tailWord_8021069) baseStart_8021069 baseEnd_8021069 := by
    simpa [prefixWord, tailWord_8021069, baseEnd_8021069] using wordTrace_append hprefix tailTrace_8021069
  have hstable : (prefixWord ++ tailWord_8021069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021069).length < 2 ^ (prefixWord ++ tailWord_8021069).sum := by decide
  have hdescent : baseEnd_8021069 < baseStart_8021069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021086 : List Nat := [4, 4, 1, 1, 1, 12]
def baseStart_8021086 : Nat := 118140960795 + 8021086 * 2 ^ 59
def prefixEnd_8021086 : Nat := 4983230072969 + 3 ^ 40 * 8021086 * 2
def baseEnd_8021086 : Nat := 16949269502261356781221

theorem tailTrace_8021086 : CollatzResearch.WordTrace tailWord_8021086 prefixEnd_8021086 16949269502261356781221 := by
  unfold tailWord_8021086
  simp only [CollatzResearch.WordTrace]
  refine ⟨36569130077372848658900389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195035360412655192847468741 36569130077372848658900389)
  ·
    refine ⟨6856711889507409123543823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36569130077372848658900389 6856711889507409123543823)
    ·
      refine ⟨10285067834261113685315735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856711889507409123543823 10285067834261113685315735)
      ·
        refine ⟨15427601751391670527973603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285067834261113685315735 15427601751391670527973603)
        ·
          refine ⟨23141402627087505791960405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15427601751391670527973603 23141402627087505791960405)
          ·
            refine ⟨16949269502261356781221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23141402627087505791960405 16949269502261356781221)
            ·
              rfl

theorem cell23_8021086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 12].length) (baseStart_8021086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021086 prefixEnd_8021086 := by exact prefixLift 8021086
  have htrace : WordTrace (prefixWord ++ tailWord_8021086) baseStart_8021086 baseEnd_8021086 := by
    simpa [prefixWord, tailWord_8021086, baseEnd_8021086] using wordTrace_append hprefix tailTrace_8021086
  have hstable : (prefixWord ++ tailWord_8021086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021086).length < 2 ^ (prefixWord ++ tailWord_8021086).sum := by decide
  have hdescent : baseEnd_8021086 < baseStart_8021086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021097 : List Nat := [1, 2, 1, 1, 1, 8, 2, 2, 1, 2, 2]
def baseStart_8021097 : Nat := 118140960795 + 8021097 * 2 ^ 59
def prefixEnd_8021097 : Nat := 4983230072969 + 3 ^ 40 * 8021097 * 2
def baseEnd_8021097 : Nat := 4118678137336709154799153

theorem tailTrace_8021097 : CollatzResearch.WordTrace tailWord_8021097 prefixEnd_8021097 4118678137336709154799153 := by
  unfold tailWord_8021097
  simp only [CollatzResearch.WordTrace]
  refine ⟨292553441821942938149853545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195035627881295292099902363 292553441821942938149853545)
  ·
    refine ⟨219415081366457203612390159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292553441821942938149853545 219415081366457203612390159)
    ·
      refine ⟨329122622049685805418585239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219415081366457203612390159 329122622049685805418585239)
      ·
        refine ⟨493683933074528708127877859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329122622049685805418585239 493683933074528708127877859)
        ·
          refine ⟨740525899611793062191816789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493683933074528708127877859 740525899611793062191816789)
          ·
            refine ⟨8678037886075699947560353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 740525899611793062191816789 8678037886075699947560353)
            ·
              refine ⟨6508528414556774960670265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8678037886075699947560353 6508528414556774960670265)
              ·
                refine ⟨4881396310917581220502699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6508528414556774960670265 4881396310917581220502699)
                ·
                  refine ⟨7322094466376371830754049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881396310917581220502699 7322094466376371830754049)
                  ·
                    refine ⟨5491570849782278873065537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7322094466376371830754049 5491570849782278873065537)
                    ·
                      refine ⟨4118678137336709154799153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491570849782278873065537 4118678137336709154799153)
                      ·
                        rfl

theorem cell23_8021097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 2, 2].length) (baseStart_8021097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021097 prefixEnd_8021097 := by exact prefixLift 8021097
  have htrace : WordTrace (prefixWord ++ tailWord_8021097) baseStart_8021097 baseEnd_8021097 := by
    simpa [prefixWord, tailWord_8021097, baseEnd_8021097] using wordTrace_append hprefix tailTrace_8021097
  have hstable : (prefixWord ++ tailWord_8021097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021097).length < 2 ^ (prefixWord ++ tailWord_8021097).sum := by decide
  have hdescent : baseEnd_8021097 < baseStart_8021097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021106 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_8021106 : Nat := 118140960795 + 8021106 * 2 ^ 59
def prefixEnd_8021106 : Nat := 4983230072969 + 3 ^ 40 * 8021106 * 2
def baseEnd_8021106 : Nat := 4118682758662599619586611

theorem tailTrace_8021106 : CollatzResearch.WordTrace tailWord_8021106 prefixEnd_8021106 4118682758662599619586611 := by
  unfold tailWord_8021106
  simp only [CollatzResearch.WordTrace]
  refine ⟨73138442519727583171732793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195035846719273555124620781 73138442519727583171732793)
  ·
    refine ⟨54853831889795687378799595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73138442519727583171732793 54853831889795687378799595)
    ·
      refine ⟨82280747834693531068199393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54853831889795687378799595 82280747834693531068199393)
      ·
        refine ⟨61710560876020148301149545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82280747834693531068199393 61710560876020148301149545)
        ·
          refine ⟨46282920657015111225862159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61710560876020148301149545 46282920657015111225862159)
          ·
            refine ⟨69424380985522666838793239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46282920657015111225862159 69424380985522666838793239)
            ·
              refine ⟨104136571478284000258189859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69424380985522666838793239 104136571478284000258189859)
              ·
                refine ⟨156204857217426000387284789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104136571478284000258189859 156204857217426000387284789)
                ·
                  refine ⟨14644205364133687536307949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156204857217426000387284789 14644205364133687536307949)
                  ·
                    refine ⟨5491577011550132826115481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14644205364133687536307949 5491577011550132826115481)
                    ·
                      refine ⟨4118682758662599619586611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491577011550132826115481 4118682758662599619586611)
                      ·
                        rfl

theorem cell23_8021106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_8021106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021106 prefixEnd_8021106 := by exact prefixLift 8021106
  have htrace : WordTrace (prefixWord ++ tailWord_8021106) baseStart_8021106 baseEnd_8021106 := by
    simpa [prefixWord, tailWord_8021106, baseEnd_8021106] using wordTrace_append hprefix tailTrace_8021106
  have hstable : (prefixWord ++ tailWord_8021106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021106).length < 2 ^ (prefixWord ++ tailWord_8021106).sum := by decide
  have hdescent : baseEnd_8021106 < baseStart_8021106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021112 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 1, 8]
def baseStart_8021112 : Nat := 118140960795 + 8021112 * 2 ^ 59
def prefixEnd_8021112 : Nat := 4983230072969 + 3 ^ 40 * 8021112 * 2
def baseEnd_8021112 : Nat := 1372895279848842198703861

theorem tailTrace_8021112 : CollatzResearch.WordTrace tailWord_8021112 prefixEnd_8021112 1372895279848842198703861 := by
  unfold tailWord_8021112
  simp only [CollatzResearch.WordTrace]
  refine ⟨146276994458444297855824795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195035992611259063807766393 146276994458444297855824795)
  ·
    refine ⟨219415491687666446783737193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146276994458444297855824795 219415491687666446783737193)
    ·
      refine ⟨164561618765749835087802895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219415491687666446783737193 164561618765749835087802895)
      ·
        refine ⟨246842428148624752631704343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164561618765749835087802895 246842428148624752631704343)
        ·
          refine ⟨370263642222937128947556515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246842428148624752631704343 370263642222937128947556515)
          ·
            refine ⟨555395463334405693421334773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370263642222937128947556515 555395463334405693421334773)
            ·
              refine ⟨52068324687600533758250135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 555395463334405693421334773 52068324687600533758250135)
              ·
                refine ⟨78102487031400800637375203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52068324687600533758250135 78102487031400800637375203)
                ·
                  refine ⟨117153730547101200956062805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78102487031400800637375203 117153730547101200956062805)
                  ·
                    refine ⟨1372895279848842198703861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117153730547101200956062805 1372895279848842198703861)
                    ·
                      rfl

theorem cell23_8021112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_8021112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021112 prefixEnd_8021112 := by exact prefixLift 8021112
  have htrace : WordTrace (prefixWord ++ tailWord_8021112) baseStart_8021112 baseEnd_8021112 := by
    simpa [prefixWord, tailWord_8021112, baseEnd_8021112] using wordTrace_append hprefix tailTrace_8021112
  have hstable : (prefixWord ++ tailWord_8021112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021112).length < 2 ^ (prefixWord ++ tailWord_8021112).sum := by decide
  have hdescent : baseEnd_8021112 < baseStart_8021112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021149 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_8021149 : Nat := 118140960795 + 8021149 * 2 ^ 59
def prefixEnd_8021149 : Nat := 4983230072969 + 3 ^ 40 * 8021149 * 2
def baseEnd_8021149 : Nat := 4118704838330742951348913

theorem tailTrace_8021149 : CollatzResearch.WordTrace tailWord_8021149 prefixEnd_8021149 4118704838330742951348913 := by
  unfold tailWord_8021149
  simp only [CollatzResearch.WordTrace]
  refine ⟨292555338417754551030746501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195036892278503034020497667 292555338417754551030746501)
  ·
    refine ⟨54854125953328978318264969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292555338417754551030746501 54854125953328978318264969)
    ·
      refine ⟨41140594464996733738698727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54854125953328978318264969 41140594464996733738698727)
      ·
        refine ⟨61710891697495100608048091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41140594464996733738698727 61710891697495100608048091)
        ·
          refine ⟨92566337546242650912072137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61710891697495100608048091 92566337546242650912072137)
          ·
            refine ⟨69424753159681988184054103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92566337546242650912072137 69424753159681988184054103)
            ·
              refine ⟨104137129739522982276081155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69424753159681988184054103 104137129739522982276081155)
              ·
                refine ⟨156205694609284473414121733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104137129739522982276081155 156205694609284473414121733)
                ·
                  refine ⟨29288567739240838765147825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156205694609284473414121733 29288567739240838765147825)
                  ·
                    refine ⟨21966425804430629073860869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29288567739240838765147825 21966425804430629073860869)
                    ·
                      refine ⟨4118704838330742951348913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21966425804430629073860869 4118704838330742951348913)
                      ·
                        rfl

theorem cell23_8021149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_8021149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021149 prefixEnd_8021149 := by exact prefixLift 8021149
  have htrace : WordTrace (prefixWord ++ tailWord_8021149) baseStart_8021149 baseEnd_8021149 := by
    simpa [prefixWord, tailWord_8021149, baseEnd_8021149] using wordTrace_append hprefix tailTrace_8021149
  have hstable : (prefixWord ++ tailWord_8021149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021149).length < 2 ^ (prefixWord ++ tailWord_8021149).sum := by decide
  have hdescent : baseEnd_8021149 < baseStart_8021149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021153 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_8021153 : Nat := 118140960795 + 8021153 * 2 ^ 59
def prefixEnd_8021153 : Nat := 4983230072969 + 3 ^ 40 * 8021153 * 2
def baseEnd_8021153 : Nat := 4118706892253360935698895

theorem tailTrace_8021153 : CollatzResearch.WordTrace tailWord_8021153 prefixEnd_8021153 4118706892253360935698895 := by
  unfold tailWord_8021153
  simp only [CollatzResearch.WordTrace]
  refine ⟨292555484309740059713892113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195036989539826706475928075 292555484309740059713892113)
  ·
    refine ⟨219416613232305044785419085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292555484309740059713892113 219416613232305044785419085)
    ·
      refine ⟨82281229962114391794532157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219416613232305044785419085 82281229962114391794532157)
      ·
        refine ⟨30855461235792896922949559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82281229962114391794532157 30855461235792896922949559)
        ·
          refine ⟨46283191853689345384424339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30855461235792896922949559 46283191853689345384424339)
          ·
            refine ⟨69424787780534018076636509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46283191853689345384424339 69424787780534018076636509)
            ·
              refine ⟨26034295417700256778738691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69424787780534018076636509 26034295417700256778738691)
              ·
                refine ⟨39051443126550385168108037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26034295417700256778738691 39051443126550385168108037)
                ·
                  refine ⟨7322145586228197219020257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39051443126550385168108037 7322145586228197219020257)
                  ·
                    refine ⟨5491609189671147914265193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7322145586228197219020257 5491609189671147914265193)
                    ·
                      refine ⟨4118706892253360935698895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491609189671147914265193 4118706892253360935698895)
                      ·
                        rfl

theorem cell23_8021153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_8021153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021153 prefixEnd_8021153 := by exact prefixLift 8021153
  have htrace : WordTrace (prefixWord ++ tailWord_8021153) baseStart_8021153 baseEnd_8021153 := by
    simpa [prefixWord, tailWord_8021153, baseEnd_8021153] using wordTrace_append hprefix tailTrace_8021153
  have hstable : (prefixWord ++ tailWord_8021153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021153).length < 2 ^ (prefixWord ++ tailWord_8021153).sum := by decide
  have hdescent : baseEnd_8021153 < baseStart_8021153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021174 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_8021174 : Nat := 118140960795 + 8021174 * 2 ^ 59
def prefixEnd_8021174 : Nat := 4983230072969 + 3 ^ 40 * 8021174 * 2
def baseEnd_8021174 : Nat := 4118717675347105353536299

theorem tailTrace_8021174 : CollatzResearch.WordTrace tailWord_8021174 prefixEnd_8021174 4118717675347105353536299 := by
  unfold tailWord_8021174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18284765640166498768775411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195037500161775986866937717 18284765640166498768775411)
  ·
    refine ⟨27427148460249748153163117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18284765640166498768775411 27427148460249748153163117)
    ·
      refine ⟨10285180672593655557436169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27427148460249748153163117 10285180672593655557436169)
      ·
        refine ⟨7713885504445241668077127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10285180672593655557436169 7713885504445241668077127)
        ·
          refine ⟨11570828256667862502115691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713885504445241668077127 11570828256667862502115691)
          ·
            refine ⟨17356242385001793753173537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11570828256667862502115691 17356242385001793753173537)
            ·
              refine ⟨13017181788751345314880153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17356242385001793753173537 13017181788751345314880153)
              ·
                refine ⟨9762886341563508986160115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13017181788751345314880153 9762886341563508986160115)
                ·
                  refine ⟨14644329512345263479240173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9762886341563508986160115 14644329512345263479240173)
                  ·
                    refine ⟨5491623567129473804715065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14644329512345263479240173 5491623567129473804715065)
                    ·
                      refine ⟨4118717675347105353536299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491623567129473804715065 4118717675347105353536299)
                      ·
                        rfl

theorem cell23_8021174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_8021174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021174 prefixEnd_8021174 := by exact prefixLift 8021174
  have htrace : WordTrace (prefixWord ++ tailWord_8021174) baseStart_8021174 baseEnd_8021174 := by
    simpa [prefixWord, tailWord_8021174, baseEnd_8021174] using wordTrace_append hprefix tailTrace_8021174
  have hstable : (prefixWord ++ tailWord_8021174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021174).length < 2 ^ (prefixWord ++ tailWord_8021174).sum := by decide
  have hdescent : baseEnd_8021174 < baseStart_8021174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021189 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_8021189 : Nat := 118140960795 + 8021189 * 2 ^ 59
def prefixEnd_8021189 : Nat := 4983230072969 + 3 ^ 40 * 8021189 * 2
def baseEnd_8021189 : Nat := 1372908459185640931616243

theorem tailTrace_8021189 : CollatzResearch.WordTrace tailWord_8021189 prefixEnd_8021189 1372908459185640931616243 := by
  unfold tailWord_8021189
  simp only [CollatzResearch.WordTrace]
  refine ⟨292556797337609637862202621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195037864891739758574801747 292556797337609637862202621)
  ·
    refine ⟨109708799001603614198325983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292556797337609637862202621 109708799001603614198325983)
    ·
      refine ⟨164563198502405421297488975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109708799001603614198325983 164563198502405421297488975)
      ·
        refine ⟨246844797753608131946233463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164563198502405421297488975 246844797753608131946233463)
        ·
          refine ⟨370267196630412197919350195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246844797753608131946233463 370267196630412197919350195)
          ·
            refine ⟨555400794945618296879025293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370267196630412197919350195 555400794945618296879025293)
            ·
              refine ⟨208275298104606861329634485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555400794945618296879025293 208275298104606861329634485)
              ·
                refine ⟨19525809197306893249653233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208275298104606861329634485 19525809197306893249653233)
                ·
                  refine ⟨14644356897980169937239925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19525809197306893249653233 14644356897980169937239925)
                  ·
                    refine ⟨1372908459185640931616243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14644356897980169937239925 1372908459185640931616243)
                    ·
                      rfl

theorem cell23_8021189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_8021189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021189 prefixEnd_8021189 := by exact prefixLift 8021189
  have htrace : WordTrace (prefixWord ++ tailWord_8021189) baseStart_8021189 baseEnd_8021189 := by
    simpa [prefixWord, tailWord_8021189, baseEnd_8021189] using wordTrace_append hprefix tailTrace_8021189
  have hstable : (prefixWord ++ tailWord_8021189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021189).length < 2 ^ (prefixWord ++ tailWord_8021189).sum := by decide
  have hdescent : baseEnd_8021189 < baseStart_8021189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021253 : List Nat := [1, 3, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_8021253 : Nat := 118140960795 + 8021253 * 2 ^ 59
def prefixEnd_8021253 : Nat := 4983230072969 + 3 ^ 40 * 8021253 * 2
def baseEnd_8021253 : Nat := 1372919413439603514816145

theorem tailTrace_8021253 : CollatzResearch.WordTrace tailWord_8021253 prefixEnd_8021253 1372919413439603514816145 := by
  unfold tailWord_8021253
  simp only [CollatzResearch.WordTrace]
  refine ⟨292559131609377776792532413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195039421072918517861688275 292559131609377776792532413)
  ·
    refine ⟨109709674353516666297199655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292559131609377776792532413 109709674353516666297199655)
    ·
      refine ⟨164564511530274999445799483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109709674353516666297199655 164564511530274999445799483)
      ·
        refine ⟨246846767295412499168699225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164564511530274999445799483 246846767295412499168699225)
        ·
          refine ⟨185135075471559374376524419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246846767295412499168699225 185135075471559374376524419)
          ·
            refine ⟨277702613207339061564786629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185135075471559374376524419 277702613207339061564786629)
            ·
              refine ⟨52069239976376074043397493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277702613207339061564786629 52069239976376074043397493)
              ·
                refine ⟨4881491247785256941568515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52069239976376074043397493 4881491247785256941568515)
                ·
                  refine ⟨7322236871677885412352773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881491247785256941568515 7322236871677885412352773)
                  ·
                    refine ⟨1372919413439603514816145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7322236871677885412352773 1372919413439603514816145)
                    ·
                      rfl

theorem cell23_8021253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_8021253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021253 prefixEnd_8021253 := by exact prefixLift 8021253
  have htrace : WordTrace (prefixWord ++ tailWord_8021253) baseStart_8021253 baseEnd_8021253 := by
    simpa [prefixWord, tailWord_8021253, baseEnd_8021253] using wordTrace_append hprefix tailTrace_8021253
  have hstable : (prefixWord ++ tailWord_8021253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021253).length < 2 ^ (prefixWord ++ tailWord_8021253).sum := by decide
  have hdescent : baseEnd_8021253 < baseStart_8021253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021269 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_8021269 : Nat := 118140960795 + 8021269 * 2 ^ 59
def prefixEnd_8021269 : Nat := 4983230072969 + 3 ^ 40 * 8021269 * 2
def baseEnd_8021269 : Nat := 4118766456009282481848361

theorem tailTrace_8021269 : CollatzResearch.WordTrace tailWord_8021269 prefixEnd_8021269 4118766456009282481848361 := by
  unfold tailWord_8021269
  simp only [CollatzResearch.WordTrace]
  refine ⟨292559715177319811525114861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195039810118213207683409907 292559715177319811525114861)
  ·
    refine ⟨109709893191494929321918073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292559715177319811525114861 109709893191494929321918073)
    ·
      refine ⟨82282419893621196991438555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109709893191494929321918073 82282419893621196991438555)
      ·
        refine ⟨123423629840431795487157833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82282419893621196991438555 123423629840431795487157833)
        ·
          refine ⟨92567722380323846615368375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123423629840431795487157833 92567722380323846615368375)
          ·
            refine ⟨138851583570485769923052563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92567722380323846615368375 138851583570485769923052563)
            ·
              refine ⟨208277375355728654884578845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138851583570485769923052563 208277375355728654884578845)
              ·
                refine ⟨78104015758398245581717067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208277375355728654884578845 78104015758398245581717067)
                ·
                  refine ⟨117156023637597368372575601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78104015758398245581717067 117156023637597368372575601)
                  ·
                    refine ⟨87867017728198026279431701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117156023637597368372575601 87867017728198026279431701)
                    ·
                      refine ⟨4118766456009282481848361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87867017728198026279431701 4118766456009282481848361)
                      ·
                        rfl

theorem cell23_8021269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_8021269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021269 prefixEnd_8021269 := by exact prefixLift 8021269
  have htrace : WordTrace (prefixWord ++ tailWord_8021269) baseStart_8021269 baseEnd_8021269 := by
    simpa [prefixWord, tailWord_8021269, baseEnd_8021269] using wordTrace_append hprefix tailTrace_8021269
  have hstable : (prefixWord ++ tailWord_8021269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021269).length < 2 ^ (prefixWord ++ tailWord_8021269).sum := by decide
  have hdescent : baseEnd_8021269 < baseStart_8021269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021296 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 1, 5]
def baseStart_8021296 : Nat := 118140960795 + 8021296 * 2 ^ 59
def prefixEnd_8021296 : Nat := 4983230072969 + 3 ^ 40 * 8021296 * 2
def baseEnd_8021296 : Nat := 1372926773328984625403579

theorem tailTrace_8021296 : CollatzResearch.WordTrace tailWord_8021296 prefixEnd_8021296 1372926773328984625403579 := by
  unfold tailWord_8021296
  simp only [CollatzResearch.WordTrace]
  refine ⟨146280349974110997568173871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195040466632147996757565161 146280349974110997568173871)
  ·
    refine ⟨219420524961166496352260807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146280349974110997568173871 219420524961166496352260807)
    ·
      refine ⟨329130787441749744528391211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219420524961166496352260807 329130787441749744528391211)
      ·
        refine ⟨493696181162624616792586817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329130787441749744528391211 493696181162624616792586817)
        ·
          refine ⟨370272135871968462594440113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493696181162624616792586817 370272135871968462594440113)
          ·
            refine ⟨277704101903976346945830085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370272135871968462594440113 277704101903976346945830085)
            ·
              refine ⟨52069519106995565052343141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277704101903976346945830085 52069519106995565052343141)
              ·
                refine ⟨9763034832561668447314339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52069519106995565052343141 9763034832561668447314339)
                ·
                  refine ⟨14644552248842502670971509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9763034832561668447314339 14644552248842502670971509)
                  ·
                    refine ⟨1372926773328984625403579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14644552248842502670971509 1372926773328984625403579)
                    ·
                      rfl

theorem cell23_8021296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_8021296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021296 prefixEnd_8021296 := by exact prefixLift 8021296
  have htrace : WordTrace (prefixWord ++ tailWord_8021296) baseStart_8021296 baseEnd_8021296 := by
    simpa [prefixWord, tailWord_8021296, baseEnd_8021296] using wordTrace_append hprefix tailTrace_8021296
  have hstable : (prefixWord ++ tailWord_8021296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021296).length < 2 ^ (prefixWord ++ tailWord_8021296).sum := by decide
  have hdescent : baseEnd_8021296 < baseStart_8021296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021336 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_8021336 : Nat := 118140960795 + 8021336 * 2 ^ 59
def prefixEnd_8021336 : Nat := 4983230072969 + 3 ^ 40 * 8021336 * 2
def baseEnd_8021336 : Nat := 4118800859213133719710553

theorem tailTrace_8021336 : CollatzResearch.WordTrace tailWord_8021336 prefixEnd_8021336 4118800859213133719710553 := by
  unfold tailWord_8021336
  simp only [CollatzResearch.WordTrace]
  refine ⟨146281079434038540983901931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195041439245384721311869241 146281079434038540983901931)
  ·
    refine ⟨219421619151057811475852897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146281079434038540983901931 219421619151057811475852897)
    ·
      refine ⟨164566214363293358606889673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219421619151057811475852897 164566214363293358606889673)
      ·
        refine ⟨123424660772470018955167255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164566214363293358606889673 123424660772470018955167255)
        ·
          refine ⟨185136991158705028432750883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123424660772470018955167255 185136991158705028432750883)
          ·
            refine ⟨277705486738057542649126325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185136991158705028432750883 277705486738057542649126325)
            ·
              refine ⟨26034889381692894623355593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277705486738057542649126325 26034889381692894623355593)
              ·
                refine ⟨19526167036269670967516695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26034889381692894623355593 19526167036269670967516695)
                ·
                  refine ⟨29289250554404506451275043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19526167036269670967516695 29289250554404506451275043)
                  ·
                    refine ⟨43933875831606759676912565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29289250554404506451275043 43933875831606759676912565)
                    ·
                      refine ⟨4118800859213133719710553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43933875831606759676912565 4118800859213133719710553)
                      ·
                        rfl

theorem cell23_8021336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_8021336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021336 prefixEnd_8021336 := by exact prefixLift 8021336
  have htrace : WordTrace (prefixWord ++ tailWord_8021336) baseStart_8021336 baseEnd_8021336 := by
    simpa [prefixWord, tailWord_8021336, baseEnd_8021336] using wordTrace_append hprefix tailTrace_8021336
  have hstable : (prefixWord ++ tailWord_8021336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021336).length < 2 ^ (prefixWord ++ tailWord_8021336).sum := by decide
  have hdescent : baseEnd_8021336 < baseStart_8021336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021356 : List Nat := [2, 2, 1, 1, 5, 2, 1, 9]
def baseStart_8021356 : Nat := 118140960795 + 8021356 * 2 ^ 59
def prefixEnd_8021356 : Nat := 4983230072969 + 3 ^ 40 * 8021356 * 2
def baseEnd_8021356 : Nat := 152548560326897171905943

theorem tailTrace_8021356 : CollatzResearch.WordTrace tailWord_8021356 prefixEnd_8021356 152548560326897171905943 := by
  unfold tailWord_8021356
  simp only [CollatzResearch.WordTrace]
  refine ⟨146281444164002312691765961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195041925552003083589021281 146281444164002312691765961)
  ·
    refine ⟨109711083123001734518824471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146281444164002312691765961 109711083123001734518824471)
    ·
      refine ⟨164566624684502601778236707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109711083123001734518824471 164566624684502601778236707)
      ·
        refine ⟨246849937026753902667355061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164566624684502601778236707 246849937026753902667355061)
        ·
          refine ⟨23142181596258178375064537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246849937026753902667355061 23142181596258178375064537)
          ·
            refine ⟨17356636197193633781298403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23142181596258178375064537 17356636197193633781298403)
            ·
              refine ⟨26034954295790450671947605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17356636197193633781298403 26034954295790450671947605)
              ·
                refine ⟨152548560326897171905943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26034954295790450671947605 152548560326897171905943)
                ·
                  rfl

theorem cell23_8021356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 9].length) (baseStart_8021356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021356 prefixEnd_8021356 := by exact prefixLift 8021356
  have htrace : WordTrace (prefixWord ++ tailWord_8021356) baseStart_8021356 baseEnd_8021356 := by
    simpa [prefixWord, tailWord_8021356, baseEnd_8021356] using wordTrace_append hprefix tailTrace_8021356
  have hstable : (prefixWord ++ tailWord_8021356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021356).length < 2 ^ (prefixWord ++ tailWord_8021356).sum := by decide
  have hdescent : baseEnd_8021356 < baseStart_8021356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021393 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 5, 3, 2]
def baseStart_8021393 : Nat := 118140960795 + 8021393 * 2 ^ 59
def prefixEnd_8021393 : Nat := 4983230072969 + 3 ^ 40 * 8021393 * 2
def baseEnd_8021393 : Nat := 4118830127610439996697791

theorem tailTrace_8021393 : CollatzResearch.WordTrace tailWord_8021393 prefixEnd_8021393 4118830127610439996697791 := by
  unfold tailWord_8021393
  simp only [CollatzResearch.WordTrace]
  refine ⟨292564237828870580702628833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195042825219247053801752555 292564237828870580702628833)
  ·
    refine ⟨219423178371652935526971625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292564237828870580702628833 219423178371652935526971625)
    ·
      refine ⟨164567383778739701645228719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219423178371652935526971625 164567383778739701645228719)
      ·
        refine ⟨246851075668109552467843079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164567383778739701645228719 246851075668109552467843079)
        ·
          refine ⟨370276613502164328701764619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246851075668109552467843079 370276613502164328701764619)
          ·
            refine ⟨555414920253246493052646929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370276613502164328701764619 555414920253246493052646929)
            ·
              refine ⟨416561190189934869789485197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555414920253246493052646929 416561190189934869789485197)
              ·
                refine ⟨156210446321225576171056949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416561190189934869789485197 156210446321225576171056949)
                ·
                  refine ⟨14644729342614897766036589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156210446321225576171056949 14644729342614897766036589)
                  ·
                    refine ⟨5491773503480586662263721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14644729342614897766036589 5491773503480586662263721)
                    ·
                      refine ⟨4118830127610439996697791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491773503480586662263721 4118830127610439996697791)
                      ·
                        rfl

theorem cell23_8021393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_8021393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021393 prefixEnd_8021393 := by exact prefixLift 8021393
  have htrace : WordTrace (prefixWord ++ tailWord_8021393) baseStart_8021393 baseEnd_8021393 := by
    simpa [prefixWord, tailWord_8021393, baseEnd_8021393] using wordTrace_append hprefix tailTrace_8021393
  have hstable : (prefixWord ++ tailWord_8021393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021393).length < 2 ^ (prefixWord ++ tailWord_8021393).sum := by decide
  have hdescent : baseEnd_8021393 < baseStart_8021393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021404 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_8021404 : Nat := 118140960795 + 8021404 * 2 ^ 59
def prefixEnd_8021404 : Nat := 4983230072969 + 3 ^ 40 * 8021404 * 2
def baseEnd_8021404 : Nat := 4118835775897639453660241

theorem tailTrace_8021404 : CollatzResearch.WordTrace tailWord_8021404 prefixEnd_8021404 4118835775897639453660241 := by
  unfold tailWord_8021404
  simp only [CollatzResearch.WordTrace]
  refine ⟨146282319515915364790639633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195043092687887153054186177 146282319515915364790639633)
  ·
    refine ⟨109711739636936523592979725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146282319515915364790639633 109711739636936523592979725)
    ·
      refine ⟨41141902363851196347367397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109711739636936523592979725 41141902363851196347367397)
      ·
        refine ⟨7714106693222099315131387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41141902363851196347367397 7714106693222099315131387)
        ·
          refine ⟨11571160039833148972697081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714106693222099315131387 11571160039833148972697081)
          ·
            refine ⟨8678370029874861729522811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11571160039833148972697081 8678370029874861729522811)
            ·
              refine ⟨13017555044812292594284217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678370029874861729522811 13017555044812292594284217)
              ·
                refine ⟨9763166283609219445713163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13017555044812292594284217 9763166283609219445713163)
                ·
                  refine ⟨14644749425413829168569745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9763166283609219445713163 14644749425413829168569745)
                  ·
                    refine ⟨10983562069060371876427309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14644749425413829168569745 10983562069060371876427309)
                    ·
                      refine ⟨4118835775897639453660241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10983562069060371876427309 4118835775897639453660241)
                      ·
                        rfl

theorem cell23_8021404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_8021404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021404 prefixEnd_8021404 := by exact prefixLift 8021404
  have htrace : WordTrace (prefixWord ++ tailWord_8021404) baseStart_8021404 baseEnd_8021404 := by
    simpa [prefixWord, tailWord_8021404, baseEnd_8021404] using wordTrace_append hprefix tailTrace_8021404
  have hstable : (prefixWord ++ tailWord_8021404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021404).length < 2 ^ (prefixWord ++ tailWord_8021404).sum := by decide
  have hdescent : baseEnd_8021404 < baseStart_8021404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021426 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_8021426 : Nat := 118140960795 + 8021426 * 2 ^ 59
def prefixEnd_8021426 : Nat := 4983230072969 + 3 ^ 40 * 8021426 * 2
def baseEnd_8021426 : Nat := 4118847072472038367585139

theorem tailTrace_8021426 : CollatzResearch.WordTrace tailWord_8021426 prefixEnd_8021426 4118847072472038367585139 := by
  unfold tailWord_8021426
  simp only [CollatzResearch.WordTrace]
  refine ⟨73141360359437756834645033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195043627625167351559053421 73141360359437756834645033)
  ·
    refine ⟨54856020269578317625983775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73141360359437756834645033 54856020269578317625983775)
    ·
      refine ⟨82284030404367476438975663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54856020269578317625983775 82284030404367476438975663)
      ·
        refine ⟨123426045606551214658463495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82284030404367476438975663 123426045606551214658463495)
        ·
          refine ⟨185139068409826821987695243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123426045606551214658463495 185139068409826821987695243)
          ·
            refine ⟨277708602614740232981542865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185139068409826821987695243 277708602614740232981542865)
            ·
              refine ⟨208281451961055174736157149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277708602614740232981542865 208281451961055174736157149)
              ·
                refine ⟨78105544485395690526058931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208281451961055174736157149 78105544485395690526058931)
                ·
                  refine ⟨117158316728093535789088397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78105544485395690526058931 117158316728093535789088397)
                  ·
                    refine ⟨43934368773035075920908149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117158316728093535789088397 43934368773035075920908149)
                    ·
                      refine ⟨4118847072472038367585139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43934368773035075920908149 4118847072472038367585139)
                      ·
                        rfl

theorem cell23_8021426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_8021426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021426 prefixEnd_8021426 := by exact prefixLift 8021426
  have htrace : WordTrace (prefixWord ++ tailWord_8021426) baseStart_8021426 baseEnd_8021426 := by
    simpa [prefixWord, tailWord_8021426, baseEnd_8021426] using wordTrace_append hprefix tailTrace_8021426
  have hstable : (prefixWord ++ tailWord_8021426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021426).length < 2 ^ (prefixWord ++ tailWord_8021426).sum := by decide
  have hdescent : baseEnd_8021426 < baseStart_8021426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021440 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 4, 2, 2]
def baseStart_8021440 : Nat := 118140960795 + 8021440 * 2 ^ 59
def prefixEnd_8021440 : Nat := 4983230072969 + 3 ^ 40 * 8021440 * 2
def baseEnd_8021440 : Nat := 4118854261201201312810075

theorem tailTrace_8021440 : CollatzResearch.WordTrace tailWord_8021440 prefixEnd_8021440 4118854261201201312810075 := by
  unfold tailWord_8021440
  simp only [CollatzResearch.WordTrace]
  refine ⟨146282976029850153864794887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195043968039800205153059849 146282976029850153864794887)
  ·
    refine ⟨219424464044775230797192331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146282976029850153864794887 219424464044775230797192331)
    ·
      refine ⟨329136696067162846195788497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219424464044775230797192331 329136696067162846195788497)
      ·
        refine ⟨246852522050372134646841373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329136696067162846195788497 246852522050372134646841373)
        ·
          refine ⟨92569695768889550492565515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246852522050372134646841373 92569695768889550492565515)
          ·
            refine ⟨138854543653334325738848273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92569695768889550492565515 138854543653334325738848273)
            ·
              refine ⟨104140907740000744304136205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138854543653334325738848273 104140907740000744304136205)
              ·
                refine ⟨39052840402500279114051077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104140907740000744304136205 39052840402500279114051077)
                ·
                  refine ⟨7322407575468802333884577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39052840402500279114051077 7322407575468802333884577)
                  ·
                    refine ⟨5491805681601601750413433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7322407575468802333884577 5491805681601601750413433)
                    ·
                      refine ⟨4118854261201201312810075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491805681601601750413433 4118854261201201312810075)
                      ·
                        rfl

theorem cell23_8021440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_8021440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021440 prefixEnd_8021440 := by exact prefixLift 8021440
  have htrace : WordTrace (prefixWord ++ tailWord_8021440) baseStart_8021440 baseEnd_8021440 := by
    simpa [prefixWord, tailWord_8021440, baseEnd_8021440] using wordTrace_append hprefix tailTrace_8021440
  have hstable : (prefixWord ++ tailWord_8021440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021440).length < 2 ^ (prefixWord ++ tailWord_8021440).sum := by decide
  have hdescent : baseEnd_8021440 < baseStart_8021440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021480 : List Nat := [2, 1, 4, 1, 1, 2, 4, 3, 5]
def baseStart_8021480 : Nat := 118140960795 + 8021480 * 2 ^ 59
def prefixEnd_8021480 : Nat := 4983230072969 + 3 ^ 40 * 8021480 * 2
def baseEnd_8021480 : Nat := 457652755603042350701099

theorem tailTrace_8021480 : CollatzResearch.WordTrace tailWord_8021480 prefixEnd_8021480 457652755603042350701099 := by
  unfold tailWord_8021480
  simp only [CollatzResearch.WordTrace]
  refine ⟨146283705489777697280522947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195044940653036929707363929 146283705489777697280522947)
  ·
    refine ⟨219425558234666545920784421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146283705489777697280522947 219425558234666545920784421)
    ·
      refine ⟨41142292168999977360147079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219425558234666545920784421 41142292168999977360147079)
      ·
        refine ⟨61713438253499966040220619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41142292168999977360147079 61713438253499966040220619)
        ·
          refine ⟨92570157380249949060330929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61713438253499966040220619 92570157380249949060330929)
          ·
            refine ⟨69427618035187461795248197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92570157380249949060330929 69427618035187461795248197)
            ·
              refine ⟨13017678381597649086609037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69427618035187461795248197 13017678381597649086609037)
              ·
                refine ⟨4881629393099118407478389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13017678381597649086609037 4881629393099118407478389)
                ·
                  refine ⟨457652755603042350701099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4881629393099118407478389 457652755603042350701099)
                  ·
                    rfl

theorem cell23_8021480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 5].length) (baseStart_8021480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021480 prefixEnd_8021480 := by exact prefixLift 8021480
  have htrace : WordTrace (prefixWord ++ tailWord_8021480) baseStart_8021480 baseEnd_8021480 := by
    simpa [prefixWord, tailWord_8021480, baseEnd_8021480] using wordTrace_append hprefix tailTrace_8021480
  have hstable : (prefixWord ++ tailWord_8021480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021480).length < 2 ^ (prefixWord ++ tailWord_8021480).sum := by decide
  have hdescent : baseEnd_8021480 < baseStart_8021480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021483 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 7, 2]
def baseStart_8021483 : Nat := 118140960795 + 8021483 * 2 ^ 59
def prefixEnd_8021483 : Nat := 4983230072969 + 3 ^ 40 * 8021483 * 2
def baseEnd_8021483 : Nat := 4118876340869344644572377

theorem tailTrace_8021483 : CollatzResearch.WordTrace tailWord_8021483 prefixEnd_8021483 4118876340869344644572377 := by
  unfold tailWord_8021483
  simp only [CollatzResearch.WordTrace]
  refine ⟨292567520398544526073405103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195045013599029684048936735 292567520398544526073405103)
  ·
    refine ⟨438851280597816789110107655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292567520398544526073405103 438851280597816789110107655)
    ·
      refine ⟨658276920896725183665161483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438851280597816789110107655 658276920896725183665161483)
      ·
        refine ⟨987415381345087775497742225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658276920896725183665161483 987415381345087775497742225)
        ·
          refine ⟨740561536008815831623306669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987415381345087775497742225 740561536008815831623306669)
          ·
            refine ⟨277710576003305936858740001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740561536008815831623306669 277710576003305936858740001)
            ·
              refine ⟨208282932002479452644055001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277710576003305936858740001 208282932002479452644055001)
              ·
                refine ⟨156212199001859589483041251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208282932002479452644055001 156212199001859589483041251)
                ·
                  refine ⟨234318298502789384224561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156212199001859589483041251 234318298502789384224561877)
                  ·
                    refine ⟨5491835121159126192763169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 234318298502789384224561877 5491835121159126192763169)
                    ·
                      refine ⟨4118876340869344644572377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491835121159126192763169 4118876340869344644572377)
                      ·
                        rfl

theorem cell23_8021483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7, 2].length) (baseStart_8021483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021483 prefixEnd_8021483 := by exact prefixLift 8021483
  have htrace : WordTrace (prefixWord ++ tailWord_8021483) baseStart_8021483 baseEnd_8021483 := by
    simpa [prefixWord, tailWord_8021483, baseEnd_8021483] using wordTrace_append hprefix tailTrace_8021483
  have hstable : (prefixWord ++ tailWord_8021483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021483).length < 2 ^ (prefixWord ++ tailWord_8021483).sum := by decide
  have hdescent : baseEnd_8021483 < baseStart_8021483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021490 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_8021490 : Nat := 118140960795 + 8021490 * 2 ^ 59
def prefixEnd_8021490 : Nat := 4983230072969 + 3 ^ 40 * 8021490 * 2
def baseEnd_8021490 : Nat := 4118879935233926117184845

theorem tailTrace_8021490 : CollatzResearch.WordTrace tailWord_8021490 prefixEnd_8021490 4118879935233926117184845 := by
  unfold tailWord_8021490
  simp only [CollatzResearch.WordTrace]
  refine ⟨73141943927379791567227481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195045183806346110845939949 73141943927379791567227481)
  ·
    refine ⟨54856457945534843675420611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73141943927379791567227481 54856457945534843675420611)
    ·
      refine ⟨82284686918302265513130917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54856457945534843675420611 82284686918302265513130917)
      ·
        refine ⟨15428378797181674783712047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82284686918302265513130917 15428378797181674783712047)
        ·
          refine ⟨23142568195772512175568071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15428378797181674783712047 23142568195772512175568071)
          ·
            refine ⟨34713852293658768263352107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23142568195772512175568071 34713852293658768263352107)
            ·
              refine ⟨52070778440488152395028161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34713852293658768263352107 52070778440488152395028161)
              ·
                refine ⟨39053083830366114296271121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52070778440488152395028161 39053083830366114296271121)
                ·
                  refine ⟨29289812872774585722203341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39053083830366114296271121 29289812872774585722203341)
                  ·
                    refine ⟨10983679827290469645826253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29289812872774585722203341 10983679827290469645826253)
                    ·
                      refine ⟨4118879935233926117184845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10983679827290469645826253 4118879935233926117184845)
                      ·
                        rfl

theorem cell23_8021490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_8021490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021490 prefixEnd_8021490 := by exact prefixLift 8021490
  have htrace : WordTrace (prefixWord ++ tailWord_8021490) baseStart_8021490 baseEnd_8021490 := by
    simpa [prefixWord, tailWord_8021490, baseEnd_8021490] using wordTrace_append hprefix tailTrace_8021490
  have hstable : (prefixWord ++ tailWord_8021490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021490).length < 2 ^ (prefixWord ++ tailWord_8021490).sum := by decide
  have hdescent : baseEnd_8021490 < baseStart_8021490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021553 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 6]
def baseStart_8021553 : Nat := 118140960795 + 8021553 * 2 ^ 59
def prefixEnd_8021553 : Nat := 4983230072969 + 3 ^ 40 * 8021553 * 2
def baseEnd_8021553 : Nat := 457656920501684374521895

theorem tailTrace_8021553 : CollatzResearch.WordTrace tailWord_8021553 prefixEnd_8021553 457656920501684374521895 := by
  unfold tailWord_8021553
  simp only [CollatzResearch.WordTrace]
  refine ⟨292570073508290928028453313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195046715672193952018968875 292570073508290928028453313)
  ·
    refine ⟨219427555131218196021339985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292570073508290928028453313 219427555131218196021339985)
    ·
      refine ⟨164570666348413647016004989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219427555131218196021339985 164570666348413647016004989)
      ·
        refine ⟨61713999880655117631001871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164570666348413647016004989 61713999880655117631001871)
        ·
          refine ⟨92570999820982676446502807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61713999880655117631001871 92570999820982676446502807)
          ·
            refine ⟨138856499731474014669754211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92570999820982676446502807 138856499731474014669754211)
            ·
              refine ⟨208284749597211022004631317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138856499731474014669754211 208284749597211022004631317)
              ·
                refine ⟨9763347637369266656467093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208284749597211022004631317 9763347637369266656467093)
                ·
                  refine ⟨457656920501684374521895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9763347637369266656467093 457656920501684374521895)
                  ·
                    rfl

theorem cell23_8021553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 6].length) (baseStart_8021553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021553 prefixEnd_8021553 := by exact prefixLift 8021553
  have htrace : WordTrace (prefixWord ++ tailWord_8021553) baseStart_8021553 baseEnd_8021553 := by
    simpa [prefixWord, tailWord_8021553, baseEnd_8021553] using wordTrace_append hprefix tailTrace_8021553
  have hstable : (prefixWord ++ tailWord_8021553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021553).length < 2 ^ (prefixWord ++ tailWord_8021553).sum := by decide
  have hdescent : baseEnd_8021553 < baseStart_8021553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021557 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_8021557 : Nat := 118140960795 + 8021557 * 2 ^ 59
def prefixEnd_8021557 : Nat := 4983230072969 + 3 ^ 40 * 8021557 * 2
def baseEnd_8021557 : Nat := 1372971446145925785015679

theorem tailTrace_8021557 : CollatzResearch.WordTrace tailWord_8021557 prefixEnd_8021557 1372971446145925785015679 := by
  unfold tailWord_8021557
  simp only [CollatzResearch.WordTrace]
  refine ⟨292570219400276436711598925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195046812933517624474399283 292570219400276436711598925)
  ·
    refine ⟨109713832275103663766849597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292570219400276436711598925 109713832275103663766849597)
    ·
      refine ⟨41142687103163873912568599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109713832275103663766849597 41142687103163873912568599)
      ·
        refine ⟨61714030654745810868852899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41142687103163873912568599 61714030654745810868852899)
        ·
          refine ⟨92571045982118716303279349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61714030654745810868852899 92571045982118716303279349)
          ·
            refine ⟨8678535560823629653432439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92571045982118716303279349 8678535560823629653432439)
            ·
              refine ⟨13017803341235444480148659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678535560823629653432439 13017803341235444480148659)
              ·
                refine ⟨19526705011853166720222989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13017803341235444480148659 19526705011853166720222989)
                ·
                  refine ⟨7322514379444937520083621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19526705011853166720222989 7322514379444937520083621)
                  ·
                    refine ⟨1372971446145925785015679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7322514379444937520083621 1372971446145925785015679)
                    ·
                      rfl

theorem cell23_8021557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_8021557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021557 prefixEnd_8021557 := by exact prefixLift 8021557
  have htrace : WordTrace (prefixWord ++ tailWord_8021557) baseStart_8021557 baseEnd_8021557 := by
    simpa [prefixWord, tailWord_8021557, baseEnd_8021557] using wordTrace_append hprefix tailTrace_8021557
  have hstable : (prefixWord ++ tailWord_8021557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021557).length < 2 ^ (prefixWord ++ tailWord_8021557).sum := by decide
  have hdescent : baseEnd_8021557 < baseStart_8021557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021607 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_8021607 : Nat := 118140960795 + 8021607 * 2 ^ 59
def prefixEnd_8021607 : Nat := 4983230072969 + 3 ^ 40 * 8021607 * 2
def baseEnd_8021607 : Nat := 4118940012470502159421807

theorem tailTrace_8021607 : CollatzResearch.WordTrace tailWord_8021607 prefixEnd_8021607 4118940012470502159421807 := by
  unfold tailWord_8021607
  simp only [CollatzResearch.WordTrace]
  refine ⟨292572043050095295250919075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195048028700063530167279383 292572043050095295250919075)
  ·
    refine ⟨438858064575142942876378613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292572043050095295250919075 438858064575142942876378613)
    ·
      refine ⟨41142943553919650894660495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438858064575142942876378613 41142943553919650894660495)
      ·
        refine ⟨61714415330879476341990743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41142943553919650894660495 61714415330879476341990743)
        ·
          refine ⟨92571622996319214512986115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61714415330879476341990743 92571622996319214512986115)
          ·
            refine ⟨138857434494478821769479173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92571622996319214512986115 138857434494478821769479173)
            ·
              refine ⟨26035768967714779081777345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138857434494478821769479173 26035768967714779081777345)
              ·
                refine ⟨19526826725786084311333009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26035768967714779081777345 19526826725786084311333009)
                ·
                  refine ⟨14645120044339563233499757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19526826725786084311333009 14645120044339563233499757)
                  ·
                    refine ⟨5491920016627336212562409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14645120044339563233499757 5491920016627336212562409)
                    ·
                      refine ⟨4118940012470502159421807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5491920016627336212562409 4118940012470502159421807)
                      ·
                        rfl

theorem cell23_8021607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_8021607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021607 prefixEnd_8021607 := by exact prefixLift 8021607
  have htrace : WordTrace (prefixWord ++ tailWord_8021607) baseStart_8021607 baseEnd_8021607 := by
    simpa [prefixWord, tailWord_8021607, baseEnd_8021607] using wordTrace_append hprefix tailTrace_8021607
  have hstable : (prefixWord ++ tailWord_8021607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021607).length < 2 ^ (prefixWord ++ tailWord_8021607).sum := by decide
  have hdescent : baseEnd_8021607 < baseStart_8021607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021623 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_8021623 : Nat := 118140960795 + 8021623 * 2 ^ 59
def prefixEnd_8021623 : Nat := 4983230072969 + 3 ^ 40 * 8021623 * 2
def baseEnd_8021623 : Nat := 4118948228160974096821733

theorem tailTrace_8021623 : CollatzResearch.WordTrace tailWord_8021623 prefixEnd_8021623 4118948228160974096821733 := by
  unfold tailWord_8021623
  simp only [CollatzResearch.WordTrace]
  refine ⟨292572626618037329983501523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195048417745358219989001015 292572626618037329983501523)
  ·
    refine ⟨438858939927055994975252285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292572626618037329983501523 438858939927055994975252285)
    ·
      refine ⟨164572102472645998115719607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438858939927055994975252285 164572102472645998115719607)
      ·
        refine ⟨246858153708968997173579411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164572102472645998115719607 246858153708968997173579411)
        ·
          refine ⟨370287230563453495760369117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246858153708968997173579411 370287230563453495760369117)
          ·
            refine ⟨138857711461295060910138419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370287230563453495760369117 138857711461295060910138419)
            ·
              refine ⟨208286567191942591365207629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138857711461295060910138419 208286567191942591365207629)
              ·
                refine ⟨78107462696978471761952861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208286567191942591365207629 78107462696978471761952861)
                ·
                  refine ⟨29290298511366926910732323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78107462696978471761952861 29290298511366926910732323)
                  ·
                    refine ⟨43935447767050390366098485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29290298511366926910732323 43935447767050390366098485)
                    ·
                      refine ⟨4118948228160974096821733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43935447767050390366098485 4118948228160974096821733)
                      ·
                        rfl

theorem cell23_8021623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_8021623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021623 prefixEnd_8021623 := by exact prefixLift 8021623
  have htrace : WordTrace (prefixWord ++ tailWord_8021623) baseStart_8021623 baseEnd_8021623 := by
    simpa [prefixWord, tailWord_8021623, baseEnd_8021623] using wordTrace_append hprefix tailTrace_8021623
  have hstable : (prefixWord ++ tailWord_8021623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021623).length < 2 ^ (prefixWord ++ tailWord_8021623).sum := by decide
  have hdescent : baseEnd_8021623 < baseStart_8021623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021660 : List Nat := [2, 2, 3, 2, 3, 1, 10]
def baseStart_8021660 : Nat := 118140960795 + 8021660 * 2 ^ 59
def prefixEnd_8021660 : Nat := 4983230072969 + 3 ^ 40 * 8021660 * 2
def baseEnd_8021660 : Nat := 50851447246236919161223

theorem tailTrace_8021660 : CollatzResearch.WordTrace tailWord_8021660 prefixEnd_8021660 50851447246236919161223 := by
  unfold tailWord_8021660
  simp only [CollatzResearch.WordTrace]
  refine ⟨146286988059451642651299217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195049317412602190201732289 146286988059451642651299217)
  ·
    refine ⟨109715241044588731988474413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146286988059451642651299217 109715241044588731988474413)
    ·
      refine ⟨41143215391720774495677905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109715241044588731988474413 41143215391720774495677905)
      ·
        refine ⟨30857411543790580871758429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41143215391720774495677905 30857411543790580871758429)
        ·
          refine ⟨11571529328921467826909411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30857411543790580871758429 11571529328921467826909411)
          ·
            refine ⟨17357293993382201740364117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11571529328921467826909411 17357293993382201740364117)
            ·
              refine ⟨50851447246236919161223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17357293993382201740364117 50851447246236919161223)
              ·
                rfl

theorem cell23_8021660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 10].length) (baseStart_8021660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021660 prefixEnd_8021660 := by exact prefixLift 8021660
  have htrace : WordTrace (prefixWord ++ tailWord_8021660) baseStart_8021660 baseEnd_8021660 := by
    simpa [prefixWord, tailWord_8021660, baseEnd_8021660] using wordTrace_append hprefix tailTrace_8021660
  have hstable : (prefixWord ++ tailWord_8021660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021660).length < 2 ^ (prefixWord ++ tailWord_8021660).sum := by decide
  have hdescent : baseEnd_8021660 < baseStart_8021660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021664 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 2, 4]
def baseStart_8021664 : Nat := 118140960795 + 8021664 * 2 ^ 59
def prefixEnd_8021664 : Nat := 4983230072969 + 3 ^ 40 * 8021664 * 2
def baseEnd_8021664 : Nat := 1372989760289269478803015

theorem tailTrace_8021664 : CollatzResearch.WordTrace tailWord_8021664 prefixEnd_8021664 1372989760289269478803015 := by
  unfold tailWord_8021664
  simp only [CollatzResearch.WordTrace]
  refine ⟨146287061005444396992872023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195049414673925862657162697 146287061005444396992872023)
  ·
    refine ⟨219430591508166595489308035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146287061005444396992872023 219430591508166595489308035)
    ·
      refine ⟨329145887262249893233962053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219430591508166595489308035 329145887262249893233962053)
      ·
        refine ⟨61714853861671854981367885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329145887262249893233962053 61714853861671854981367885)
        ·
          refine ⟨23143070198126945618012957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61714853861671854981367885 23143070198126945618012957)
          ·
            refine ⟨8678651324297604606754859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23143070198126945618012957 8678651324297604606754859)
            ·
              refine ⟨13017976986446406910132289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678651324297604606754859 13017976986446406910132289)
              ·
                refine ⟨9763482739834805182599217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13017976986446406910132289 9763482739834805182599217)
                ·
                  refine ⟨7322612054876103886949413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9763482739834805182599217 7322612054876103886949413)
                  ·
                    refine ⟨1372989760289269478803015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7322612054876103886949413 1372989760289269478803015)
                    ·
                      rfl

theorem cell23_8021664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_8021664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021664 prefixEnd_8021664 := by exact prefixLift 8021664
  have htrace : WordTrace (prefixWord ++ tailWord_8021664) baseStart_8021664 baseEnd_8021664 := by
    simpa [prefixWord, tailWord_8021664, baseEnd_8021664] using wordTrace_append hprefix tailTrace_8021664
  have hstable : (prefixWord ++ tailWord_8021664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021664).length < 2 ^ (prefixWord ++ tailWord_8021664).sum := by decide
  have hdescent : baseEnd_8021664 < baseStart_8021664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021687 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_8021687 : Nat := 118140960795 + 8021687 * 2 ^ 59
def prefixEnd_8021687 : Nat := 4983230072969 + 3 ^ 40 * 8021687 * 2
def baseEnd_8021687 : Nat := 4118981090922861846421439

theorem tailTrace_8021687 : CollatzResearch.WordTrace tailWord_8021687 prefixEnd_8021687 4118981090922861846421439 := by
  unfold tailWord_8021687
  simp only [CollatzResearch.WordTrace]
  refine ⟨292574960889805468913831315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195049973926536979275887543 292574960889805468913831315)
  ·
    refine ⟨438862441334708203370746973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292574960889805468913831315 438862441334708203370746973)
    ·
      refine ⟨164573415500515576264030115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438862441334708203370746973 164573415500515576264030115)
      ·
        refine ⟨246860123250773364396045173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164573415500515576264030115 246860123250773364396045173)
        ·
          refine ⟨23143136554760002912129235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246860123250773364396045173 23143136554760002912129235)
          ·
            refine ⟨34714704832140004368193853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23143136554760002912129235 34714704832140004368193853)
            ·
              refine ⟨13018014312052501638072695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34714704832140004368193853 13018014312052501638072695)
              ·
                refine ⟨19527021468078752457109043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13018014312052501638072695 19527021468078752457109043)
                ·
                  refine ⟨29290532202118128685663565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19527021468078752457109043 29290532202118128685663565)
                  ·
                    refine ⟨10983949575794298257123837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29290532202118128685663565 10983949575794298257123837)
                    ·
                      refine ⟨4118981090922861846421439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10983949575794298257123837 4118981090922861846421439)
                      ·
                        rfl

theorem cell23_8021687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_8021687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021687 prefixEnd_8021687 := by exact prefixLift 8021687
  have htrace : WordTrace (prefixWord ++ tailWord_8021687) baseStart_8021687 baseEnd_8021687 := by
    simpa [prefixWord, tailWord_8021687, baseEnd_8021687] using wordTrace_append hprefix tailTrace_8021687
  have hstable : (prefixWord ++ tailWord_8021687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021687).length < 2 ^ (prefixWord ++ tailWord_8021687).sum := by decide
  have hdescent : baseEnd_8021687 < baseStart_8021687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021700 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_8021700 : Nat := 118140960795 + 8021700 * 2 ^ 59
def prefixEnd_8021700 : Nat := 4983230072969 + 3 ^ 40 * 8021700 * 2
def baseEnd_8021700 : Nat := 4118987766171370295558879

theorem tailTrace_8021700 : CollatzResearch.WordTrace tailWord_8021700 prefixEnd_8021700 4118987766171370295558879 := by
  unfold tailWord_8021700
  simp only [CollatzResearch.WordTrace]
  refine ⟨146287717519379186067027277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195050290025838914756036369 146287717519379186067027277)
  ·
    refine ⟨54857894069767194775135229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146287717519379186067027277 54857894069767194775135229)
    ·
      refine ⟨20571710276162698040675711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54857894069767194775135229 20571710276162698040675711)
      ·
        refine ⟨30857565414244047061013567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20571710276162698040675711 30857565414244047061013567)
        ·
          refine ⟨46286348121366070591520351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30857565414244047061013567 46286348121366070591520351)
          ·
            refine ⟨69429522182049105887280527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46286348121366070591520351 69429522182049105887280527)
            ·
              refine ⟨104144283273073658830920791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69429522182049105887280527 104144283273073658830920791)
              ·
                refine ⟨156216424909610488246381187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104144283273073658830920791 156216424909610488246381187)
                ·
                  refine ⟨234324637364415732369571781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156216424909610488246381187 234324637364415732369571781)
                  ·
                    refine ⟨43935869505827949819294709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234324637364415732369571781 43935869505827949819294709)
                    ·
                      refine ⟨4118987766171370295558879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43935869505827949819294709 4118987766171370295558879)
                      ·
                        rfl

theorem cell23_8021700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_8021700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021700 prefixEnd_8021700 := by exact prefixLift 8021700
  have htrace : WordTrace (prefixWord ++ tailWord_8021700) baseStart_8021700 baseEnd_8021700 := by
    simpa [prefixWord, tailWord_8021700, baseEnd_8021700] using wordTrace_append hprefix tailTrace_8021700
  have hstable : (prefixWord ++ tailWord_8021700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021700).length < 2 ^ (prefixWord ++ tailWord_8021700).sum := by decide
  have hdescent : baseEnd_8021700 < baseStart_8021700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021740 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_8021740 : Nat := 118140960795 + 8021740 * 2 ^ 59
def prefixEnd_8021740 : Nat := 4983230072969 + 3 ^ 40 * 8021740 * 2
def baseEnd_8021740 : Nat := 4119008305397550139058695

theorem tailTrace_8021740 : CollatzResearch.WordTrace tailWord_8021740 prefixEnd_8021740 4119008305397550139058695 := by
  unfold tailWord_8021740
  simp only [CollatzResearch.WordTrace]
  refine ⟨146288446979306729482755337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195051262639075639310340449 146288446979306729482755337)
  ·
    refine ⟨109716335234480047112066503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146288446979306729482755337 109716335234480047112066503)
    ·
      refine ⟨164574502851720070668099755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109716335234480047112066503 164574502851720070668099755)
      ·
        refine ⟨246861754277580106002149633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164574502851720070668099755 246861754277580106002149633)
        ·
          refine ⟨185146315708185079501612225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246861754277580106002149633 185146315708185079501612225)
          ·
            refine ⟨138859736781138809626209169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185146315708185079501612225 138859736781138809626209169)
            ·
              refine ⟨104144802585854107219656877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138859736781138809626209169 104144802585854107219656877)
              ·
                refine ⟨39054300969695290207371329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104144802585854107219656877 39054300969695290207371329)
                ·
                  refine ⟨29290725727271467655528497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39054300969695290207371329 29290725727271467655528497)
                  ·
                    refine ⟨21968044295453600741646373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29290725727271467655528497 21968044295453600741646373)
                    ·
                      refine ⟨4119008305397550139058695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21968044295453600741646373 4119008305397550139058695)
                      ·
                        rfl

theorem cell23_8021740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_8021740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021740 prefixEnd_8021740 := by exact prefixLift 8021740
  have htrace : WordTrace (prefixWord ++ tailWord_8021740) baseStart_8021740 baseEnd_8021740 := by
    simpa [prefixWord, tailWord_8021740, baseEnd_8021740] using wordTrace_append hprefix tailTrace_8021740
  have hstable : (prefixWord ++ tailWord_8021740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021740).length < 2 ^ (prefixWord ++ tailWord_8021740).sum := by decide
  have hdescent : baseEnd_8021740 < baseStart_8021740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021748 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_8021748 : Nat := 118140960795 + 8021748 * 2 ^ 59
def prefixEnd_8021748 : Nat := 4983230072969 + 3 ^ 40 * 8021748 * 2
def baseEnd_8021748 : Nat := 4119012413242786107758659

theorem tailTrace_8021748 : CollatzResearch.WordTrace tailWord_8021748 prefixEnd_8021748 4119012413242786107758659 := by
  unfold tailWord_8021748
  simp only [CollatzResearch.WordTrace]
  refine ⟨146288592871292238165900949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195051457161722984221201265 146288592871292238165900949)
  ·
    refine ⟨6857277790841823664026607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146288592871292238165900949 6857277790841823664026607)
    ·
      refine ⟨10285916686262735496039911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857277790841823664026607 10285916686262735496039911)
      ·
        refine ⟨15428875029394103244059867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285916686262735496039911 15428875029394103244059867)
        ·
          refine ⟨23143312544091154866089801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15428875029394103244059867 23143312544091154866089801)
          ·
            refine ⟨17357484408068366149567351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23143312544091154866089801 17357484408068366149567351)
            ·
              refine ⟨26036226612102549224351027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17357484408068366149567351 26036226612102549224351027)
              ·
                refine ⟨39054339918153823836526541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26036226612102549224351027 39054339918153823836526541)
                ·
                  refine ⟨14645377469307683938697453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39054339918153823836526541 14645377469307683938697453)
                  ·
                    refine ⟨5492016550990381477011545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14645377469307683938697453 5492016550990381477011545)
                    ·
                      refine ⟨4119012413242786107758659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492016550990381477011545 4119012413242786107758659)
                      ·
                        rfl

theorem cell23_8021748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_8021748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021748 prefixEnd_8021748 := by exact prefixLift 8021748
  have htrace : WordTrace (prefixWord ++ tailWord_8021748) baseStart_8021748 baseEnd_8021748 := by
    simpa [prefixWord, tailWord_8021748, baseEnd_8021748] using wordTrace_append hprefix tailTrace_8021748
  have hstable : (prefixWord ++ tailWord_8021748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021748).length < 2 ^ (prefixWord ++ tailWord_8021748).sum := by decide
  have hdescent : baseEnd_8021748 < baseStart_8021748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021760 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3]
def baseStart_8021760 : Nat := 118140960795 + 8021760 * 2 ^ 59
def prefixEnd_8021760 : Nat := 4983230072969 + 3 ^ 40 * 8021760 * 2
def baseEnd_8021760 : Nat := 4119018575010640060808603

theorem tailTrace_8021760 : CollatzResearch.WordTrace tailWord_8021760 prefixEnd_8021760 4119018575010640060808603 := by
  unfold tailWord_8021760
  simp only [CollatzResearch.WordTrace]
  refine ⟨146288811709270501190619367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195051748945694001587492489 146288811709270501190619367)
  ·
    refine ⟨219433217563905751785929051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146288811709270501190619367 219433217563905751785929051)
    ·
      refine ⟨329149826345858627678893577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219433217563905751785929051 329149826345858627678893577)
      ·
        refine ⟨246862369759393970759170183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329149826345858627678893577 246862369759393970759170183)
        ·
          refine ⟨370293554639090956138755275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246862369759393970759170183 370293554639090956138755275)
          ·
            refine ⟨555440331958636434208132913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370293554639090956138755275 555440331958636434208132913)
            ·
              refine ⟨416580248968977325656099685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555440331958636434208132913 416580248968977325656099685)
              ·
                refine ⟨78108796681683248560518691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416580248968977325656099685 78108796681683248560518691)
                ·
                  refine ⟨117163195022524872840778037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78108796681683248560518691 117163195022524872840778037)
                  ·
                    refine ⟨10984049533361706828822941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117163195022524872840778037 10984049533361706828822941)
                    ·
                      refine ⟨4119018575010640060808603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10984049533361706828822941 4119018575010640060808603)
                      ·
                        rfl

theorem cell23_8021760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_8021760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021760 prefixEnd_8021760 := by exact prefixLift 8021760
  have htrace : WordTrace (prefixWord ++ tailWord_8021760) baseStart_8021760 baseEnd_8021760 := by
    simpa [prefixWord, tailWord_8021760, baseEnd_8021760] using wordTrace_append hprefix tailTrace_8021760
  have hstable : (prefixWord ++ tailWord_8021760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021760).length < 2 ^ (prefixWord ++ tailWord_8021760).sum := by decide
  have hdescent : baseEnd_8021760 < baseStart_8021760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021773 : List Nat := [1, 7, 2, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_8021773 : Nat := 118140960795 + 8021773 * 2 ^ 59
def prefixEnd_8021773 : Nat := 4983230072969 + 3 ^ 40 * 8021773 * 2
def baseEnd_8021773 : Nat := 4119025250259148509946045

theorem tailTrace_8021773 : CollatzResearch.WordTrace tailWord_8021773 prefixEnd_8021773 4119025250259148509946045 := by
  unfold tailWord_8021773
  simp only [CollatzResearch.WordTrace]
  refine ⟨292578097567493905601461973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195052065044995937067641315 292578097567493905601461973)
  ·
    refine ⟨6857299161738138412534265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 292578097567493905601461973 6857299161738138412534265)
    ·
      refine ⟨5142974371303603809400699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6857299161738138412534265 5142974371303603809400699)
      ·
        refine ⟨7714461556955405714101049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142974371303603809400699 7714461556955405714101049)
        ·
          refine ⟨5785846167716554285575787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7714461556955405714101049 5785846167716554285575787)
          ·
            refine ⟨8678769251574831428363681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785846167716554285575787 8678769251574831428363681)
            ·
              refine ⟨6509076938681123571272761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8678769251574831428363681 6509076938681123571272761)
              ·
                refine ⟨4881807704010842678454571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509076938681123571272761 4881807704010842678454571)
                ·
                  refine ⟨7322711556016264017681857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4881807704010842678454571 7322711556016264017681857)
                  ·
                    refine ⟨5492033667012198013261393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7322711556016264017681857 5492033667012198013261393)
                    ·
                      refine ⟨4119025250259148509946045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492033667012198013261393 4119025250259148509946045)
                      ·
                        rfl

theorem cell23_8021773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_8021773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021773 prefixEnd_8021773 := by exact prefixLift 8021773
  have htrace : WordTrace (prefixWord ++ tailWord_8021773) baseStart_8021773 baseEnd_8021773 := by
    simpa [prefixWord, tailWord_8021773, baseEnd_8021773] using wordTrace_append hprefix tailTrace_8021773
  have hstable : (prefixWord ++ tailWord_8021773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021773).length < 2 ^ (prefixWord ++ tailWord_8021773).sum := by decide
  have hdescent : baseEnd_8021773 < baseStart_8021773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021778 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_8021778 : Nat := 118140960795 + 8021778 * 2 ^ 59
def prefixEnd_8021778 : Nat := 4983230072969 + 3 ^ 40 * 8021778 * 2
def baseEnd_8021778 : Nat := 4119027817662420990383521

theorem tailTrace_8021778 : CollatzResearch.WordTrace tailWord_8021778 prefixEnd_8021778 4119027817662420990383521 := by
  unfold tailWord_8021778
  simp only [CollatzResearch.WordTrace]
  refine ⟨73144569983118947863848497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195052186621650527636929325 73144569983118947863848497)
  ·
    refine ⟨54858427487339210897886373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73144569983118947863848497 54858427487339210897886373)
    ·
      refine ⟨10285955153876102043353695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54858427487339210897886373 10285955153876102043353695)
      ·
        refine ⟨15428932730814153065030543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285955153876102043353695 15428932730814153065030543)
        ·
          refine ⟨23143399096221229597545815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15428932730814153065030543 23143399096221229597545815)
          ·
            refine ⟨34715098644331844396318723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23143399096221229597545815 34715098644331844396318723)
            ·
              refine ⟨52072647966497766594478085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34715098644331844396318723 52072647966497766594478085)
              ·
                refine ⟨9763621493718331236464641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52072647966497766594478085 9763621493718331236464641)
                ·
                  refine ⟨7322716120288748427348481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9763621493718331236464641 7322716120288748427348481)
                  ·
                    refine ⟨5492037090216561320511361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7322716120288748427348481 5492037090216561320511361)
                    ·
                      refine ⟨4119027817662420990383521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492037090216561320511361 4119027817662420990383521)
                      ·
                        rfl

theorem cell23_8021778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_8021778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021778 prefixEnd_8021778 := by exact prefixLift 8021778
  have htrace : WordTrace (prefixWord ++ tailWord_8021778) baseStart_8021778 baseEnd_8021778 := by
    simpa [prefixWord, tailWord_8021778, baseEnd_8021778] using wordTrace_append hprefix tailTrace_8021778
  have hstable : (prefixWord ++ tailWord_8021778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021778).length < 2 ^ (prefixWord ++ tailWord_8021778).sum := by decide
  have hdescent : baseEnd_8021778 < baseStart_8021778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021784 : List Nat := [2, 1, 2, 3, 1, 1, 6, 2, 5]
def baseStart_8021784 : Nat := 118140960795 + 8021784 * 2 ^ 59
def prefixEnd_8021784 : Nat := 4983230072969 + 3 ^ 40 * 8021784 * 2
def baseEnd_8021784 : Nat := 457670099838483107434277

theorem tailTrace_8021784 : CollatzResearch.WordTrace tailWord_8021784 prefixEnd_8021784 457670099838483107434277 := by
  unfold tailWord_8021784
  simp only [CollatzResearch.WordTrace]
  refine ⟨146289249385227027240056203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195052332513636036320074937 146289249385227027240056203)
  ·
    refine ⟨219433874077840540860084305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146289249385227027240056203 219433874077840540860084305)
    ·
      refine ⟨164575405558380405645063229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219433874077840540860084305 164575405558380405645063229)
      ·
        refine ⟨61715777084392652116898711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164575405558380405645063229 61715777084392652116898711)
        ·
          refine ⟨92573665626588978175348067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61715777084392652116898711 92573665626588978175348067)
          ·
            refine ⟨138860498439883467263022101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92573665626588978175348067 138860498439883467263022101)
            ·
              refine ⟨6509085864369537527954161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138860498439883467263022101 6509085864369537527954161)
              ·
                refine ⟨4881814398277153145965621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509085864369537527954161 4881814398277153145965621)
                ·
                  refine ⟨457670099838483107434277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4881814398277153145965621 457670099838483107434277)
                  ·
                    rfl

theorem cell23_8021784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 5].length) (baseStart_8021784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021784 prefixEnd_8021784 := by exact prefixLift 8021784
  have htrace : WordTrace (prefixWord ++ tailWord_8021784) baseStart_8021784 baseEnd_8021784 := by
    simpa [prefixWord, tailWord_8021784, baseEnd_8021784] using wordTrace_append hprefix tailTrace_8021784
  have hstable : (prefixWord ++ tailWord_8021784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021784).length < 2 ^ (prefixWord ++ tailWord_8021784).sum := by decide
  have hdescent : baseEnd_8021784 < baseStart_8021784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021814 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_8021814 : Nat := 118140960795 + 8021814 * 2 ^ 59
def prefixEnd_8021814 : Nat := 4983230072969 + 3 ^ 40 * 8021814 * 2
def baseEnd_8021814 : Nat := 1373015434321994283177785

theorem tailTrace_8021814 : CollatzResearch.WordTrace tailWord_8021814 prefixEnd_8021814 1373015434321994283177785 := by
  unfold tailWord_8021814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18286224560021585600231531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195053061973563579735802997 18286224560021585600231531)
  ·
    refine ⟨27429336840032378400347297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18286224560021585600231531 27429336840032378400347297)
    ·
      refine ⟨20572002630024283800260473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27429336840032378400347297 20572002630024283800260473)
      ·
        refine ⟨15429001972518212850195355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20572002630024283800260473 15429001972518212850195355)
        ·
          refine ⟨23143502958777319275293033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15429001972518212850195355 23143502958777319275293033)
          ·
            refine ⟨17357627219082989456469775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23143502958777319275293033 17357627219082989456469775)
            ·
              refine ⟨26036440828624484184704663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17357627219082989456469775 26036440828624484184704663)
              ·
                refine ⟨39054661242936726277056995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26036440828624484184704663 39054661242936726277056995)
                ·
                  refine ⟨58581991864405089415585493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39054661242936726277056995 58581991864405089415585493)
                  ·
                    refine ⟨1373015434321994283177785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58581991864405089415585493 1373015434321994283177785)
                    ·
                      rfl

theorem cell23_8021814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_8021814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021814 prefixEnd_8021814 := by exact prefixLift 8021814
  have htrace : WordTrace (prefixWord ++ tailWord_8021814) baseStart_8021814 baseEnd_8021814 := by
    simpa [prefixWord, tailWord_8021814, baseEnd_8021814] using wordTrace_append hprefix tailTrace_8021814
  have hstable : (prefixWord ++ tailWord_8021814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021814).length < 2 ^ (prefixWord ++ tailWord_8021814).sum := by decide
  have hdescent : baseEnd_8021814 < baseStart_8021814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021844 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_8021844 : Nat := 118140960795 + 8021844 * 2 ^ 59
def prefixEnd_8021844 : Nat := 4983230072969 + 3 ^ 40 * 8021844 * 2
def baseEnd_8021844 : Nat := 1373020569128539244052739

theorem tailTrace_8021844 : CollatzResearch.WordTrace tailWord_8021844 prefixEnd_8021844 1373020569128539244052739 := by
  unfold tailWord_8021844
  simp only [CollatzResearch.WordTrace]
  refine ⟨146290343575118342363648293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195053791433491123151531057 146290343575118342363648293)
  ·
    refine ⟨27429439420334689193184055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146290343575118342363648293 27429439420334689193184055)
    ·
      refine ⟨41144159130502033789776083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27429439420334689193184055 41144159130502033789776083)
      ·
        refine ⟨61716238695753050684664125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41144159130502033789776083 61716238695753050684664125)
        ·
          refine ⟨23143589510907394006749047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61716238695753050684664125 23143589510907394006749047)
          ·
            refine ⟨34715384266361091010123571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23143589510907394006749047 34715384266361091010123571)
            ·
              refine ⟨52073076399541636515185357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34715384266361091010123571 52073076399541636515185357)
              ·
                refine ⟨19527403649828113693194509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52073076399541636515185357 19527403649828113693194509)
                ·
                  refine ⟨7322776368685542634947941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19527403649828113693194509 7322776368685542634947941)
                  ·
                    refine ⟨1373020569128539244052739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7322776368685542634947941 1373020569128539244052739)
                    ·
                      rfl

theorem cell23_8021844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_8021844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021844 prefixEnd_8021844 := by exact prefixLift 8021844
  have htrace : WordTrace (prefixWord ++ tailWord_8021844) baseStart_8021844 baseEnd_8021844 := by
    simpa [prefixWord, tailWord_8021844, baseEnd_8021844] using wordTrace_append hprefix tailTrace_8021844
  have hstable : (prefixWord ++ tailWord_8021844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021844).length < 2 ^ (prefixWord ++ tailWord_8021844).sum := by decide
  have hdescent : baseEnd_8021844 < baseStart_8021844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021880 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_8021880 : Nat := 118140960795 + 8021880 * 2 ^ 59
def prefixEnd_8021880 : Nat := 4983230072969 + 3 ^ 40 * 8021880 * 2
def baseEnd_8021880 : Nat := 4119080192689179591308051

theorem tailTrace_8021880 : CollatzResearch.WordTrace tailWord_8021880 prefixEnd_8021880 4119080192689179591308051 := by
  unfold tailWord_8021880
  simp only [CollatzResearch.WordTrace]
  refine ⟨146291000089053131437803547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195054666785404175250404729 146291000089053131437803547)
  ·
    refine ⟨219436500133579697156705321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146291000089053131437803547 219436500133579697156705321)
    ·
      refine ⟨164577375100184772867528991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219436500133579697156705321 164577375100184772867528991)
      ·
        refine ⟨246866062650277159301293487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164577375100184772867528991 246866062650277159301293487)
        ·
          refine ⟨370299093975415738951940231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246866062650277159301293487 370299093975415738951940231)
          ·
            refine ⟨555448640963123608427910347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370299093975415738951940231 555448640963123608427910347)
            ·
              refine ⟨833172961444685412641865521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555448640963123608427910347 833172961444685412641865521)
              ·
                refine ⟨624879721083514059481399141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833172961444685412641865521 624879721083514059481399141)
                ·
                  refine ⟨117164947703158886152762339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624879721083514059481399141 117164947703158886152762339)
                  ·
                    refine ⟨175747421554738329229143509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117164947703158886152762339 175747421554738329229143509)
                    ·
                      refine ⟨4119080192689179591308051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175747421554738329229143509 4119080192689179591308051)
                      ·
                        rfl

theorem cell23_8021880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_8021880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021880 prefixEnd_8021880 := by exact prefixLift 8021880
  have htrace : WordTrace (prefixWord ++ tailWord_8021880) baseStart_8021880 baseEnd_8021880 := by
    simpa [prefixWord, tailWord_8021880, baseEnd_8021880] using wordTrace_append hprefix tailTrace_8021880
  have hstable : (prefixWord ++ tailWord_8021880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021880).length < 2 ^ (prefixWord ++ tailWord_8021880).sum := by decide
  have hdescent : baseEnd_8021880 < baseStart_8021880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021924 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_8021924 : Nat := 118140960795 + 8021924 * 2 ^ 59
def prefixEnd_8021924 : Nat := 4983230072969 + 3 ^ 40 * 8021924 * 2
def baseEnd_8021924 : Nat := 4119102785837977419157849

theorem tailTrace_8021924 : CollatzResearch.WordTrace tailWord_8021924 prefixEnd_8021924 4119102785837977419157849 := by
  unfold tailWord_8021924
  simp only [CollatzResearch.WordTrace]
  refine ⟨146291802494973429195104413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195055736659964572260139217 146291802494973429195104413)
  ·
    refine ⟨54859425935615035948164155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146291802494973429195104413 54859425935615035948164155)
    ·
      refine ⟨82289138903422553922246233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54859425935615035948164155 82289138903422553922246233)
      ·
        refine ⟨61716854177566915441684675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82289138903422553922246233 61716854177566915441684675)
        ·
          refine ⟨92575281266350373162527013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61716854177566915441684675 92575281266350373162527013)
          ·
            refine ⟨17357865237440694967973815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92575281266350373162527013 17357865237440694967973815)
            ·
              refine ⟨26036797856161042451960723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17357865237440694967973815 26036797856161042451960723)
              ·
                refine ⟨39055196784241563677941085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26036797856161042451960723 39055196784241563677941085)
                ·
                  refine ⟨14645698794090586379227907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39055196784241563677941085 14645698794090586379227907)
                  ·
                    refine ⟨21968548191135879568841861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14645698794090586379227907 21968548191135879568841861)
                    ·
                      refine ⟨4119102785837977419157849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21968548191135879568841861 4119102785837977419157849)
                      ·
                        rfl

theorem cell23_8021924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_8021924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021924 prefixEnd_8021924 := by exact prefixLift 8021924
  have htrace : WordTrace (prefixWord ++ tailWord_8021924) baseStart_8021924 baseEnd_8021924 := by
    simpa [prefixWord, tailWord_8021924, baseEnd_8021924] using wordTrace_append hprefix tailTrace_8021924
  have hstable : (prefixWord ++ tailWord_8021924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021924).length < 2 ^ (prefixWord ++ tailWord_8021924).sum := by decide
  have hdescent : baseEnd_8021924 < baseStart_8021924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021964 : List Nat := [2, 2, 1, 4, 1, 4, 1, 8]
def baseStart_8021964 : Nat := 118140960795 + 8021964 * 2 ^ 59
def prefixEnd_8021964 : Nat := 4983230072969 + 3 ^ 40 * 8021964 * 2
def baseEnd_8021964 : Nat := 152560123150524343061395

theorem tailTrace_8021964 : CollatzResearch.WordTrace tailWord_8021964 prefixEnd_8021964 152560123150524343061395 := by
  unfold tailWord_8021964
  simp only [CollatzResearch.WordTrace]
  refine ⟨146292531954900972610832473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195056709273201296814443297 146292531954900972610832473)
  ·
    refine ⟨109719398966175729458124355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146292531954900972610832473 109719398966175729458124355)
    ·
      refine ⟨164579098449263594187186533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109719398966175729458124355 164579098449263594187186533)
      ·
        refine ⟨30858580959236923910097475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164579098449263594187186533 30858580959236923910097475)
        ·
          refine ⟨46287871438855385865146213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30858580959236923910097475 46287871438855385865146213)
          ·
            refine ⟨8678975894785384849714915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46287871438855385865146213 8678975894785384849714915)
            ·
              refine ⟨13018463842178077274572373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678975894785384849714915 13018463842178077274572373)
              ·
                refine ⟨152560123150524343061395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13018463842178077274572373 152560123150524343061395)
                ·
                  rfl

theorem cell23_8021964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 8].length) (baseStart_8021964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021964 prefixEnd_8021964 := by exact prefixLift 8021964
  have htrace : WordTrace (prefixWord ++ tailWord_8021964) baseStart_8021964 baseEnd_8021964 := by
    simpa [prefixWord, tailWord_8021964, baseEnd_8021964] using wordTrace_append hprefix tailTrace_8021964
  have hstable : (prefixWord ++ tailWord_8021964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021964).length < 2 ^ (prefixWord ++ tailWord_8021964).sum := by decide
  have hdescent : baseEnd_8021964 < baseStart_8021964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8021981 : List Nat := [1, 4, 3, 1, 3, 1, 3, 7]
def baseStart_8021981 : Nat := 118140960795 + 8021981 * 2 ^ 59
def prefixEnd_8021981 : Nat := 4983230072969 + 3 ^ 40 * 8021981 * 2
def baseEnd_8021981 : Nat := 152560446453158655412781

theorem tailTrace_8021981 : CollatzResearch.WordTrace tailWord_8021981 prefixEnd_8021981 152560446453158655412781 := by
  unfold tailWord_8021981
  simp only [CollatzResearch.WordTrace]
  refine ⟨292585683950740357125033797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195057122633826904750022531 292585683950740357125033797)
  ·
    refine ⟨54859815740763816960943837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292585683950740357125033797 54859815740763816960943837)
    ·
      refine ⟨20572430902786431360353939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54859815740763816960943837 20572430902786431360353939)
      ·
        refine ⟨30858646354179647040530909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20572430902786431360353939 30858646354179647040530909)
        ·
          refine ⟨11571992382817367640199091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30858646354179647040530909 11571992382817367640199091)
          ·
            refine ⟨17357988574226051460298637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11571992382817367640199091 17357988574226051460298637)
            ·
              refine ⟨6509245715334769297611989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17357988574226051460298637 6509245715334769297611989)
              ·
                refine ⟨152560446453158655412781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6509245715334769297611989 152560446453158655412781)
                ·
                  rfl

theorem cell23_8021981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 7].length) (baseStart_8021981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8021981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8021981 prefixEnd_8021981 := by exact prefixLift 8021981
  have htrace : WordTrace (prefixWord ++ tailWord_8021981) baseStart_8021981 baseEnd_8021981 := by
    simpa [prefixWord, tailWord_8021981, baseEnd_8021981] using wordTrace_append hprefix tailTrace_8021981
  have hstable : (prefixWord ++ tailWord_8021981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8021981).length < 2 ^ (prefixWord ++ tailWord_8021981).sum := by decide
  have hdescent : baseEnd_8021981 < baseStart_8021981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8021981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022101 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_8022101 : Nat := 118140960795 + 8022101 * 2 ^ 59
def prefixEnd_8022101 : Nat := 4983230072969 + 3 ^ 40 * 8022101 * 2
def baseEnd_8022101 : Nat := 1373064557304607742214845

theorem tailTrace_8022101 : CollatzResearch.WordTrace tailWord_8022101 prefixEnd_8022101 1373064557304607742214845 := by
  unfold tailWord_8022101
  simp only [CollatzResearch.WordTrace]
  refine ⟨292590060710305617619402157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195060040473537078412934771 292590060710305617619402157)
  ·
    refine ⟨109721272766364606607275809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292590060710305617619402157 109721272766364606607275809)
    ·
      refine ⟨82290954574773454955456857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109721272766364606607275809 82290954574773454955456857)
      ·
        refine ⟨61718215931080091216592643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82290954574773454955456857 61718215931080091216592643)
        ·
          refine ⟨92577323896620136824888965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61718215931080091216592643 92577323896620136824888965)
          ·
            refine ⟨17358248230616275654666681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92577323896620136824888965 17358248230616275654666681)
            ·
              refine ⟨13018686172962206741000011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17358248230616275654666681 13018686172962206741000011)
              ·
                refine ⟨19528029259443310111500017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13018686172962206741000011 19528029259443310111500017)
                ·
                  refine ⟨14646021944582482583625013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19528029259443310111500017 14646021944582482583625013)
                  ·
                    refine ⟨1373064557304607742214845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14646021944582482583625013 1373064557304607742214845)
                    ·
                      rfl

theorem cell23_8022101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_8022101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022101 prefixEnd_8022101 := by exact prefixLift 8022101
  have htrace : WordTrace (prefixWord ++ tailWord_8022101) baseStart_8022101 baseEnd_8022101 := by
    simpa [prefixWord, tailWord_8022101, baseEnd_8022101] using wordTrace_append hprefix tailTrace_8022101
  have hstable : (prefixWord ++ tailWord_8022101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022101).length < 2 ^ (prefixWord ++ tailWord_8022101).sum := by decide
  have hdescent : baseEnd_8022101 < baseStart_8022101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022121 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 2, 4, 2]
def baseStart_8022121 : Nat := 118140960795 + 8022121 * 2 ^ 59
def prefixEnd_8022121 : Nat := 4983230072969 + 3 ^ 40 * 8022121 * 2
def baseEnd_8022121 : Nat := 4119203941526913148394443

theorem tailTrace_8022121 : CollatzResearch.WordTrace tailWord_8022121 prefixEnd_8022121 4119203941526913148394443 := by
  unfold tailWord_8022121
  simp only [CollatzResearch.WordTrace]
  refine ⟨292590790170233161035130217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195060526780155440690086811 292590790170233161035130217)
  ·
    refine ⟨219443092627674870776347663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292590790170233161035130217 219443092627674870776347663)
    ·
      refine ⟨329164638941512306164521495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219443092627674870776347663 329164638941512306164521495)
      ·
        refine ⟨493746958412268459246782243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329164638941512306164521495 493746958412268459246782243)
        ·
          refine ⟨740620437618402688870173365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493746958412268459246782243 740620437618402688870173365)
          ·
            refine ⟨69433166026725252081578753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 740620437618402688870173365 69433166026725252081578753)
            ·
              refine ⟨52074874520043939061184065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69433166026725252081578753 52074874520043939061184065)
              ·
                refine ⟨39056155890032954295888049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52074874520043939061184065 39056155890032954295888049)
                ·
                  refine ⟨29292116917524715721916037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39056155890032954295888049 29292116917524715721916037)
                  ·
                    refine ⟨5492271922035884197859257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29292116917524715721916037 5492271922035884197859257)
                    ·
                      refine ⟨4119203941526913148394443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492271922035884197859257 4119203941526913148394443)
                      ·
                        rfl

theorem cell23_8022121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 4, 2].length) (baseStart_8022121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022121 prefixEnd_8022121 := by exact prefixLift 8022121
  have htrace : WordTrace (prefixWord ++ tailWord_8022121) baseStart_8022121 baseEnd_8022121 := by
    simpa [prefixWord, tailWord_8022121, baseEnd_8022121] using wordTrace_append hprefix tailTrace_8022121
  have hstable : (prefixWord ++ tailWord_8022121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022121).length < 2 ^ (prefixWord ++ tailWord_8022121).sum := by decide
  have hdescent : baseEnd_8022121 < baseStart_8022121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022122 : List Nat := [3, 1, 3, 2, 4, 1, 2, 2, 5]
def baseStart_8022122 : Nat := 118140960795 + 8022122 * 2 ^ 59
def prefixEnd_8022122 : Nat := 4983230072969 + 3 ^ 40 * 8022122 * 2
def baseEnd_8022122 : Nat := 457689383889729738275771

theorem tailTrace_8022122 : CollatzResearch.WordTrace tailWord_8022122 prefixEnd_8022122 457689383889729738275771 := by
  unfold tailWord_8022122
  simp only [CollatzResearch.WordTrace]
  refine ⟨73147706660807384551479155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195060551095486358803944413 73147706660807384551479155)
  ·
    refine ⟨109721559991211076827218733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73147706660807384551479155 109721559991211076827218733)
    ·
      refine ⟨41145584996704153810207025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109721559991211076827218733 41145584996704153810207025)
      ·
        refine ⟨30859188747528115357655269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41145584996704153810207025 30859188747528115357655269)
        ·
          refine ⟨5786097890161521629560363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30859188747528115357655269 5786097890161521629560363)
          ·
            refine ⟨8679146835242282444340545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786097890161521629560363 8679146835242282444340545)
            ·
              refine ⟨6509360126431711833255409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8679146835242282444340545 6509360126431711833255409)
              ·
                refine ⟨4882020094823783874941557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509360126431711833255409 4882020094823783874941557)
                ·
                  refine ⟨457689383889729738275771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4882020094823783874941557 457689383889729738275771)
                  ·
                    rfl

theorem cell23_8022122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_8022122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022122 prefixEnd_8022122 := by exact prefixLift 8022122
  have htrace : WordTrace (prefixWord ++ tailWord_8022122) baseStart_8022122 baseEnd_8022122 := by
    simpa [prefixWord, tailWord_8022122, baseEnd_8022122] using wordTrace_append hprefix tailTrace_8022122
  have hstable : (prefixWord ++ tailWord_8022122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022122).length < 2 ^ (prefixWord ++ tailWord_8022122).sum := by decide
  have hdescent : baseEnd_8022122 < baseStart_8022122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022158 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_8022158 : Nat := 118140960795 + 8022158 * 2 ^ 59
def prefixEnd_8022158 : Nat := 4983230072969 + 3 ^ 40 * 8022158 * 2
def baseEnd_8022158 : Nat := 4119222940311129503631773

theorem tailTrace_8022158 : CollatzResearch.WordTrace tailWord_8022158 prefixEnd_8022158 4119222940311129503631773 := by
  unfold tailWord_8022158
  simp only [CollatzResearch.WordTrace]
  refine ⟨36574017458887389544278391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195061426447399410902818085 36574017458887389544278391)
  ·
    refine ⟨54861026188331084316417587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36574017458887389544278391 54861026188331084316417587)
    ·
      refine ⟨82291539282496626474626381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54861026188331084316417587 82291539282496626474626381)
      ·
        refine ⟨30859327230936234927984893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82291539282496626474626381 30859327230936234927984893)
        ·
          refine ⟨11572247711601088097994335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30859327230936234927984893 11572247711601088097994335)
          ·
            refine ⟨17358371567401632146991503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11572247711601088097994335 17358371567401632146991503)
            ·
              refine ⟨26037557351102448220487255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17358371567401632146991503 26037557351102448220487255)
              ·
                refine ⟨39056336026653672330730883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26037557351102448220487255 39056336026653672330730883)
                ·
                  refine ⟨58584504039980508496096325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39056336026653672330730883 58584504039980508496096325)
                  ·
                    refine ⟨10984594507496345343018061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58584504039980508496096325 10984594507496345343018061)
                    ·
                      refine ⟨4119222940311129503631773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10984594507496345343018061 4119222940311129503631773)
                      ·
                        rfl

theorem cell23_8022158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_8022158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022158 prefixEnd_8022158 := by exact prefixLift 8022158
  have htrace : WordTrace (prefixWord ++ tailWord_8022158) baseStart_8022158 baseEnd_8022158 := by
    simpa [prefixWord, tailWord_8022158, baseEnd_8022158] using wordTrace_append hprefix tailTrace_8022158
  have hstable : (prefixWord ++ tailWord_8022158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022158).length < 2 ^ (prefixWord ++ tailWord_8022158).sum := by decide
  have hdescent : baseEnd_8022158 < baseStart_8022158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022171 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 3]
def baseStart_8022171 : Nat := 118140960795 + 8022171 * 2 ^ 59
def prefixEnd_8022171 : Nat := 4983230072969 + 3 ^ 40 * 8022171 * 2
def baseEnd_8022171 : Nat := 4119229615559637952769213

theorem tailTrace_8022171 : CollatzResearch.WordTrace tailWord_8022171 prefixEnd_8022171 4119229615559637952769213 := by
  unfold tailWord_8022171
  simp only [CollatzResearch.WordTrace]
  refine ⟨292592613820052019574450367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195061742546701346382966911 292592613820052019574450367)
  ·
    refine ⟨438888920730078029361675551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292592613820052019574450367 438888920730078029361675551)
    ·
      refine ⟨658333381095117044042513327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438888920730078029361675551 658333381095117044042513327)
      ·
        refine ⟨987500071642675566063769991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658333381095117044042513327 987500071642675566063769991)
        ·
          refine ⟨1481250107464013349095654987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987500071642675566063769991 1481250107464013349095654987)
          ·
            refine ⟨2221875161196020023643482481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481250107464013349095654987 2221875161196020023643482481)
            ·
              refine ⟨1666406370897015017732611861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2221875161196020023643482481 1666406370897015017732611861)
              ·
                refine ⟨78112798635797578956216181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1666406370897015017732611861 78112798635797578956216181)
                ·
                  refine ⟨7323074872106023027145267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78112798635797578956216181 7323074872106023027145267)
                  ·
                    refine ⟨10984612308159034540717901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323074872106023027145267 10984612308159034540717901)
                    ·
                      refine ⟨4119229615559637952769213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10984612308159034540717901 4119229615559637952769213)
                      ·
                        rfl

theorem cell23_8022171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 3].length) (baseStart_8022171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022171 prefixEnd_8022171 := by exact prefixLift 8022171
  have htrace : WordTrace (prefixWord ++ tailWord_8022171) baseStart_8022171 baseEnd_8022171 := by
    simpa [prefixWord, tailWord_8022171, baseEnd_8022171] using wordTrace_append hprefix tailTrace_8022171
  have hstable : (prefixWord ++ tailWord_8022171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022171).length < 2 ^ (prefixWord ++ tailWord_8022171).sum := by decide
  have hdescent : baseEnd_8022171 < baseStart_8022171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022178 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 6]
def baseStart_8022178 : Nat := 118140960795 + 8022178 * 2 ^ 59
def prefixEnd_8022178 : Nat := 4983230072969 + 3 ^ 40 * 8022178 * 2
def baseEnd_8022178 : Nat := 457692578880468825042409

theorem tailTrace_8022178 : CollatzResearch.WordTrace tailWord_8022178 prefixEnd_8022178 457692578880468825042409 := by
  unfold tailWord_8022178
  simp only [CollatzResearch.WordTrace]
  refine ⟨73148217282756664942488797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195061912754017773179970125 73148217282756664942488797)
  ·
    refine ⟨27430581481033749353433299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73148217282756664942488797 27430581481033749353433299)
    ·
      refine ⟨41145872221550624030149949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27430581481033749353433299 41145872221550624030149949)
      ·
        refine ⟨15429702083081484011306231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41145872221550624030149949 15429702083081484011306231)
        ·
          refine ⟨23144553124622226016959347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15429702083081484011306231 23144553124622226016959347)
          ·
            refine ⟨34716829686933339025439021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23144553124622226016959347 34716829686933339025439021)
            ·
              refine ⟨13018811132600002134539633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34716829686933339025439021 13018811132600002134539633)
              ·
                refine ⟨9764108349450001600904725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13018811132600002134539633 9764108349450001600904725)
                ·
                  refine ⟨457692578880468825042409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9764108349450001600904725 457692578880468825042409)
                  ·
                    rfl

theorem cell23_8022178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_8022178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022178 prefixEnd_8022178 := by exact prefixLift 8022178
  have htrace : WordTrace (prefixWord ++ tailWord_8022178) baseStart_8022178 baseEnd_8022178 := by
    simpa [prefixWord, tailWord_8022178, baseEnd_8022178] using wordTrace_append hprefix tailTrace_8022178
  have hstable : (prefixWord ++ tailWord_8022178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022178).length < 2 ^ (prefixWord ++ tailWord_8022178).sum := by decide
  have hdescent : baseEnd_8022178 < baseStart_8022178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022208 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 1, 5]
def baseStart_8022208 : Nat := 118140960795 + 8022208 * 2 ^ 59
def prefixEnd_8022208 : Nat := 4983230072969 + 3 ^ 40 * 8022208 * 2
def baseEnd_8022208 : Nat := 1373082871447951436002181

theorem tailTrace_8022208 : CollatzResearch.WordTrace tailWord_8022208 prefixEnd_8022208 1373082871447951436002181 := by
  unfold tailWord_8022208
  simp only [CollatzResearch.WordTrace]
  refine ⟨146296981660458987446773639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195062642213945316595698185 146296981660458987446773639)
  ·
    refine ⟨219445472490688481170160459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146296981660458987446773639 219445472490688481170160459)
    ·
      refine ⟨329168208736032721755240689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219445472490688481170160459 329168208736032721755240689)
      ·
        refine ⟨246876156552024541316430517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329168208736032721755240689 246876156552024541316430517)
        ·
          refine ⟨23144639676752300748415361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246876156552024541316430517 23144639676752300748415361)
          ·
            refine ⟨17358479757564225561311521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23144639676752300748415361 17358479757564225561311521)
            ·
              refine ⟨13018859818173169170983641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17358479757564225561311521 13018859818173169170983641)
              ·
                refine ⟨9764144863629876878237731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13018859818173169170983641 9764144863629876878237731)
                ·
                  refine ⟨14646217295444815317356597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764144863629876878237731 14646217295444815317356597)
                  ·
                    refine ⟨1373082871447951436002181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14646217295444815317356597 1373082871447951436002181)
                    ·
                      rfl

theorem cell23_8022208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_8022208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022208 prefixEnd_8022208 := by exact prefixLift 8022208
  have htrace : WordTrace (prefixWord ++ tailWord_8022208) baseStart_8022208 baseEnd_8022208 := by
    simpa [prefixWord, tailWord_8022208, baseEnd_8022208] using wordTrace_append hprefix tailTrace_8022208
  have hstable : (prefixWord ++ tailWord_8022208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022208).length < 2 ^ (prefixWord ++ tailWord_8022208).sum := by decide
  have hdescent : baseEnd_8022208 < baseStart_8022208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022222 : List Nat := [4, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_8022222 : Nat := 118140960795 + 8022222 * 2 ^ 59
def prefixEnd_8022222 : Nat := 4983230072969 + 3 ^ 40 * 8022222 * 2
def baseEnd_8022222 : Nat := 4119255803073017253231479

theorem tailTrace_8022222 : CollatzResearch.WordTrace tailWord_8022222 prefixEnd_8022222 4119255803073017253231479 := by
  unfold tailWord_8022222
  simp only [CollatzResearch.WordTrace]
  refine ⟨36574309242858406910569615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195062982628578170189704613 36574309242858406910569615)
  ·
    refine ⟨54861463864287610365854423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36574309242858406910569615 54861463864287610365854423)
    ·
      refine ⟨82292195796431415548781635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54861463864287610365854423 82292195796431415548781635)
      ·
        refine ⟨123438293694647123323172453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82292195796431415548781635 123438293694647123323172453)
        ·
          refine ⟨23144680067746335623094835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123438293694647123323172453 23144680067746335623094835)
          ·
            refine ⟨34717020101619503434642253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23144680067746335623094835 34717020101619503434642253)
            ·
              refine ⟨13018882538107313787990845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34717020101619503434642253 13018882538107313787990845)
              ·
                refine ⟨4882080951790242670496567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13018882538107313787990845 4882080951790242670496567)
                ·
                  refine ⟨7323121427685364005744851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882080951790242670496567 7323121427685364005744851)
                  ·
                    refine ⟨10984682141528046008617277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323121427685364005744851 10984682141528046008617277)
                    ·
                      refine ⟨4119255803073017253231479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10984682141528046008617277 4119255803073017253231479)
                      ·
                        rfl

theorem cell23_8022222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_8022222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022222 prefixEnd_8022222 := by exact prefixLift 8022222
  have htrace : WordTrace (prefixWord ++ tailWord_8022222) baseStart_8022222 baseEnd_8022222 := by
    simpa [prefixWord, tailWord_8022222, baseEnd_8022222] using wordTrace_append hprefix tailTrace_8022222
  have hstable : (prefixWord ++ tailWord_8022222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022222).length < 2 ^ (prefixWord ++ tailWord_8022222).sum := by decide
  have hdescent : baseEnd_8022222 < baseStart_8022222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022231 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_8022231 : Nat := 118140960795 + 8022231 * 2 ^ 59
def prefixEnd_8022231 : Nat := 4983230072969 + 3 ^ 40 * 8022231 * 2
def baseEnd_8022231 : Nat := 4119260424398907718018937

theorem tailTrace_8022231 : CollatzResearch.WordTrace tailWord_8022231 prefixEnd_8022231 4119260424398907718018937 := by
  unfold tailWord_8022231
  simp only [CollatzResearch.WordTrace]
  refine ⟨292594802199834649821634547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195063201466556433214423031 292594802199834649821634547)
  ·
    refine ⟨438892203299751974732451821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292594802199834649821634547 438892203299751974732451821)
    ·
      refine ⟨164584576237406990524669433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438892203299751974732451821 164584576237406990524669433)
      ·
        refine ⟨123438432178055242893502075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164584576237406990524669433 123438432178055242893502075)
        ·
          refine ⟨185157648267082864340253113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123438432178055242893502075 185157648267082864340253113)
          ·
            refine ⟨138868236200312148255189835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185157648267082864340253113 138868236200312148255189835)
            ·
              refine ⟨208302354300468222382784753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138868236200312148255189835 208302354300468222382784753)
              ·
                refine ⟨156226765725351166787088565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208302354300468222382784753 156226765725351166787088565)
                ·
                  refine ⟨14646259286751671886289553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156226765725351166787088565 14646259286751671886289553)
                  ·
                    refine ⟨10984694465063753914717165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14646259286751671886289553 10984694465063753914717165)
                    ·
                      refine ⟨4119260424398907718018937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10984694465063753914717165 4119260424398907718018937)
                      ·
                        rfl

theorem cell23_8022231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_8022231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022231 prefixEnd_8022231 := by exact prefixLift 8022231
  have htrace : WordTrace (prefixWord ++ tailWord_8022231) baseStart_8022231 baseEnd_8022231 := by
    simpa [prefixWord, tailWord_8022231, baseEnd_8022231] using wordTrace_append hprefix tailTrace_8022231
  have hstable : (prefixWord ++ tailWord_8022231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022231).length < 2 ^ (prefixWord ++ tailWord_8022231).sum := by decide
  have hdescent : baseEnd_8022231 < baseStart_8022231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022234 : List Nat := [3, 1, 1, 2, 2, 1, 13]
def baseStart_8022234 : Nat := 118140960795 + 8022234 * 2 ^ 59
def prefixEnd_8022234 : Nat := 4983230072969 + 3 ^ 40 * 8022234 * 2
def baseEnd_8022234 : Nat := 50855085985689767978783

theorem tailTrace_8022234 : CollatzResearch.WordTrace tailWord_8022234 prefixEnd_8022234 50855085985689767978783 := by
  unfold tailWord_8022234
  simp only [CollatzResearch.WordTrace]
  refine ⟨73148727904705945333498439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195063274412549187555995837 73148727904705945333498439)
  ·
    refine ⟨109723091857058918000247659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73148727904705945333498439 109723091857058918000247659)
    ·
      refine ⟨164584637785588377000371489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109723091857058918000247659 164584637785588377000371489)
      ·
        refine ⟨123438478339191282750278617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164584637785588377000371489 123438478339191282750278617)
        ·
          refine ⟨92578858754393462062708963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123438478339191282750278617 92578858754393462062708963)
          ·
            refine ⟨138868288131590193094063445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92578858754393462062708963 138868288131590193094063445)
            ·
              refine ⟨50855085985689767978783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 138868288131590193094063445 50855085985689767978783)
              ·
                rfl

theorem cell23_8022234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 13].length) (baseStart_8022234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022234 prefixEnd_8022234 := by exact prefixLift 8022234
  have htrace : WordTrace (prefixWord ++ tailWord_8022234) baseStart_8022234 baseEnd_8022234 := by
    simpa [prefixWord, tailWord_8022234, baseEnd_8022234] using wordTrace_append hprefix tailTrace_8022234
  have hstable : (prefixWord ++ tailWord_8022234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022234).length < 2 ^ (prefixWord ++ tailWord_8022234).sum := by decide
  have hdescent : baseEnd_8022234 < baseStart_8022234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022255 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 2, 4]
def baseStart_8022255 : Nat := 118140960795 + 8022255 * 2 ^ 59
def prefixEnd_8022255 : Nat := 4983230072969 + 3 ^ 40 * 8022255 * 2
def baseEnd_8022255 : Nat := 1373090915978205208039609

theorem tailTrace_8022255 : CollatzResearch.WordTrace tailWord_8022255 prefixEnd_8022255 1373090915978205208039609 := by
  unfold tailWord_8022255
  simp only [CollatzResearch.WordTrace]
  refine ⟨292595677551747701920508219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195063785034498467947005479 292595677551747701920508219)
  ·
    refine ⟨438893516327621552880762329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292595677551747701920508219 438893516327621552880762329)
    ·
      refine ⟨329170137245716164660571747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438893516327621552880762329 329170137245716164660571747)
      ·
        refine ⟨493755205868574246990857621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329170137245716164660571747 493755205868574246990857621)
        ·
          refine ⟨23144775275089417827696451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 493755205868574246990857621 23144775275089417827696451)
          ·
            refine ⟨34717162912634126741544677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23144775275089417827696451 34717162912634126741544677)
            ·
              refine ⟨6509468046118898764039627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34717162912634126741544677 6509468046118898764039627)
              ·
                refine ⟨9764202069178348146059441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509468046118898764039627 9764202069178348146059441)
                ·
                  refine ⟨7323151551883761109544581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9764202069178348146059441 7323151551883761109544581)
                  ·
                    refine ⟨1373090915978205208039609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7323151551883761109544581 1373090915978205208039609)
                    ·
                      rfl

theorem cell23_8022255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 4].length) (baseStart_8022255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022255 prefixEnd_8022255 := by exact prefixLift 8022255
  have htrace : WordTrace (prefixWord ++ tailWord_8022255) baseStart_8022255 baseEnd_8022255 := by
    simpa [prefixWord, tailWord_8022255, baseEnd_8022255] using wordTrace_append hprefix tailTrace_8022255
  have hstable : (prefixWord ++ tailWord_8022255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022255).length < 2 ^ (prefixWord ++ tailWord_8022255).sum := by decide
  have hdescent : baseEnd_8022255 < baseStart_8022255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022295 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_8022295 : Nat := 118140960795 + 8022295 * 2 ^ 59
def prefixEnd_8022295 : Nat := 4983230072969 + 3 ^ 40 * 8022295 * 2
def baseEnd_8022295 : Nat := 4119293287160795467618643

theorem tailTrace_8022295 : CollatzResearch.WordTrace tailWord_8022295 prefixEnd_8022295 4119293287160795467618643 := by
  unfold tailWord_8022295
  simp only [CollatzResearch.WordTrace]
  refine ⟨292597136471602788751964339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195064757647735192501309559 292597136471602788751964339)
  ·
    refine ⟨438895704707404183127946509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292597136471602788751964339 438895704707404183127946509)
    ·
      refine ⟨164585889265276568672979941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438895704707404183127946509 164585889265276568672979941)
      ·
        refine ⟨30859854237239356626183739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164585889265276568672979941 30859854237239356626183739)
        ·
          refine ⟨46289781355859034939275609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30859854237239356626183739 46289781355859034939275609)
          ·
            refine ⟨34717336016894276204456707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46289781355859034939275609 34717336016894276204456707)
            ·
              refine ⟨52076004025341414306685061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34717336016894276204456707 52076004025341414306685061)
              ·
                refine ⟨9764250754751515182503449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52076004025341414306685061 9764250754751515182503449)
                ·
                  refine ⟨7323188066063636386877587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9764250754751515182503449 7323188066063636386877587)
                  ·
                    refine ⟨10984782099095454580316381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323188066063636386877587 10984782099095454580316381)
                    ·
                      refine ⟨4119293287160795467618643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10984782099095454580316381 4119293287160795467618643)
                      ·
                        rfl

theorem cell23_8022295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_8022295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022295 prefixEnd_8022295 := by exact prefixLift 8022295
  have htrace : WordTrace (prefixWord ++ tailWord_8022295) baseStart_8022295 baseEnd_8022295 := by
    simpa [prefixWord, tailWord_8022295, baseEnd_8022295] using wordTrace_append hprefix tailTrace_8022295
  have hstable : (prefixWord ++ tailWord_8022295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022295).length < 2 ^ (prefixWord ++ tailWord_8022295).sum := by decide
  have hdescent : baseEnd_8022295 < baseStart_8022295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022335 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 4, 2, 2]
def baseStart_8022335 : Nat := 118140960795 + 8022335 * 2 ^ 59
def prefixEnd_8022335 : Nat := 4983230072969 + 3 ^ 40 * 8022335 * 2
def baseEnd_8022335 : Nat := 4119313826386975311118459

theorem tailTrace_8022335 : CollatzResearch.WordTrace tailWord_8022335 prefixEnd_8022335 4119313826386975311118459 := by
  unfold tailWord_8022335
  simp only [CollatzResearch.WordTrace]
  refine ⟨292598595391457875583420459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195065730260971917055613639 292598595391457875583420459)
  ·
    refine ⟨438897893087186813375130689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292598595391457875583420459 438897893087186813375130689)
    ·
      refine ⟨329173419815390110031348017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438897893087186813375130689 329173419815390110031348017)
      ·
        refine ⟨246880064861542582523511013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329173419815390110031348017 246880064861542582523511013)
        ·
          refine ⟨46290012161539234223158315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246880064861542582523511013 46290012161539234223158315)
          ·
            refine ⟨69435018242308851334737473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46290012161539234223158315 69435018242308851334737473)
            ·
              refine ⟨52076263681731638501053105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69435018242308851334737473 52076263681731638501053105)
              ·
                refine ⟨39057197761298728875789829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52076263681731638501053105 39057197761298728875789829)
                ·
                  refine ⟨7323224580243511664210593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39057197761298728875789829 7323224580243511664210593)
                  ·
                    refine ⟨5492418435182633748157945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7323224580243511664210593 5492418435182633748157945)
                    ·
                      refine ⟨4119313826386975311118459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492418435182633748157945 4119313826386975311118459)
                      ·
                        rfl

theorem cell23_8022335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_8022335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022335 prefixEnd_8022335 := by exact prefixLift 8022335
  have htrace : WordTrace (prefixWord ++ tailWord_8022335) baseStart_8022335 baseEnd_8022335 := by
    simpa [prefixWord, tailWord_8022335, baseEnd_8022335] using wordTrace_append hprefix tailTrace_8022335
  have hstable : (prefixWord ++ tailWord_8022335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022335).length < 2 ^ (prefixWord ++ tailWord_8022335).sum := by decide
  have hdescent : baseEnd_8022335 < baseStart_8022335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022352 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 2, 2, 2]
def baseStart_8022352 : Nat := 118140960795 + 8022352 * 2 ^ 59
def prefixEnd_8022352 : Nat := 4983230072969 + 3 ^ 40 * 8022352 * 2
def baseEnd_8022352 : Nat := 4119322555558101744605881

theorem tailTrace_8022352 : CollatzResearch.WordTrace tailWord_8022352 prefixEnd_8022352 4119322555558101744605881 := by
  unfold tailWord_8022352
  simp only [CollatzResearch.WordTrace]
  refine ⟨146299607716198143743394655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195066143621597524991192873 146299607716198143743394655)
  ·
    refine ⟨219449411574297215615091983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146299607716198143743394655 219449411574297215615091983)
    ·
      refine ⟨329174117361445823422637975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219449411574297215615091983 329174117361445823422637975)
      ·
        refine ⟨493761176042168735133956963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329174117361445823422637975 493761176042168735133956963)
        ·
          refine ⟨740641764063253102700935445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493761176042168735133956963 740641764063253102700935445)
          ·
            refine ⟨34717582690464989189106349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 740641764063253102700935445 34717582690464989189106349)
            ·
              refine ⟨13019093508924370945914881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34717582690464989189106349 13019093508924370945914881)
              ·
                refine ⟨9764320131693278209436161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13019093508924370945914881 9764320131693278209436161)
                ·
                  refine ⟨7323240098769958657077121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9764320131693278209436161 7323240098769958657077121)
                  ·
                    refine ⟨5492430074077468992807841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7323240098769958657077121 5492430074077468992807841)
                    ·
                      refine ⟨4119322555558101744605881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492430074077468992807841 4119322555558101744605881)
                      ·
                        rfl

theorem cell23_8022352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 2, 2].length) (baseStart_8022352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022352 prefixEnd_8022352 := by exact prefixLift 8022352
  have htrace : WordTrace (prefixWord ++ tailWord_8022352) baseStart_8022352 baseEnd_8022352 := by
    simpa [prefixWord, tailWord_8022352, baseEnd_8022352] using wordTrace_append hprefix tailTrace_8022352
  have hstable : (prefixWord ++ tailWord_8022352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022352).length < 2 ^ (prefixWord ++ tailWord_8022352).sum := by decide
  have hdescent : baseEnd_8022352 < baseStart_8022352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022371 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 3, 7]
def baseStart_8022371 : Nat := 118140960795 + 8022371 * 2 ^ 59
def prefixEnd_8022371 : Nat := 4983230072969 + 3 ^ 40 * 8022371 * 2
def baseEnd_8022371 : Nat := 1373110770563512390089431

theorem tailTrace_8022371 : CollatzResearch.WordTrace tailWord_8022371 prefixEnd_8022371 1373110770563512390089431 := by
  unfold tailWord_8022371
  simp only [CollatzResearch.WordTrace]
  refine ⟨292599908419327453731730967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195066605612884969154487311 292599908419327453731730967)
  ·
    refine ⟨438899862628991180597596451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292599908419327453731730967 438899862628991180597596451)
    ·
      refine ⟨658349793943486770896394677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438899862628991180597596451 658349793943486770896394677)
      ·
        refine ⟨61720293182201884771537001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 658349793943486770896394677 61720293182201884771537001)
        ·
          refine ⟨46290219886651413578652751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61720293182201884771537001 46290219886651413578652751)
          ·
            refine ⟨69435329829977120367979127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46290219886651413578652751 69435329829977120367979127)
            ·
              refine ⟨104152994744965680551968691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69435329829977120367979127 104152994744965680551968691)
              ·
                refine ⟨156229492117448520827953037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104152994744965680551968691 156229492117448520827953037)
                ·
                  refine ⟨58586059544043195310482389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156229492117448520827953037 58586059544043195310482389)
                  ·
                    refine ⟨1373110770563512390089431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58586059544043195310482389 1373110770563512390089431)
                    ·
                      rfl

theorem cell23_8022371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 7].length) (baseStart_8022371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022371 prefixEnd_8022371 := by exact prefixLift 8022371
  have htrace : WordTrace (prefixWord ++ tailWord_8022371) baseStart_8022371 baseEnd_8022371 := by
    simpa [prefixWord, tailWord_8022371, baseEnd_8022371] using wordTrace_append hprefix tailTrace_8022371
  have hstable : (prefixWord ++ tailWord_8022371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022371).length < 2 ^ (prefixWord ++ tailWord_8022371).sum := by decide
  have hdescent : baseEnd_8022371 < baseStart_8022371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022451 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8]
def baseStart_8022451 : Nat := 118140960795 + 8022451 * 2 ^ 59
def prefixEnd_8022451 : Nat := 4983230072969 + 3 ^ 40 * 8022451 * 2
def baseEnd_8022451 : Nat := 4119373390142896857267925

theorem tailTrace_8022451 : CollatzResearch.WordTrace tailWord_8022451 prefixEnd_8022451 4119373390142896857267925 := by
  unfold tailWord_8022451
  simp only [CollatzResearch.WordTrace]
  refine ⟨292602826259037627394643207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195068550839358418263095471 292602826259037627394643207)
  ·
    refine ⟨438904239388556441091964811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292602826259037627394643207 438904239388556441091964811)
    ·
      refine ⟨658356359082834661637947217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438904239388556441091964811 658356359082834661637947217)
      ·
        refine ⟨493767269312125996228460413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658356359082834661637947217 493767269312125996228460413)
        ·
          refine ⟨185162725992047248585672655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493767269312125996228460413 185162725992047248585672655)
          ·
            refine ⟨277744088988070872878508983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185162725992047248585672655 277744088988070872878508983)
            ·
              refine ⟨416616133482106309317763475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277744088988070872878508983 416616133482106309317763475)
              ·
                refine ⟨624924200223159463976645213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416616133482106309317763475 624924200223159463976645213)
                ·
                  refine ⟨234346575083684798991241955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624924200223159463976645213 234346575083684798991241955)
                  ·
                    refine ⟨351519862625527198486862933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234346575083684798991241955 351519862625527198486862933)
                    ·
                      refine ⟨4119373390142896857267925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 351519862625527198486862933 4119373390142896857267925)
                      ·
                        rfl

theorem cell23_8022451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_8022451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022451 prefixEnd_8022451 := by exact prefixLift 8022451
  have htrace : WordTrace (prefixWord ++ tailWord_8022451) baseStart_8022451 baseEnd_8022451 := by
    simpa [prefixWord, tailWord_8022451, baseEnd_8022451] using wordTrace_append hprefix tailTrace_8022451
  have hstable : (prefixWord ++ tailWord_8022451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022451).length < 2 ^ (prefixWord ++ tailWord_8022451).sum := by decide
  have hdescent : baseEnd_8022451 < baseStart_8022451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022475 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 3]
def baseStart_8022475 : Nat := 118140960795 + 8022475 * 2 ^ 59
def prefixEnd_8022475 : Nat := 4983230072969 + 3 ^ 40 * 8022475 * 2
def baseEnd_8022475 : Nat := 4119385713678604763367815

theorem tailTrace_8022475 : CollatzResearch.WordTrace tailWord_8022475 prefixEnd_8022475 4119385713678604763367815 := by
  unfold tailWord_8022475
  simp only [CollatzResearch.WordTrace]
  refine ⟨292603701610950679493516879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195069134407300452995677919 292603701610950679493516879)
  ·
    refine ⟨438905552416426019240275319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292603701610950679493516879 438905552416426019240275319)
    ·
      refine ⟨658358328624639028860412979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438905552416426019240275319 658358328624639028860412979)
      ·
        refine ⟨987537492936958543290619469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658358328624639028860412979 987537492936958543290619469)
        ·
          refine ⟨370326559851359453733982301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 987537492936958543290619469 370326559851359453733982301)
          ·
            refine ⟨138872459944259795150243363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370326559851359453733982301 138872459944259795150243363)
            ·
              refine ⟨208308689916389692725365045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138872459944259795150243363 208308689916389692725365045)
              ·
                refine ⟨19528939679661533693002973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208308689916389692725365045 19528939679661533693002973)
                ·
                  refine ⟨7323352379873075134876115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19528939679661533693002973 7323352379873075134876115)
                  ·
                    refine ⟨10985028569809612702314173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323352379873075134876115 10985028569809612702314173)
                    ·
                      refine ⟨4119385713678604763367815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10985028569809612702314173 4119385713678604763367815)
                      ·
                        rfl

theorem cell23_8022475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 3].length) (baseStart_8022475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022475 prefixEnd_8022475 := by exact prefixLift 8022475
  have htrace : WordTrace (prefixWord ++ tailWord_8022475) baseStart_8022475 baseEnd_8022475 := by
    simpa [prefixWord, tailWord_8022475, baseEnd_8022475] using wordTrace_append hprefix tailTrace_8022475
  have hstable : (prefixWord ++ tailWord_8022475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022475).length < 2 ^ (prefixWord ++ tailWord_8022475).sum := by decide
  have hdescent : baseEnd_8022475 < baseStart_8022475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022508 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_8022508 : Nat := 118140960795 + 8022508 * 2 ^ 59
def prefixEnd_8022508 : Nat := 4983230072969 + 3 ^ 40 * 8022508 * 2
def baseEnd_8022508 : Nat := 1373134219513401044751721

theorem tailTrace_8022508 : CollatzResearch.WordTrace tailWord_8022508 prefixEnd_8022508 1373134219513401044751721 := by
  unfold tailWord_8022508
  simp only [CollatzResearch.WordTrace]
  refine ⟨146302452609915563064734089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195069936813220750752978785 146302452609915563064734089)
  ·
    refine ⟨109726839457436672298550567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146302452609915563064734089 109726839457436672298550567)
    ·
      refine ⟨164590259186155008447825851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109726839457436672298550567 164590259186155008447825851)
      ·
        refine ⟨246885388779232512671738777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164590259186155008447825851 246885388779232512671738777)
        ·
          refine ⟨185164041584424384503804083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246885388779232512671738777 185164041584424384503804083)
          ·
            refine ⟨277746062376636576755706125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185164041584424384503804083 277746062376636576755706125)
            ·
              refine ⟨104154773391238716283389797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277746062376636576755706125 104154773391238716283389797)
              ·
                refine ⟨19529020010857259303135587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104154773391238716283389797 19529020010857259303135587)
                ·
                  refine ⟨29293530016285888954703381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19529020010857259303135587 29293530016285888954703381)
                  ·
                    refine ⟨1373134219513401044751721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29293530016285888954703381 1373134219513401044751721)
                    ·
                      rfl

theorem cell23_8022508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_8022508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022508 prefixEnd_8022508 := by exact prefixLift 8022508
  have htrace : WordTrace (prefixWord ++ tailWord_8022508) baseStart_8022508 baseEnd_8022508 := by
    simpa [prefixWord, tailWord_8022508, baseEnd_8022508] using wordTrace_append hprefix tailTrace_8022508
  have hstable : (prefixWord ++ tailWord_8022508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022508).length < 2 ^ (prefixWord ++ tailWord_8022508).sum := by decide
  have hdescent : baseEnd_8022508 < baseStart_8022508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022515 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 4]
def baseStart_8022515 : Nat := 118140960795 + 8022515 * 2 ^ 59
def prefixEnd_8022515 : Nat := 4983230072969 + 3 ^ 40 * 8022515 * 2
def baseEnd_8022515 : Nat := 4119406252904784606867631

theorem tailTrace_8022515 : CollatzResearch.WordTrace tailWord_8022515 prefixEnd_8022515 4119406252904784606867631 := by
  unfold tailWord_8022515
  simp only [CollatzResearch.WordTrace]
  refine ⟨292605160530805766324972999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195070107020537177549981999 292605160530805766324972999)
  ·
    refine ⟨438907740796208649487459499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292605160530805766324972999 438907740796208649487459499)
    ·
      refine ⟨658361611194312974231189249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438907740796208649487459499 658361611194312974231189249)
      ·
        refine ⟨493771208395734730673391937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658361611194312974231189249 493771208395734730673391937)
        ·
          refine ⟨370328406296801048005043953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493771208395734730673391937 370328406296801048005043953)
          ·
            refine ⟨277746304722600786003782965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370328406296801048005043953 277746304722600786003782965)
            ·
              refine ⟨26038716067743823687854653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277746304722600786003782965 26038716067743823687854653)
              ·
                refine ⟨9764518525403933882945495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26038716067743823687854653 9764518525403933882945495)
                ·
                  refine ⟨14646777788105900824418243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764518525403933882945495 14646777788105900824418243)
                  ·
                    refine ⟨21970166682158851236627365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14646777788105900824418243 21970166682158851236627365)
                    ·
                      refine ⟨4119406252904784606867631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21970166682158851236627365 4119406252904784606867631)
                      ·
                        rfl

theorem cell23_8022515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_8022515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022515 prefixEnd_8022515 := by exact prefixLift 8022515
  have htrace : WordTrace (prefixWord ++ tailWord_8022515) baseStart_8022515 baseEnd_8022515 := by
    simpa [prefixWord, tailWord_8022515, baseEnd_8022515] using wordTrace_append hprefix tailTrace_8022515
  have hstable : (prefixWord ++ tailWord_8022515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022515).length < 2 ^ (prefixWord ++ tailWord_8022515).sum := by decide
  have hdescent : baseEnd_8022515 < baseStart_8022515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022525 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_8022525 : Nat := 118140960795 + 8022525 * 2 ^ 59
def prefixEnd_8022525 : Nat := 4983230072969 + 3 ^ 40 * 8022525 * 2
def baseEnd_8022525 : Nat := 1373137129237109855914195

theorem tailTrace_8022525 : CollatzResearch.WordTrace tailWord_8022525 prefixEnd_8022525 1373137129237109855914195 := by
  unfold tailWord_8022525
  simp only [CollatzResearch.WordTrace]
  refine ⟨292605525260769538032837029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195070350173846358688558019 292605525260769538032837029)
  ·
    refine ⟨54863535986394288381156943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292605525260769538032837029 54863535986394288381156943)
    ·
      refine ⟨82295303979591432571735415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54863535986394288381156943 82295303979591432571735415)
      ·
        refine ⟨123442955969387148857603123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82295303979591432571735415 123442955969387148857603123)
        ·
          refine ⟨185164433954080723286404685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123442955969387148857603123 185164433954080723286404685)
          ·
            refine ⟨69436662732780271232401757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185164433954080723286404685 69436662732780271232401757)
            ·
              refine ⟨26038748524792601712150659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69436662732780271232401757 26038748524792601712150659)
              ·
                refine ⟨39058122787188902568225989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26038748524792601712150659 39058122787188902568225989)
                ·
                  refine ⟨7323398022597919231542373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39058122787188902568225989 7323398022597919231542373)
                  ·
                    refine ⟨1373137129237109855914195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7323398022597919231542373 1373137129237109855914195)
                    ·
                      rfl

theorem cell23_8022525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_8022525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022525 prefixEnd_8022525 := by exact prefixLift 8022525
  have htrace : WordTrace (prefixWord ++ tailWord_8022525) baseStart_8022525 baseEnd_8022525 := by
    simpa [prefixWord, tailWord_8022525, baseEnd_8022525] using wordTrace_append hprefix tailTrace_8022525
  have hstable : (prefixWord ++ tailWord_8022525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022525).length < 2 ^ (prefixWord ++ tailWord_8022525).sum := by decide
  have hdescent : baseEnd_8022525 < baseStart_8022525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022538 : List Nat := [3, 1, 2, 2, 2, 1, 2, 10]
def baseStart_8022538 : Nat := 118140960795 + 8022538 * 2 ^ 59
def prefixEnd_8022538 : Nat := 4983230072969 + 3 ^ 40 * 8022538 * 2
def baseEnd_8022538 : Nat := 152571039368882889514075

theorem tailTrace_8022538 : CollatzResearch.WordTrace tailWord_8022538 prefixEnd_8022538 152571039368882889514075 := by
  unfold tailWord_8022538
  simp only [CollatzResearch.WordTrace]
  refine ⟨73151499852430610313265067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195070666273148294168706845 73151499852430610313265067)
  ·
    refine ⟨109727249778645915469897601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73151499852430610313265067 109727249778645915469897601)
    ·
      refine ⟨82295437333984436602423201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109727249778645915469897601 82295437333984436602423201)
      ·
        refine ⟨61721578000488327451817401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82295437333984436602423201 61721578000488327451817401)
        ·
          refine ⟨46291183500366245588863051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61721578000488327451817401 46291183500366245588863051)
          ·
            refine ⟨69436775250549368383294577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46291183500366245588863051 69436775250549368383294577)
            ·
              refine ⟨52077581437912026287470933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69436775250549368383294577 52077581437912026287470933)
              ·
                refine ⟨152571039368882889514075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52077581437912026287470933 152571039368882889514075)
                ·
                  rfl

theorem cell23_8022538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_8022538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022538 prefixEnd_8022538 := by exact prefixLift 8022538
  have htrace : WordTrace (prefixWord ++ tailWord_8022538) baseStart_8022538 baseEnd_8022538 := by
    simpa [prefixWord, tailWord_8022538, baseEnd_8022538] using wordTrace_append hprefix tailTrace_8022538
  have hstable : (prefixWord ++ tailWord_8022538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022538).length < 2 ^ (prefixWord ++ tailWord_8022538).sum := by decide
  have hdescent : baseEnd_8022538 < baseStart_8022538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022542 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_8022542 : Nat := 118140960795 + 8022542 * 2 ^ 59
def prefixEnd_8022542 : Nat := 4983230072969 + 3 ^ 40 * 8022542 * 2
def baseEnd_8022542 : Nat := 1373140038960818667076669

theorem tailTrace_8022542 : CollatzResearch.WordTrace tailWord_8022542 prefixEnd_8022542 1373140038960818667076669 := by
  unfold tailWord_8022542
  simp only [CollatzResearch.WordTrace]
  refine ⟨36575768162713493742025735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195070763534471966624137253 36575768162713493742025735)
  ·
    refine ⟨54863652244070240613038603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36575768162713493742025735 54863652244070240613038603)
    ·
      refine ⟨82295478366105360919557905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54863652244070240613038603 82295478366105360919557905)
      ·
        refine ⟨61721608774579020689668429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82295478366105360919557905 61721608774579020689668429)
        ·
          refine ⟨23145603290467132758625661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61721608774579020689668429 23145603290467132758625661)
          ·
            refine ⟨8679601233925174784484623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23145603290467132758625661 8679601233925174784484623)
            ·
              refine ⟨13019401850887762176726935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8679601233925174784484623 13019401850887762176726935)
              ·
                refine ⟨19529102776331643265090403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13019401850887762176726935 19529102776331643265090403)
                ·
                  refine ⟨29293654164497464897635605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19529102776331643265090403 29293654164497464897635605)
                  ·
                    refine ⟨1373140038960818667076669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29293654164497464897635605 1373140038960818667076669)
                    ·
                      rfl

theorem cell23_8022542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_8022542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022542 prefixEnd_8022542 := by exact prefixLift 8022542
  have htrace : WordTrace (prefixWord ++ tailWord_8022542) baseStart_8022542 baseEnd_8022542 := by
    simpa [prefixWord, tailWord_8022542, baseEnd_8022542] using wordTrace_append hprefix tailTrace_8022542
  have hstable : (prefixWord ++ tailWord_8022542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022542).length < 2 ^ (prefixWord ++ tailWord_8022542).sum := by decide
  have hdescent : baseEnd_8022542 < baseStart_8022542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022552 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_8022552 : Nat := 118140960795 + 8022552 * 2 ^ 59
def prefixEnd_8022552 : Nat := 4983230072969 + 3 ^ 40 * 8022552 * 2
def baseEnd_8022552 : Nat := 4119425251689000962104961

theorem tailTrace_8022552 : CollatzResearch.WordTrace tailWord_8022552 prefixEnd_8022552 4119425251689000962104961 := by
  unfold tailWord_8022552
  simp only [CollatzResearch.WordTrace]
  refine ⟨146303255015835860822034955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195071006687781147762713273 146303255015835860822034955)
  ·
    refine ⟨219454882523753791233052433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146303255015835860822034955 219454882523753791233052433)
    ·
      refine ⟨164591161892815343424789325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219454882523753791233052433 164591161892815343424789325)
      ·
        refine ⟨61721685709805753784295997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164591161892815343424789325 61721685709805753784295997)
        ·
          refine ⟨23145632141177157669110999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61721685709805753784295997 23145632141177157669110999)
          ·
            refine ⟨34718448211765736503666499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23145632141177157669110999 34718448211765736503666499)
            ·
              refine ⟨52077672317648604755499749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34718448211765736503666499 52077672317648604755499749)
              ·
                refine ⟨9764563559559113391656203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52077672317648604755499749 9764563559559113391656203)
                ·
                  refine ⟨14646845339338670087484305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764563559559113391656203 14646845339338670087484305)
                  ·
                    refine ⟨10985134004504002565613229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14646845339338670087484305 10985134004504002565613229)
                    ·
                      refine ⟨4119425251689000962104961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10985134004504002565613229 4119425251689000962104961)
                      ·
                        rfl

theorem cell23_8022552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_8022552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022552 prefixEnd_8022552 := by exact prefixLift 8022552
  have htrace : WordTrace (prefixWord ++ tailWord_8022552) baseStart_8022552 baseEnd_8022552 := by
    simpa [prefixWord, tailWord_8022552, baseEnd_8022552] using wordTrace_append hprefix tailTrace_8022552
  have hstable : (prefixWord ++ tailWord_8022552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022552).length < 2 ^ (prefixWord ++ tailWord_8022552).sum := by decide
  have hdescent : baseEnd_8022552 < baseStart_8022552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022565 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_8022565 : Nat := 118140960795 + 8022565 * 2 ^ 59
def prefixEnd_8022565 : Nat := 4983230072969 + 3 ^ 40 * 8022565 * 2
def baseEnd_8022565 : Nat := 4119431926937509411242401

theorem tailTrace_8022565 : CollatzResearch.WordTrace tailWord_8022565 prefixEnd_8022565 4119431926937509411242401 := by
  unfold tailWord_8022565
  simp only [CollatzResearch.WordTrace]
  refine ⟨292606984180624624864293149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195071322787083083242862099 292606984180624624864293149)
  ·
    refine ⟨109727619067734234324109931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292606984180624624864293149 109727619067734234324109931)
    ·
      refine ⟨164591428601601351486164897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109727619067734234324109931 164591428601601351486164897)
      ·
        refine ⟨123443571451201013614623673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164591428601601351486164897 123443571451201013614623673)
        ·
          refine ⟨92582678588400760210967755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123443571451201013614623673 92582678588400760210967755)
          ·
            refine ⟨138874017882601140316451633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92582678588400760210967755 138874017882601140316451633)
            ·
              refine ⟨104155513411950855237338725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138874017882601140316451633 104155513411950855237338725)
              ·
                refine ⟨19529158764740785357001011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104155513411950855237338725 19529158764740785357001011)
                ·
                  refine ⟨29293738147111178035501517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19529158764740785357001011 29293738147111178035501517)
                  ·
                    refine ⟨10985151805166691763313069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29293738147111178035501517 10985151805166691763313069)
                    ·
                      refine ⟨4119431926937509411242401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10985151805166691763313069 4119431926937509411242401)
                      ·
                        rfl

theorem cell23_8022565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_8022565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022565 prefixEnd_8022565 := by exact prefixLift 8022565
  have htrace : WordTrace (prefixWord ++ tailWord_8022565) baseStart_8022565 baseEnd_8022565 := by
    simpa [prefixWord, tailWord_8022565, baseEnd_8022565] using wordTrace_append hprefix tailTrace_8022565
  have hstable : (prefixWord ++ tailWord_8022565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022565).length < 2 ^ (prefixWord ++ tailWord_8022565).sum := by decide
  have hdescent : baseEnd_8022565 < baseStart_8022565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022599 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_8022599 : Nat := 118140960795 + 8022599 * 2 ^ 59
def prefixEnd_8022599 : Nat := 4983230072969 + 3 ^ 40 * 8022599 * 2
def baseEnd_8022599 : Nat := 4119449385279762278217245

theorem tailTrace_8022599 : CollatzResearch.WordTrace tailWord_8022599 prefixEnd_8022599 4119449385279762278217245 := by
  unfold tailWord_8022599
  simp only [CollatzResearch.WordTrace]
  refine ⟨292608224262501448671030851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195072149508334299114020567 292608224262501448671030851)
  ·
    refine ⟨438912336393752173006546277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292608224262501448671030851 438912336393752173006546277)
    ·
      refine ⟨82296063073828532438727427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438912336393752173006546277 82296063073828532438727427)
      ·
        refine ⟨123444094610742798658091141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82296063073828532438727427 123444094610742798658091141)
        ·
          refine ⟨23145767739514274748392089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123444094610742798658091141 23145767739514274748392089)
          ·
            refine ⟨17359325804635706061294067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23145767739514274748392089 17359325804635706061294067)
            ·
              refine ⟨26038988706953559091941101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17359325804635706061294067 26038988706953559091941101)
              ·
                refine ⟨9764620765107584659477913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26038988706953559091941101 9764620765107584659477913)
                ·
                  refine ⟨7323465573830688494608435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9764620765107584659477913 7323465573830688494608435)
                  ·
                    refine ⟨10985198360746032741912653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323465573830688494608435 10985198360746032741912653)
                    ·
                      refine ⟨4119449385279762278217245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10985198360746032741912653 4119449385279762278217245)
                      ·
                        rfl

theorem cell23_8022599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_8022599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022599 prefixEnd_8022599 := by exact prefixLift 8022599
  have htrace : WordTrace (prefixWord ++ tailWord_8022599) baseStart_8022599 baseEnd_8022599 := by
    simpa [prefixWord, tailWord_8022599, baseEnd_8022599] using wordTrace_append hprefix tailTrace_8022599
  have hstable : (prefixWord ++ tailWord_8022599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022599).length < 2 ^ (prefixWord ++ tailWord_8022599).sum := by decide
  have hdescent : baseEnd_8022599 < baseStart_8022599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022609 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 1, 3, 2]
def baseStart_8022609 : Nat := 118140960795 + 8022609 * 2 ^ 59
def prefixEnd_8022609 : Nat := 4983230072969 + 3 ^ 40 * 8022609 * 2
def baseEnd_8022609 : Nat := 4119454520086307239092199

theorem tailTrace_8022609 : CollatzResearch.WordTrace tailWord_8022609 prefixEnd_8022609 4119454520086307239092199 := by
  unfold tailWord_8022609
  simp only [CollatzResearch.WordTrace]
  refine ⟨292608588992465220378894881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195072392661643480252596587 292608588992465220378894881)
  ·
    refine ⟨219456441744348915284171161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292608588992465220378894881 219456441744348915284171161)
    ·
      refine ⟨164592331308261686463128371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219456441744348915284171161 164592331308261686463128371)
      ·
        refine ⟨246888496962392529694692557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164592331308261686463128371 246888496962392529694692557)
        ·
          refine ⟨92583186360897198635509709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246888496962392529694692557 92583186360897198635509709)
          ·
            refine ⟨34718694885336449488316141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92583186360897198635509709 34718694885336449488316141)
            ·
              refine ⟨13019510582001168558118553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34718694885336449488316141 13019510582001168558118553)
              ·
                refine ⟨9764632936500876418588915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13019510582001168558118553 9764632936500876418588915)
                ·
                  refine ⟨14646949404751314627883373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764632936500876418588915 14646949404751314627883373)
                  ·
                    refine ⟨5492606026781742985456265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14646949404751314627883373 5492606026781742985456265)
                    ·
                      refine ⟨4119454520086307239092199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492606026781742985456265 4119454520086307239092199)
                      ·
                        rfl

theorem cell23_8022609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_8022609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022609 prefixEnd_8022609 := by exact prefixLift 8022609
  have htrace : WordTrace (prefixWord ++ tailWord_8022609) baseStart_8022609 baseEnd_8022609 := by
    simpa [prefixWord, tailWord_8022609, baseEnd_8022609] using wordTrace_append hprefix tailTrace_8022609
  have hstable : (prefixWord ++ tailWord_8022609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022609).length < 2 ^ (prefixWord ++ tailWord_8022609).sum := by decide
  have hdescent : baseEnd_8022609 < baseStart_8022609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022625 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_8022625 : Nat := 118140960795 + 8022625 * 2 ^ 59
def prefixEnd_8022625 : Nat := 4983230072969 + 3 ^ 40 * 8022625 * 2
def baseEnd_8022625 : Nat := 4119462735776779176492125

theorem tailTrace_8022625 : CollatzResearch.WordTrace tailWord_8022625 prefixEnd_8022625 4119462735776779176492125 := by
  unfold tailWord_8022625
  simp only [CollatzResearch.WordTrace]
  refine ⟨292609172560407255111477329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195072781706938170074318219 292609172560407255111477329)
  ·
    refine ⟨219456879420305441333607997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292609172560407255111477329 219456879420305441333607997)
    ·
      refine ⟨82296329782614540500102999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219456879420305441333607997 82296329782614540500102999)
      ·
        refine ⟨123444494673921810750154499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82296329782614540500102999 123444494673921810750154499)
        ·
          refine ⟨185166742010882716125231749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123444494673921810750154499 185166742010882716125231749)
          ·
            refine ⟨34718764127040509273480953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185166742010882716125231749 34718764127040509273480953)
            ·
              refine ⟨26039073095280381955110715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34718764127040509273480953 26039073095280381955110715)
              ·
                refine ⟨39058609642920572932666073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26039073095280381955110715 39058609642920572932666073)
                ·
                  refine ⟨29293957232190429699499555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39058609642920572932666073 29293957232190429699499555)
                  ·
                    refine ⟨43940935848285644549249333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29293957232190429699499555 43940935848285644549249333)
                    ·
                      refine ⟨4119462735776779176492125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43940935848285644549249333 4119462735776779176492125)
                      ·
                        rfl

theorem cell23_8022625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_8022625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022625 prefixEnd_8022625 := by exact prefixLift 8022625
  have htrace : WordTrace (prefixWord ++ tailWord_8022625) baseStart_8022625 baseEnd_8022625 := by
    simpa [prefixWord, tailWord_8022625, baseEnd_8022625] using wordTrace_append hprefix tailTrace_8022625
  have hstable : (prefixWord ++ tailWord_8022625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022625).length < 2 ^ (prefixWord ++ tailWord_8022625).sum := by decide
  have hdescent : baseEnd_8022625 < baseStart_8022625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022639 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 2, 2, 2]
def baseStart_8022639 : Nat := 118140960795 + 8022639 * 2 ^ 59
def prefixEnd_8022639 : Nat := 4983230072969 + 3 ^ 40 * 8022639 * 2
def baseEnd_8022639 : Nat := 4119469924505942121717061

theorem tailTrace_8022639 : CollatzResearch.WordTrace tailWord_8022639 prefixEnd_8022639 4119469924505942121717061 := by
  unfold tailWord_8022639
  simp only [CollatzResearch.WordTrace]
  refine ⟨292609683182356535502486971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195073122121571023668324647 292609683182356535502486971)
  ·
    refine ⟨438914524773534803253730457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292609683182356535502486971 438914524773534803253730457)
    ·
      refine ⟨329185893580151102440297843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438914524773534803253730457 329185893580151102440297843)
      ·
        refine ⟨493778840370226653660446765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329185893580151102440297843 493778840370226653660446765)
        ·
          refine ⟨185167065138834995122667537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493778840370226653660446765 185167065138834995122667537)
          ·
            refine ⟨138875298854126246342000653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185167065138834995122667537 138875298854126246342000653)
            ·
              refine ⟨52078237070297342378250245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138875298854126246342000653 52078237070297342378250245)
              ·
                refine ⟨9764669450680751695921921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52078237070297342378250245 9764669450680751695921921)
                ·
                  refine ⟨7323502088010563771941441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9764669450680751695921921 7323502088010563771941441)
                  ·
                    refine ⟨5492626566007922828956081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7323502088010563771941441 5492626566007922828956081)
                    ·
                      refine ⟨4119469924505942121717061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492626566007922828956081 4119469924505942121717061)
                      ·
                        rfl

theorem cell23_8022639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 2, 2].length) (baseStart_8022639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022639 prefixEnd_8022639 := by exact prefixLift 8022639
  have htrace : WordTrace (prefixWord ++ tailWord_8022639) baseStart_8022639 baseEnd_8022639 := by
    simpa [prefixWord, tailWord_8022639, baseEnd_8022639] using wordTrace_append hprefix tailTrace_8022639
  have hstable : (prefixWord ++ tailWord_8022639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022639).length < 2 ^ (prefixWord ++ tailWord_8022639).sum := by decide
  have hdescent : baseEnd_8022639 < baseStart_8022639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022685 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_8022685 : Nat := 118140960795 + 8022685 * 2 ^ 59
def prefixEnd_8022685 : Nat := 4983230072969 + 3 ^ 40 * 8022685 * 2
def baseEnd_8022685 : Nat := 4119493544616048941741849

theorem tailTrace_8022685 : CollatzResearch.WordTrace tailWord_8022685 prefixEnd_8022685 4119493544616048941741849 := by
  unfold tailWord_8022685
  simp only [CollatzResearch.WordTrace]
  refine ⟨292611360940189885358661509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195074240626793256905774339 292611360940189885358661509)
  ·
    refine ⟨54864630176285603504749033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292611360940189885358661509 54864630176285603504749033)
    ·
      refine ⟨41148472632214202628561775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54864630176285603504749033 41148472632214202628561775)
      ·
        refine ⟨61722708948321303942842663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41148472632214202628561775 61722708948321303942842663)
        ·
          refine ⟨92584063422481955914263995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61722708948321303942842663 92584063422481955914263995)
          ·
            refine ⟨138876095133722933871395993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92584063422481955914263995 138876095133722933871395993)
            ·
              refine ⟨104157071350292200403546995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138876095133722933871395993 104157071350292200403546995)
              ·
                refine ⟨156235607025438300605320493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104157071350292200403546995 156235607025438300605320493)
                ·
                  refine ⟨58588352634539362726995185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156235607025438300605320493 58588352634539362726995185)
                  ·
                    refine ⟨43941264475904522045246389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58588352634539362726995185 43941264475904522045246389)
                    ·
                      refine ⟨4119493544616048941741849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43941264475904522045246389 4119493544616048941741849)
                      ·
                        rfl

theorem cell23_8022685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_8022685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022685 prefixEnd_8022685 := by exact prefixLift 8022685
  have htrace : WordTrace (prefixWord ++ tailWord_8022685) baseStart_8022685 baseEnd_8022685 := by
    simpa [prefixWord, tailWord_8022685, baseEnd_8022685] using wordTrace_append hprefix tailTrace_8022685
  have hstable : (prefixWord ++ tailWord_8022685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022685).length < 2 ^ (prefixWord ++ tailWord_8022685).sum := by decide
  have hdescent : baseEnd_8022685 < baseStart_8022685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022796 : List Nat := [2, 2, 1, 2, 2, 1, 1, 7, 1, 1, 3]
def baseStart_8022796 : Nat := 118140960795 + 8022796 * 2 ^ 59
def prefixEnd_8022796 : Nat := 4983230072969 + 3 ^ 40 * 8022796 * 2
def baseEnd_8022796 : Nat := 4119550540968698007453839

theorem tailTrace_8022796 : CollatzResearch.WordTrace tailWord_8022796 prefixEnd_8022796 4119550540968698007453839 := by
  unfold tailWord_8022796
  simp only [CollatzResearch.WordTrace]
  refine ⟨146307704721393875657976121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195076939628525167543968161 146307704721393875657976121)
  ·
    refine ⟨109730778541045406743482091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146307704721393875657976121 109730778541045406743482091)
    ·
      refine ⟨164596167811568110115223137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109730778541045406743482091 164596167811568110115223137)
      ·
        refine ⟨123447125858676082586417353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164596167811568110115223137 123447125858676082586417353)
        ·
          refine ⟨92585344394007061939813015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123447125858676082586417353 92585344394007061939813015)
          ·
            refine ⟨138878016591010592909719523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92585344394007061939813015 138878016591010592909719523)
            ·
              refine ⟨208317024886515889364579285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138878016591010592909719523 208317024886515889364579285)
              ·
                refine ⟨4882430270777716156982327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 208317024886515889364579285 4882430270777716156982327)
                ·
                  refine ⟨7323645406166574235473491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882430270777716156982327 7323645406166574235473491)
                  ·
                    refine ⟨10985468109249861353210237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323645406166574235473491 10985468109249861353210237)
                    ·
                      refine ⟨4119550540968698007453839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10985468109249861353210237 4119550540968698007453839)
                      ·
                        rfl

theorem cell23_8022796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_8022796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022796 prefixEnd_8022796 := by exact prefixLift 8022796
  have htrace : WordTrace (prefixWord ++ tailWord_8022796) baseStart_8022796 baseEnd_8022796 := by
    simpa [prefixWord, tailWord_8022796, baseEnd_8022796] using wordTrace_append hprefix tailTrace_8022796
  have hstable : (prefixWord ++ tailWord_8022796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022796).length < 2 ^ (prefixWord ++ tailWord_8022796).sum := by decide
  have hdescent : baseEnd_8022796 < baseStart_8022796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022799 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 1, 5]
def baseStart_8022799 : Nat := 118140960795 + 8022799 * 2 ^ 59
def prefixEnd_8022799 : Nat := 4983230072969 + 3 ^ 40 * 8022799 * 2
def baseEnd_8022799 : Nat := 1373184027136887165238775

theorem tailTrace_8022799 : CollatzResearch.WordTrace tailWord_8022799 prefixEnd_8022799 1373184027136887165238775 := by
  unfold tailWord_8022799
  simp only [CollatzResearch.WordTrace]
  refine ⟨292615518861776882828311451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195077012574517921885540967 292615518861776882828311451)
  ·
    refine ⟨438923278292665324242467177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292615518861776882828311451 438923278292665324242467177)
    ·
      refine ⟨329192458719498993181850383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438923278292665324242467177 329192458719498993181850383)
      ·
        refine ⟨493788688079248489772775575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329192458719498993181850383 493788688079248489772775575)
        ·
          refine ⟨740683032118872734659163363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493788688079248489772775575 740683032118872734659163363)
          ·
            refine ⟨1111024548178309101988745045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740683032118872734659163363 1111024548178309101988745045)
            ·
              refine ⟨6509909461982279894465303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1111024548178309101988745045 6509909461982279894465303)
              ·
                refine ⟨9764864192973419841697955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509909461982279894465303 9764864192973419841697955)
                ·
                  refine ⟨14647296289460129762546933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764864192973419841697955 14647296289460129762546933)
                  ·
                    refine ⟨1373184027136887165238775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14647296289460129762546933 1373184027136887165238775)
                    ·
                      rfl

theorem cell23_8022799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 5].length) (baseStart_8022799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022799 prefixEnd_8022799 := by exact prefixLift 8022799
  have htrace : WordTrace (prefixWord ++ tailWord_8022799) baseStart_8022799 baseEnd_8022799 := by
    simpa [prefixWord, tailWord_8022799, baseEnd_8022799] using wordTrace_append hprefix tailTrace_8022799
  have hstable : (prefixWord ++ tailWord_8022799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022799).length < 2 ^ (prefixWord ++ tailWord_8022799).sum := by decide
  have hdescent : baseEnd_8022799 < baseStart_8022799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022839 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_8022839 : Nat := 118140960795 + 8022839 * 2 ^ 59
def prefixEnd_8022839 : Nat := 4983230072969 + 3 ^ 40 * 8022839 * 2
def baseEnd_8022839 : Nat := 4119572620636841339216141

theorem tailTrace_8022839 : CollatzResearch.WordTrace tailWord_8022839 prefixEnd_8022839 4119572620636841339216141 := by
  unfold tailWord_8022839
  simp only [CollatzResearch.WordTrace]
  refine ⟨292616977781631969659767571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195077985187754646439845047 292616977781631969659767571)
  ·
    refine ⟨438925466672447954489651357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292616977781631969659767571 438925466672447954489651357)
    ·
      refine ⟨164597050002167982933619259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438925466672447954489651357 164597050002167982933619259)
      ·
        refine ⟨246895575003251974400428889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164597050002167982933619259 246895575003251974400428889)
        ·
          refine ⟨185171681252438980800321667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246895575003251974400428889 185171681252438980800321667)
          ·
            refine ⟨277757521878658471200482501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185171681252438980800321667 277757521878658471200482501)
            ·
              refine ⟨52079535352248463350090469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277757521878658471200482501 52079535352248463350090469)
              ·
                refine ⟨9764912878546586878141963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52079535352248463350090469 9764912878546586878141963)
                ·
                  refine ⟨14647369317819880317212945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764912878546586878141963 14647369317819880317212945)
                  ·
                    refine ⟨10985526988364910237909709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14647369317819880317212945 10985526988364910237909709)
                    ·
                      refine ⟨4119572620636841339216141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10985526988364910237909709 4119572620636841339216141)
                      ·
                        rfl

theorem cell23_8022839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_8022839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022839 prefixEnd_8022839 := by exact prefixLift 8022839
  have htrace : WordTrace (prefixWord ++ tailWord_8022839) baseStart_8022839 baseEnd_8022839 := by
    simpa [prefixWord, tailWord_8022839, baseEnd_8022839] using wordTrace_append hprefix tailTrace_8022839
  have hstable : (prefixWord ++ tailWord_8022839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022839).length < 2 ^ (prefixWord ++ tailWord_8022839).sum := by decide
  have hdescent : baseEnd_8022839 < baseStart_8022839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022896 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 1, 3, 2]
def baseStart_8022896 : Nat := 118140960795 + 8022896 * 2 ^ 59
def prefixEnd_8022896 : Nat := 4983230072969 + 3 ^ 40 * 8022896 * 2
def baseEnd_8022896 : Nat := 4119601889034147616203379

theorem tailTrace_8022896 : CollatzResearch.WordTrace tailWord_8022896 prefixEnd_8022896 4119601889034147616203379 := by
  unfold tailWord_8022896
  simp only [CollatzResearch.WordTrace]
  refine ⟨146309528371212734197296271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195079371161616978929728361 146309528371212734197296271)
  ·
    refine ⟨219464292556819101295944407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146309528371212734197296271 219464292556819101295944407)
    ·
      refine ⟨329196438835228651943916611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219464292556819101295944407 329196438835228651943916611)
      ·
        refine ⟨493794658252842977915874917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329196438835228651943916611 493794658252842977915874917)
        ·
          refine ⟨92586498422408058359226547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493794658252842977915874917 92586498422408058359226547)
          ·
            refine ⟨138879747633612087538839821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92586498422408058359226547 138879747633612087538839821)
            ·
              refine ⟨52079905362604532827064933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138879747633612087538839821 52079905362604532827064933)
              ·
                refine ⟨9764982255488349905074675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52079905362604532827064933 9764982255488349905074675)
                ·
                  refine ⟨14647473383232524857612013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9764982255488349905074675 14647473383232524857612013)
                  ·
                    refine ⟨5492802518712196821604505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14647473383232524857612013 5492802518712196821604505)
                    ·
                      refine ⟨4119601889034147616203379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492802518712196821604505 4119601889034147616203379)
                      ·
                        rfl

theorem cell23_8022896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 3, 2].length) (baseStart_8022896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022896 prefixEnd_8022896 := by exact prefixLift 8022896
  have htrace : WordTrace (prefixWord ++ tailWord_8022896) baseStart_8022896 baseEnd_8022896 := by
    simpa [prefixWord, tailWord_8022896, baseEnd_8022896] using wordTrace_append hprefix tailTrace_8022896
  have hstable : (prefixWord ++ tailWord_8022896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022896).length < 2 ^ (prefixWord ++ tailWord_8022896).sum := by decide
  have hdescent : baseEnd_8022896 < baseStart_8022896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8022992 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 2, 8]
def baseStart_8022992 : Nat := 118140960795 + 8022992 * 2 ^ 59
def prefixEnd_8022992 : Nat := 4983230072969 + 3 ^ 40 * 8022992 * 2
def baseEnd_8022992 : Nat := 1373217061058993080200979

theorem tailTrace_8022992 : CollatzResearch.WordTrace tailWord_8022992 prefixEnd_8022992 1373217061058993080200979 := by
  unfold tailWord_8022992
  simp only [CollatzResearch.WordTrace]
  refine ⟨146311279075038838395043615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195081705433385117860058153 146311279075038838395043615)
  ·
    refine ⟨219466918612558257592565423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146311279075038838395043615 219466918612558257592565423)
    ·
      refine ⟨329200377918837386388848135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219466918612558257592565423 329200377918837386388848135)
      ·
        refine ⟨493800566878256079583272203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329200377918837386388848135 493800566878256079583272203)
        ·
          refine ⟨740700850317384119374908305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493800566878256079583272203 740700850317384119374908305)
          ·
            refine ⟨555525637738038089531181229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740700850317384119374908305 555525637738038089531181229)
            ·
              refine ⟨208322114151764283574192961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555525637738038089531181229 208322114151764283574192961)
              ·
                refine ⟨156241585613823212680644721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208322114151764283574192961 156241585613823212680644721)
                ·
                  refine ⟨117181189210367409510483541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156241585613823212680644721 117181189210367409510483541)
                  ·
                    refine ⟨1373217061058993080200979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117181189210367409510483541 1373217061058993080200979)
                    ·
                      rfl

theorem cell23_8022992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_8022992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8022992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8022992 prefixEnd_8022992 := by exact prefixLift 8022992
  have htrace : WordTrace (prefixWord ++ tailWord_8022992) baseStart_8022992 baseEnd_8022992 := by
    simpa [prefixWord, tailWord_8022992, baseEnd_8022992] using wordTrace_append hprefix tailTrace_8022992
  have hstable : (prefixWord ++ tailWord_8022992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8022992).length < 2 ^ (prefixWord ++ tailWord_8022992).sum := by decide
  have hdescent : baseEnd_8022992 < baseStart_8022992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8022992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023016 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_8023016 : Nat := 118140960795 + 8023016 * 2 ^ 59
def prefixEnd_8023016 : Nat := 4983230072969 + 3 ^ 40 * 8023016 * 2
def baseEnd_8023016 : Nat := 4119663506712687146702827

theorem tailTrace_8023016 : CollatzResearch.WordTrace tailWord_8023016 prefixEnd_8023016 4119663506712687146702827 := by
  unfold tailWord_8023016
  simp only [CollatzResearch.WordTrace]
  refine ⟨146311716750995364444480451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195082289001327152592640601 146311716750995364444480451)
  ·
    refine ⟨219467575126493046666720677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146311716750995364444480451 219467575126493046666720677)
    ·
      refine ⟨41150170336217446250010127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219467575126493046666720677 41150170336217446250010127)
      ·
        refine ⟨61725255504326169375015191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41150170336217446250010127 61725255504326169375015191)
        ·
          refine ⟨92587883256489254062522787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61725255504326169375015191 92587883256489254062522787)
          ·
            refine ⟨138881824884733881093784181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92587883256489254062522787 138881824884733881093784181)
            ·
              refine ⟨13020171082943801352542267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138881824884733881093784181 13020171082943801352542267)
              ·
                refine ⟨19530256624415702028813401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13020171082943801352542267 19530256624415702028813401)
                ·
                  refine ⟨14647692468311776521610051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19530256624415702028813401 14647692468311776521610051)
                  ·
                    refine ⟨21971538702467664782415077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14647692468311776521610051 21971538702467664782415077)
                    ·
                      refine ⟨4119663506712687146702827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21971538702467664782415077 4119663506712687146702827)
                      ·
                        rfl

theorem cell23_8023016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_8023016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023016 prefixEnd_8023016 := by exact prefixLift 8023016
  have htrace : WordTrace (prefixWord ++ tailWord_8023016) baseStart_8023016 baseEnd_8023016 := by
    simpa [prefixWord, tailWord_8023016, baseEnd_8023016] using wordTrace_append hprefix tailTrace_8023016
  have hstable : (prefixWord ++ tailWord_8023016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023016).length < 2 ^ (prefixWord ++ tailWord_8023016).sum := by decide
  have hdescent : baseEnd_8023016 < baseStart_8023016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023028 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_8023028 : Nat := 118140960795 + 8023028 * 2 ^ 59
def prefixEnd_8023028 : Nat := 4983230072969 + 3 ^ 40 * 8023028 * 2
def baseEnd_8023028 : Nat := 4119669668480541099752773

theorem tailTrace_8023028 : CollatzResearch.WordTrace tailWord_8023028 prefixEnd_8023028 4119669668480541099752773 := by
  unfold tailWord_8023028
  simp only [CollatzResearch.WordTrace]
  refine ⟨146311935588973627469198869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195082580785298169958931825 146311935588973627469198869)
  ·
    refine ⟨6858371980733138787618697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146311935588973627469198869 6858371980733138787618697)
    ·
      refine ⟨5143778985549854090714023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6858371980733138787618697 5143778985549854090714023)
      ·
        refine ⟨7715668478324781136071035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143778985549854090714023 7715668478324781136071035)
        ·
          refine ⟨11573502717487171704106553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7715668478324781136071035 11573502717487171704106553)
          ·
            refine ⟨8680127038115378778079915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11573502717487171704106553 8680127038115378778079915)
            ·
              refine ⟨13020190557173068167119873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680127038115378778079915 13020190557173068167119873)
              ·
                refine ⟨9765142917879801125339905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020190557173068167119873 9765142917879801125339905)
                ·
                  refine ⟨7323857188409850844004929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9765142917879801125339905 7323857188409850844004929)
                  ·
                    refine ⟨5492892891307388133003697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7323857188409850844004929 5492892891307388133003697)
                    ·
                      refine ⟨4119669668480541099752773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5492892891307388133003697 4119669668480541099752773)
                      ·
                        rfl

theorem cell23_8023028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_8023028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023028 prefixEnd_8023028 := by exact prefixLift 8023028
  have htrace : WordTrace (prefixWord ++ tailWord_8023028) baseStart_8023028 baseEnd_8023028 := by
    simpa [prefixWord, tailWord_8023028, baseEnd_8023028] using wordTrace_append hprefix tailTrace_8023028
  have hstable : (prefixWord ++ tailWord_8023028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023028).length < 2 ^ (prefixWord ++ tailWord_8023028).sum := by decide
  have hdescent : baseEnd_8023028 < baseStart_8023028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023100 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_8023100 : Nat := 118140960795 + 8023100 * 2 ^ 59
def prefixEnd_8023100 : Nat := 4983230072969 + 3 ^ 40 * 8023100 * 2
def baseEnd_8023100 : Nat := 4119706639087664818052441

theorem tailTrace_8023100 : CollatzResearch.WordTrace tailWord_8023100 prefixEnd_8023100 4119706639087664818052441 := by
  unfold tailWord_8023100
  simp only [CollatzResearch.WordTrace]
  refine ⟨146313248616843205617509377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195084331489124274156679169 146313248616843205617509377)
  ·
    refine ⟨109734936462632404213132033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146313248616843205617509377 109734936462632404213132033)
    ·
      refine ⟨82301202346974303159849025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109734936462632404213132033 82301202346974303159849025)
      ·
        refine ⟨61725901760230727369886769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82301202346974303159849025 61725901760230727369886769)
        ·
          refine ⟨46294426320173045527415077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61725901760230727369886769 46294426320173045527415077)
          ·
            refine ⟨8680204935032446036390327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46294426320173045527415077 8680204935032446036390327)
            ·
              refine ⟨13020307402548669054585491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680204935032446036390327 13020307402548669054585491)
              ·
                refine ⟨19530461103823003581878237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13020307402548669054585491 19530461103823003581878237)
                ·
                  refine ⟨7323922913933626343204339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19530461103823003581878237 7323922913933626343204339)
                  ·
                    refine ⟨10985884370900439514806509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323922913933626343204339 10985884370900439514806509)
                    ·
                      refine ⟨4119706639087664818052441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10985884370900439514806509 4119706639087664818052441)
                      ·
                        rfl

theorem cell23_8023100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_8023100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023100 prefixEnd_8023100 := by exact prefixLift 8023100
  have htrace : WordTrace (prefixWord ++ tailWord_8023100) baseStart_8023100 baseEnd_8023100 := by
    simpa [prefixWord, tailWord_8023100, baseEnd_8023100] using wordTrace_append hprefix tailTrace_8023100
  have hstable : (prefixWord ++ tailWord_8023100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023100).length < 2 ^ (prefixWord ++ tailWord_8023100).sum := by decide
  have hdescent : baseEnd_8023100 < baseStart_8023100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023136 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_8023136 : Nat := 118140960795 + 8023136 * 2 ^ 59
def prefixEnd_8023136 : Nat := 4983230072969 + 3 ^ 40 * 8023136 * 2
def baseEnd_8023136 : Nat := 4119725124391226677202275

theorem tailTrace_8023136 : CollatzResearch.WordTrace tailWord_8023136 prefixEnd_8023136 4119725124391226677202275 := by
  unfold tailWord_8023136
  simp only [CollatzResearch.WordTrace]
  refine ⟨146313905130777994691664631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195085206841037326255552841 146313905130777994691664631)
  ·
    refine ⟨219470857696166992037496947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146313905130777994691664631 219470857696166992037496947)
    ·
      refine ⟨329206286544250488056245421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219470857696166992037496947 329206286544250488056245421)
      ·
        refine ⟨123452357454093933021092033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329206286544250488056245421 123452357454093933021092033)
        ·
          refine ⟨92589268090570449765819025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123452357454093933021092033 92589268090570449765819025)
          ·
            refine ⟨69441951067927837324364269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92589268090570449765819025 69441951067927837324364269)
            ·
              refine ⟨26040731650472938996636601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69441951067927837324364269 26040731650472938996636601)
              ·
                refine ⟨19530548737854704247477451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26040731650472938996636601 19530548737854704247477451)
                ·
                  refine ⟨29295823106782056371216177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19530548737854704247477451 29295823106782056371216177)
                  ·
                    refine ⟨21971867330086542278412133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29295823106782056371216177 21971867330086542278412133)
                    ·
                      refine ⟨4119725124391226677202275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21971867330086542278412133 4119725124391226677202275)
                      ·
                        rfl

theorem cell23_8023136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_8023136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023136 prefixEnd_8023136 := by exact prefixLift 8023136
  have htrace : WordTrace (prefixWord ++ tailWord_8023136) baseStart_8023136 baseEnd_8023136 := by
    simpa [prefixWord, tailWord_8023136, baseEnd_8023136] using wordTrace_append hprefix tailTrace_8023136
  have hstable : (prefixWord ++ tailWord_8023136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023136).length < 2 ^ (prefixWord ++ tailWord_8023136).sum := by decide
  have hdescent : baseEnd_8023136 < baseStart_8023136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023143 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_8023143 : Nat := 118140960795 + 8023143 * 2 ^ 59
def prefixEnd_8023143 : Nat := 4983230072969 + 3 ^ 40 * 8023143 * 2
def baseEnd_8023143 : Nat := 4119728718755808149814743

theorem tailTrace_8023143 : CollatzResearch.WordTrace tailWord_8023143 prefixEnd_8023143 4119728718755808149814743 := by
  unfold tailWord_8023143
  simp only [CollatzResearch.WordTrace]
  refine ⟨292628065572530629578834083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195085377048353753052556055 292628065572530629578834083)
  ·
    refine ⟨438942098358795944368251125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292628065572530629578834083 438942098358795944368251125)
    ·
      refine ⟨41150821721137119784523543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438942098358795944368251125 41150821721137119784523543)
      ·
        refine ⟨61726232581705679676785315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41150821721137119784523543 61726232581705679676785315)
        ·
          refine ⟨92589348872558519515177973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61726232581705679676785315 92589348872558519515177973)
          ·
            refine ⟨8680251456802361204547935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92589348872558519515177973 8680251456802361204547935)
            ·
              refine ⟨13020377185203541806821903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680251456802361204547935 13020377185203541806821903)
              ·
                refine ⟨19530565777805312710232855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13020377185203541806821903 19530565777805312710232855)
                ·
                  refine ⟨29295848666707969065349283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19530565777805312710232855 29295848666707969065349283)
                  ·
                    refine ⟨43943773000061953598023925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29295848666707969065349283 43943773000061953598023925)
                    ·
                      refine ⟨4119728718755808149814743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43943773000061953598023925 4119728718755808149814743)
                      ·
                        rfl

theorem cell23_8023143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_8023143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023143 prefixEnd_8023143 := by exact prefixLift 8023143
  have htrace : WordTrace (prefixWord ++ tailWord_8023143) baseStart_8023143 baseEnd_8023143 := by
    simpa [prefixWord, tailWord_8023143, baseEnd_8023143] using wordTrace_append hprefix tailTrace_8023143
  have hstable : (prefixWord ++ tailWord_8023143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023143).length < 2 ^ (prefixWord ++ tailWord_8023143).sum := by decide
  have hdescent : baseEnd_8023143 < baseStart_8023143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023150 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_8023150 : Nat := 118140960795 + 8023150 * 2 ^ 59
def prefixEnd_8023150 : Nat := 4983230072969 + 3 ^ 40 * 8023150 * 2
def baseEnd_8023150 : Nat := 1373244104373463207475737

theorem tailTrace_8023150 : CollatzResearch.WordTrace tailWord_8023150 prefixEnd_8023150 1373244104373463207475737 := by
  unfold tailWord_8023150
  simp only [CollatzResearch.WordTrace]
  refine ⟨36578540110438158721792363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195085547255670179849559269 36578540110438158721792363)
  ·
    refine ⟨54867810165657238082688545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36578540110438158721792363 54867810165657238082688545)
    ·
      refine ⟨41150857624242928562016409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54867810165657238082688545 41150857624242928562016409)
      ·
        refine ⟨30863143218182196421512307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41150857624242928562016409 30863143218182196421512307)
        ·
          refine ⟨46294714827273294632268461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30863143218182196421512307 46294714827273294632268461)
          ·
            refine ⟨17360518060227485487100673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46294714827273294632268461 17360518060227485487100673)
            ·
              refine ⟨13020388545170614115325505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17360518060227485487100673 13020388545170614115325505)
              ·
                refine ⟨9765291408877960586494129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020388545170614115325505 9765291408877960586494129)
                ·
                  refine ⟨7323968556658470439870597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9765291408877960586494129 7323968556658470439870597)
                  ·
                    refine ⟨1373244104373463207475737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7323968556658470439870597 1373244104373463207475737)
                    ·
                      rfl

theorem cell23_8023150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_8023150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023150 prefixEnd_8023150 := by exact prefixLift 8023150
  have htrace : WordTrace (prefixWord ++ tailWord_8023150) baseStart_8023150 baseEnd_8023150 := by
    simpa [prefixWord, tailWord_8023150, baseEnd_8023150] using wordTrace_append hprefix tailTrace_8023150
  have hstable : (prefixWord ++ tailWord_8023150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023150).length < 2 ^ (prefixWord ++ tailWord_8023150).sum := by decide
  have hdescent : baseEnd_8023150 < baseStart_8023150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023159 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 9]
def baseStart_8023159 : Nat := 118140960795 + 8023159 * 2 ^ 59
def prefixEnd_8023159 : Nat := 4983230072969 + 3 ^ 40 * 8023159 * 2
def baseEnd_8023159 : Nat := 1373245644815426695738223

theorem tailTrace_8023159 : CollatzResearch.WordTrace tailWord_8023159 prefixEnd_8023159 1373245644815426695738223 := by
  unfold tailWord_8023159
  simp only [CollatzResearch.WordTrace]
  refine ⟨292628649140472664311416531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195085766093648442874277687 292628649140472664311416531)
  ·
    refine ⟨438942973710708996467124797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292628649140472664311416531 438942973710708996467124797)
    ·
      refine ⟨164603615141515873675171799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438942973710708996467124797 164603615141515873675171799)
      ·
        refine ⟨246905422712273810512757699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164603615141515873675171799 246905422712273810512757699)
        ·
          refine ⟨370358134068410715769136549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246905422712273810512757699 370358134068410715769136549)
          ·
            refine ⟨69442150137827009206713103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370358134068410715769136549 69442150137827009206713103)
            ·
              refine ⟨104163225206740513810069655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69442150137827009206713103 104163225206740513810069655)
              ·
                refine ⟨156244837810110770715104483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104163225206740513810069655 156244837810110770715104483)
                ·
                  refine ⟨234367256715166156072656725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156244837810110770715104483 234367256715166156072656725)
                  ·
                    refine ⟨1373245644815426695738223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234367256715166156072656725 1373245644815426695738223)
                    ·
                      rfl

theorem cell23_8023159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_8023159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023159 prefixEnd_8023159 := by exact prefixLift 8023159
  have htrace : WordTrace (prefixWord ++ tailWord_8023159) baseStart_8023159 baseEnd_8023159 := by
    simpa [prefixWord, tailWord_8023159, baseEnd_8023159] using wordTrace_append hprefix tailTrace_8023159
  have hstable : (prefixWord ++ tailWord_8023159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023159).length < 2 ^ (prefixWord ++ tailWord_8023159).sum := by decide
  have hdescent : baseEnd_8023159 < baseStart_8023159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023200 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 1, 3, 2]
def baseStart_8023200 : Nat := 118140960795 + 8023200 * 2 ^ 59
def prefixEnd_8023200 : Nat := 4983230072969 + 3 ^ 40 * 8023200 * 2
def baseEnd_8023200 : Nat := 4119757987153114426801981

theorem tailTrace_8023200 : CollatzResearch.WordTrace tailWord_8023200 prefixEnd_8023200 4119757987153114426801981 := by
  unfold tailWord_8023200
  simp only [CollatzResearch.WordTrace]
  refine ⟨146315072266662064156829527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195086763022216085542439369 146315072266662064156829527)
  ·
    refine ⟨219472608399993096235244291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146315072266662064156829527 219472608399993096235244291)
    ·
      refine ⟨329208912599989644352866437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219472608399993096235244291 329208912599989644352866437)
      ·
        refine ⟨61726671112498058316162457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329208912599989644352866437 61726671112498058316162457)
        ·
          refine ⟨46295003334373543737121843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61726671112498058316162457 46295003334373543737121843)
          ·
            refine ⟨69442505001560315605682765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46295003334373543737121843 69442505001560315605682765)
            ·
              refine ⟨26040939375585118352131037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69442505001560315605682765 26040939375585118352131037)
              ·
                refine ⟨9765352265844419382049139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26040939375585118352131037 9765352265844419382049139)
                ·
                  refine ⟨14648028398766629073073709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765352265844419382049139 14648028398766629073073709)
                  ·
                    refine ⟨5493010649537485902402641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14648028398766629073073709 5493010649537485902402641)
                    ·
                      refine ⟨4119757987153114426801981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493010649537485902402641 4119757987153114426801981)
                      ·
                        rfl

theorem cell23_8023200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_8023200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023200 prefixEnd_8023200 := by exact prefixLift 8023200
  have htrace : WordTrace (prefixWord ++ tailWord_8023200) baseStart_8023200 baseEnd_8023200 := by
    simpa [prefixWord, tailWord_8023200, baseEnd_8023200] using wordTrace_append hprefix tailTrace_8023200
  have hstable : (prefixWord ++ tailWord_8023200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023200).length < 2 ^ (prefixWord ++ tailWord_8023200).sum := by decide
  have hdescent : baseEnd_8023200 < baseStart_8023200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023207 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_8023207 : Nat := 118140960795 + 8023207 * 2 ^ 59
def prefixEnd_8023207 : Nat := 4983230072969 + 3 ^ 40 * 8023207 * 2
def baseEnd_8023207 : Nat := 4119761581517695899414449

theorem tailTrace_8023207 : CollatzResearch.WordTrace tailWord_8023207 prefixEnd_8023207 4119761581517695899414449 := by
  unfold tailWord_8023207
  simp only [CollatzResearch.WordTrace]
  refine ⟨292630399844298768509163875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195086933229532512339442583 292630399844298768509163875)
  ·
    refine ⟨438945599766448152763745813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292630399844298768509163875 438945599766448152763745813)
    ·
      refine ⟨20575574989052257160800585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 438945599766448152763745813 20575574989052257160800585)
      ·
        refine ⟨15431681241789192870600439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20575574989052257160800585 15431681241789192870600439)
        ·
          refine ⟨23147521862683789305900659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15431681241789192870600439 23147521862683789305900659)
          ·
            refine ⟨34721282794025683958850989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23147521862683789305900659 34721282794025683958850989)
            ·
              refine ⟨13020481047759631484569121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34721282794025683958850989 13020481047759631484569121)
              ·
                refine ⟨9765360785819723613426841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020481047759631484569121 9765360785819723613426841)
                ·
                  refine ⟨7324020589364792710070131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9765360785819723613426841 7324020589364792710070131)
                  ·
                    refine ⟨10986030884047189065105197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7324020589364792710070131 10986030884047189065105197)
                    ·
                      refine ⟨4119761581517695899414449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986030884047189065105197 4119761581517695899414449)
                      ·
                        rfl

theorem cell23_8023207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_8023207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023207 prefixEnd_8023207 := by exact prefixLift 8023207
  have htrace : WordTrace (prefixWord ++ tailWord_8023207) baseStart_8023207 baseEnd_8023207 := by
    simpa [prefixWord, tailWord_8023207, baseEnd_8023207] using wordTrace_append hprefix tailTrace_8023207
  have hstable : (prefixWord ++ tailWord_8023207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023207).length < 2 ^ (prefixWord ++ tailWord_8023207).sum := by decide
  have hdescent : baseEnd_8023207 < baseStart_8023207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023276 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_8023276 : Nat := 118140960795 + 8023276 * 2 ^ 59
def prefixEnd_8023276 : Nat := 4983230072969 + 3 ^ 40 * 8023276 * 2
def baseEnd_8023276 : Nat := 4119797011682856129451631

theorem tailTrace_8023276 : CollatzResearch.WordTrace tailWord_8023276 prefixEnd_8023276 4119797011682856129451631 := by
  unfold tailWord_8023276
  simp only [CollatzResearch.WordTrace]
  refine ⟨146316458240524396646712841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195088610987365862195617121 146316458240524396646712841)
  ·
    refine ⟨109737343680393297485034631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146316458240524396646712841 109737343680393297485034631)
    ·
      refine ⟨164606015520589946227551947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109737343680393297485034631 164606015520589946227551947)
      ·
        refine ⟨246909023280884919341327921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164606015520589946227551947 246909023280884919341327921)
        ·
          refine ⟨185181767460663689505995941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246909023280884919341327921 185181767460663689505995941)
          ·
            refine ⟨34721581398874441782374239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185181767460663689505995941 34721581398874441782374239)
            ·
              refine ⟨52082372098311662673561359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34721581398874441782374239 52082372098311662673561359)
              ·
                refine ⟨78123558147467494010342039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52082372098311662673561359 78123558147467494010342039)
                ·
                  refine ⟨117185337221201241015513059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78123558147467494010342039 117185337221201241015513059)
                  ·
                    refine ⟨175778005831801861523269589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117185337221201241015513059 175778005831801861523269589)
                    ·
                      refine ⟨4119797011682856129451631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175778005831801861523269589 4119797011682856129451631)
                      ·
                        rfl

theorem cell23_8023276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_8023276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023276 prefixEnd_8023276 := by exact prefixLift 8023276
  have htrace : WordTrace (prefixWord ++ tailWord_8023276) baseStart_8023276 baseEnd_8023276 := by
    simpa [prefixWord, tailWord_8023276, baseEnd_8023276] using wordTrace_append hprefix tailTrace_8023276
  have hstable : (prefixWord ++ tailWord_8023276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023276).length < 2 ^ (prefixWord ++ tailWord_8023276).sum := by decide
  have hdescent : baseEnd_8023276 < baseStart_8023276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023300 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_8023300 : Nat := 118140960795 + 8023300 * 2 ^ 59
def prefixEnd_8023300 : Nat := 4983230072969 + 3 ^ 40 * 8023300 * 2
def baseEnd_8023300 : Nat := 1373269778406188011850507

theorem tailTrace_8023300 : CollatzResearch.WordTrace tailWord_8023300 prefixEnd_8023300 1373269778406188011850507 := by
  unfold tailWord_8023300
  simp only [CollatzResearch.WordTrace]
  refine ⟨146316895916480922696149677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195089194555307896928199569 146316895916480922696149677)
  ·
    refine ⟨54868835968680346011056129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146316895916480922696149677 54868835968680346011056129)
    ·
      refine ⟨41151626976510259508292097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54868835968680346011056129 41151626976510259508292097)
      ·
        refine ⟨30863720232382694631219073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41151626976510259508292097 30863720232382694631219073)
        ·
          refine ⟨23147790174287020973414305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30863720232382694631219073 23147790174287020973414305)
          ·
            refine ⟨17360842630715265730060729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23147790174287020973414305 17360842630715265730060729)
            ·
              refine ⟨13020631973036449297545547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17360842630715265730060729 13020631973036449297545547)
              ·
                refine ⟨19530947959554673946318321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13020631973036449297545547 19530947959554673946318321)
                ·
                  refine ⟨14648210969666005459738741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19530947959554673946318321 14648210969666005459738741)
                  ·
                    refine ⟨1373269778406188011850507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14648210969666005459738741 1373269778406188011850507)
                    ·
                      rfl

theorem cell23_8023300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_8023300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023300 prefixEnd_8023300 := by exact prefixLift 8023300
  have htrace : WordTrace (prefixWord ++ tailWord_8023300) baseStart_8023300 baseEnd_8023300 := by
    simpa [prefixWord, tailWord_8023300, baseEnd_8023300] using wordTrace_append hprefix tailTrace_8023300
  have hstable : (prefixWord ++ tailWord_8023300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023300).length < 2 ^ (prefixWord ++ tailWord_8023300).sum := by decide
  have hdescent : baseEnd_8023300 < baseStart_8023300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023357 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8023357 : Nat := 118140960795 + 8023357 * 2 ^ 59
def prefixEnd_8023357 : Nat := 4983230072969 + 3 ^ 40 * 8023357 * 2
def baseEnd_8023357 : Nat := 4119838603615870312538759

theorem tailTrace_8023357 : CollatzResearch.WordTrace tailWord_8023357 prefixEnd_8023357 4119838603615870312538759 := by
  unfold tailWord_8023357
  simp only [CollatzResearch.WordTrace]
  refine ⟨292635870793755344127124325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195090580529170229418082883 292635870793755344127124325)
  ·
    refine ⟨54869225773829127023835811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292635870793755344127124325 54869225773829127023835811)
    ·
      refine ⟨82303838660743690535753717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54869225773829127023835811 82303838660743690535753717)
      ·
        refine ⟨7715984874444720987726911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82303838660743690535753717 7715984874444720987726911)
        ·
          refine ⟨11573977311667081481590367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7715984874444720987726911 11573977311667081481590367)
          ·
            refine ⟨17360965967500622222385551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11573977311667081481590367 17360965967500622222385551)
            ·
              refine ⟨26041448951250933333578327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17360965967500622222385551 26041448951250933333578327)
              ·
                refine ⟨39062173426876400000367491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26041448951250933333578327 39062173426876400000367491)
                ·
                  refine ⟨58593260140314600000551237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39062173426876400000367491 58593260140314600000551237)
                  ·
                    refine ⟨10986236276308987500103357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58593260140314600000551237 10986236276308987500103357)
                    ·
                      refine ⟨4119838603615870312538759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986236276308987500103357 4119838603615870312538759)
                      ·
                        rfl

theorem cell23_8023357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8023357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023357 prefixEnd_8023357 := by exact prefixLift 8023357
  have htrace : WordTrace (prefixWord ++ tailWord_8023357) baseStart_8023357 baseEnd_8023357 := by
    simpa [prefixWord, tailWord_8023357, baseEnd_8023357] using wordTrace_append hprefix tailTrace_8023357
  have hstable : (prefixWord ++ tailWord_8023357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023357).length < 2 ^ (prefixWord ++ tailWord_8023357).sum := by decide
  have hdescent : baseEnd_8023357 < baseStart_8023357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023364 : List Nat := [2, 3, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_8023364 : Nat := 118140960795 + 8023364 * 2 ^ 59
def prefixEnd_8023364 : Nat := 4983230072969 + 3 ^ 40 * 8023364 * 2
def baseEnd_8023364 : Nat := 1373280732660150595050409

theorem tailTrace_8023364 : CollatzResearch.WordTrace tailWord_8023364 prefixEnd_8023364 1373280732660150595050409 := by
  unfold tailWord_8023364
  simp only [CollatzResearch.WordTrace]
  refine ⟨146318063052364992161314573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195090750736486656215086097 146318063052364992161314573)
  ·
    refine ⟨54869273644636872060492965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146318063052364992161314573 54869273644636872060492965)
    ·
      refine ⟨10287988808369413511342431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54869273644636872060492965 10287988808369413511342431)
      ·
        refine ⟨15431983212554120267013647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10287988808369413511342431 15431983212554120267013647)
        ·
          refine ⟨23147974818831180400520471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15431983212554120267013647 23147974818831180400520471)
          ·
            refine ⟨34721962228246770600780707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23147974818831180400520471 34721962228246770600780707)
            ·
              refine ⟨52082943342370155901171061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34721962228246770600780707 52082943342370155901171061)
              ·
                refine ⟨4882775938347202115734787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52082943342370155901171061 4882775938347202115734787)
                ·
                  refine ⟨7324163907520803173602181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882775938347202115734787 7324163907520803173602181)
                  ·
                    refine ⟨1373280732660150595050409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324163907520803173602181 1373280732660150595050409)
                    ·
                      rfl

theorem cell23_8023364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_8023364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023364 prefixEnd_8023364 := by exact prefixLift 8023364
  have htrace : WordTrace (prefixWord ++ tailWord_8023364) baseStart_8023364 baseEnd_8023364 := by
    simpa [prefixWord, tailWord_8023364, baseEnd_8023364] using wordTrace_append hprefix tailTrace_8023364
  have hstable : (prefixWord ++ tailWord_8023364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023364).length < 2 ^ (prefixWord ++ tailWord_8023364).sum := by decide
  have hdescent : baseEnd_8023364 < baseStart_8023364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023393 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_8023393 : Nat := 118140960795 + 8023393 * 2 ^ 59
def prefixEnd_8023393 : Nat := 4983230072969 + 3 ^ 40 * 8023393 * 2
def baseEnd_8023393 : Nat := 4119857088919432171688593

theorem tailTrace_8023393 : CollatzResearch.WordTrace tailWord_8023393 prefixEnd_8023393 4119857088919432171688593 := by
  unfold tailWord_8023393
  simp only [CollatzResearch.WordTrace]
  refine ⟨292637183821624922275434833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195091455881083281516956555 292637183821624922275434833)
  ·
    refine ⟨219477887866218691706576125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292637183821624922275434833 219477887866218691706576125)
    ·
      refine ⟨82304207949832009389966047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219477887866218691706576125 82304207949832009389966047)
      ·
        refine ⟨123456311924748014084949071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82304207949832009389966047 123456311924748014084949071)
        ·
          refine ⟨185184467887122021127423607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123456311924748014084949071 185184467887122021127423607)
          ·
            refine ⟨277776701830683031691135411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185184467887122021127423607 277776701830683031691135411)
            ·
              refine ⟨416665052746024547536703117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277776701830683031691135411 416665052746024547536703117)
              ·
                refine ⟨156249394779759205326263669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416665052746024547536703117 156249394779759205326263669)
                ·
                  refine ⟨14648380760602425499337219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156249394779759205326263669 14648380760602425499337219)
                  ·
                    refine ⟨21972571140903638249005829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14648380760602425499337219 21972571140903638249005829)
                    ·
                      refine ⟨4119857088919432171688593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21972571140903638249005829 4119857088919432171688593)
                      ·
                        rfl

theorem cell23_8023393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_8023393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023393 prefixEnd_8023393 := by exact prefixLift 8023393
  have htrace : WordTrace (prefixWord ++ tailWord_8023393) baseStart_8023393 baseEnd_8023393 := by
    simpa [prefixWord, tailWord_8023393, baseEnd_8023393] using wordTrace_append hprefix tailTrace_8023393
  have hstable : (prefixWord ++ tailWord_8023393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023393).length < 2 ^ (prefixWord ++ tailWord_8023393).sum := by decide
  have hdescent : baseEnd_8023393 < baseStart_8023393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023403 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 8, 4]
def baseStart_8023403 : Nat := 118140960795 + 8023403 * 2 ^ 59
def prefixEnd_8023403 : Nat := 4983230072969 + 3 ^ 40 * 8023403 * 2
def baseEnd_8023403 : Nat := 1373287407908659044187849

theorem tailTrace_8023403 : CollatzResearch.WordTrace tailWord_8023403 prefixEnd_8023403 1373287407908659044187849 := by
  unfold tailWord_8023403
  simp only [CollatzResearch.WordTrace]
  refine ⟨292637548551588693983298863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195091699034392462655532575 292637548551588693983298863)
  ·
    refine ⟨438956322827383040974948295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292637548551588693983298863 438956322827383040974948295)
    ·
      refine ⟨658434484241074561462422443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438956322827383040974948295 658434484241074561462422443)
      ·
        refine ⟨987651726361611842193633665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658434484241074561462422443 987651726361611842193633665)
        ·
          refine ⟨740738794771208881645225249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987651726361611842193633665 740738794771208881645225249)
          ·
            refine ⟨555554096078406661233918937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740738794771208881645225249 555554096078406661233918937)
            ·
              refine ⟨416665572058804995925439203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555554096078406661233918937 416665572058804995925439203)
              ·
                refine ⟨624998358088207493888158805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416665572058804995925439203 624998358088207493888158805)
                ·
                  refine ⟨7324199508846181569001861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 624998358088207493888158805 7324199508846181569001861)
                  ·
                    refine ⟨1373287407908659044187849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324199508846181569001861 1373287407908659044187849)
                    ·
                      rfl

theorem cell23_8023403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 4].length) (baseStart_8023403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023403 prefixEnd_8023403 := by exact prefixLift 8023403
  have htrace : WordTrace (prefixWord ++ tailWord_8023403) baseStart_8023403 baseEnd_8023403 := by
    simpa [prefixWord, tailWord_8023403, baseEnd_8023403] using wordTrace_append hprefix tailTrace_8023403
  have hstable : (prefixWord ++ tailWord_8023403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023403).length < 2 ^ (prefixWord ++ tailWord_8023403).sum := by decide
  have hdescent : baseEnd_8023403 < baseStart_8023403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023410 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_8023410 : Nat := 118140960795 + 8023410 * 2 ^ 59
def prefixEnd_8023410 : Nat := 4983230072969 + 3 ^ 40 * 8023410 * 2
def baseEnd_8023410 : Nat := 4119865818090558605176015

theorem tailTrace_8023410 : CollatzResearch.WordTrace tailWord_8023410 prefixEnd_8023410 4119865818090558605176015 := by
  unfold tailWord_8023410
  simp only [CollatzResearch.WordTrace]
  refine ⟨73159450965640833544700921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195091869241708889452535789 73159450965640833544700921)
  ·
    refine ⟨54869588224230625158525691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73159450965640833544700921 54869588224230625158525691)
    ·
      refine ⟨82304382336345937737788537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54869588224230625158525691 82304382336345937737788537)
      ·
        refine ⟨61728286752259453303341403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82304382336345937737788537 61728286752259453303341403)
        ·
          refine ⟨92592430128389179955012105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61728286752259453303341403 92592430128389179955012105)
          ·
            refine ⟨69444322596291884966259079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92592430128389179955012105 69444322596291884966259079)
            ·
              refine ⟨104166483894437827449388619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69444322596291884966259079 104166483894437827449388619)
              ·
                refine ⟨156249725841656741174082929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104166483894437827449388619 156249725841656741174082929)
                ·
                  refine ⟨117187294381242555880562197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156249725841656741174082929 117187294381242555880562197)
                  ·
                    refine ⟨5493154424120744806901353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117187294381242555880562197 5493154424120744806901353)
                    ·
                      refine ⟨4119865818090558605176015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493154424120744806901353 4119865818090558605176015)
                      ·
                        rfl

theorem cell23_8023410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_8023410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023410 prefixEnd_8023410 := by exact prefixLift 8023410
  have htrace : WordTrace (prefixWord ++ tailWord_8023410) baseStart_8023410 baseEnd_8023410 := by
    simpa [prefixWord, tailWord_8023410, baseEnd_8023410] using wordTrace_append hprefix tailTrace_8023410
  have hstable : (prefixWord ++ tailWord_8023410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023410).length < 2 ^ (prefixWord ++ tailWord_8023410).sum := by decide
  have hdescent : baseEnd_8023410 < baseStart_8023410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023438 : List Nat := [4, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_8023438 : Nat := 118140960795 + 8023438 * 2 ^ 59
def prefixEnd_8023438 : Nat := 4983230072969 + 3 ^ 40 * 8023438 * 2
def baseEnd_8023438 : Nat := 4119880195548884495625887

theorem tailTrace_8023438 : CollatzResearch.WordTrace tailWord_8023438 prefixEnd_8023438 4119880195548884495625887 := by
  unfold tailWord_8023438
  simp only [CollatzResearch.WordTrace]
  refine ⟨36579853138307736870102871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195092550070974596640548645 36579853138307736870102871)
  ·
    refine ⟨54869779707461605305154307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36579853138307736870102871 54869779707461605305154307)
    ·
      refine ⟨82304669561192407957731461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54869779707461605305154307 82304669561192407957731461)
      ·
        refine ⟨15432125542723576492074649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82304669561192407957731461 15432125542723576492074649)
        ·
          refine ⟨11574094157042682369055987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15432125542723576492074649 11574094157042682369055987)
          ·
            refine ⟨17361141235564023553583981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574094157042682369055987 17361141235564023553583981)
            ·
              refine ⟨6510427963336508832593993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17361141235564023553583981 6510427963336508832593993)
              ·
                refine ⟨4882820972502381624445495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6510427963336508832593993 4882820972502381624445495)
                ·
                  refine ⟨7324231458753572436668243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882820972502381624445495 7324231458753572436668243)
                  ·
                    refine ⟨10986347188130358655002365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7324231458753572436668243 10986347188130358655002365)
                    ·
                      refine ⟨4119880195548884495625887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986347188130358655002365 4119880195548884495625887)
                      ·
                        rfl

theorem cell23_8023438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_8023438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023438 prefixEnd_8023438 := by exact prefixLift 8023438
  have htrace : WordTrace (prefixWord ++ tailWord_8023438) baseStart_8023438 baseEnd_8023438 := by
    simpa [prefixWord, tailWord_8023438, baseEnd_8023438] using wordTrace_append hprefix tailTrace_8023438
  have hstable : (prefixWord ++ tailWord_8023438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023438).length < 2 ^ (prefixWord ++ tailWord_8023438).sum := by decide
  have hdescent : baseEnd_8023438 < baseStart_8023438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023460 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_8023460 : Nat := 118140960795 + 8023460 * 2 ^ 59
def prefixEnd_8023460 : Nat := 4983230072969 + 3 ^ 40 * 8023460 * 2
def baseEnd_8023460 : Nat := 4119891492123283409550785

theorem tailTrace_8023460 : CollatzResearch.WordTrace tailWord_8023460 prefixEnd_8023460 4119891492123283409550785 := by
  unfold tailWord_8023460
  simp only [CollatzResearch.WordTrace]
  refine ⟨146319813756191096359061917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195093085008254795145415889 146319813756191096359061917)
  ·
    refine ⟨54869930158571661134648219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146319813756191096359061917 54869930158571661134648219)
    ·
      refine ⟨82304895237857491701972329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54869930158571661134648219 82304895237857491701972329)
      ·
        refine ⟨61728671428393118776479247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82304895237857491701972329 61728671428393118776479247)
        ·
          refine ⟨92593007142589678164718871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61728671428393118776479247 92593007142589678164718871)
          ·
            refine ⟨138889510713884517247078307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92593007142589678164718871 138889510713884517247078307)
            ·
              refine ⟨208334266070826775870617461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138889510713884517247078307 208334266070826775870617461)
              ·
                refine ⟨19531337444140010237870387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208334266070826775870617461 19531337444140010237870387)
                ·
                  refine ⟨29297006166210015356805581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19531337444140010237870387 29297006166210015356805581)
                  ·
                    refine ⟨10986377312328755758802093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29297006166210015356805581 10986377312328755758802093)
                    ·
                      refine ⟨4119891492123283409550785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986377312328755758802093 4119891492123283409550785)
                      ·
                        rfl

theorem cell23_8023460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_8023460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023460 prefixEnd_8023460 := by exact prefixLift 8023460
  have htrace : WordTrace (prefixWord ++ tailWord_8023460) baseStart_8023460 baseEnd_8023460 := by
    simpa [prefixWord, tailWord_8023460, baseEnd_8023460] using wordTrace_append hprefix tailTrace_8023460
  have hstable : (prefixWord ++ tailWord_8023460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023460).length < 2 ^ (prefixWord ++ tailWord_8023460).sum := by decide
  have hdescent : baseEnd_8023460 < baseStart_8023460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023464 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_8023464 : Nat := 118140960795 + 8023464 * 2 ^ 59
def prefixEnd_8023464 : Nat := 4983230072969 + 3 ^ 40 * 8023464 * 2
def baseEnd_8023464 : Nat := 4119893546045901393900767

theorem tailTrace_8023464 : CollatzResearch.WordTrace tailWord_8023464 prefixEnd_8023464 4119893546045901393900767 := by
  unfold tailWord_8023464
  simp only [CollatzResearch.WordTrace]
  refine ⟨146319886702183850700634723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195093182269578467600846297 146319886702183850700634723)
  ·
    refine ⟨219479830053275776050952085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146319886702183850700634723 219479830053275776050952085)
    ·
      refine ⟨10288117033747302002388379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219479830053275776050952085 10288117033747302002388379)
      ·
        refine ⟨15432175550620953003582569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10288117033747302002388379 15432175550620953003582569)
        ·
          refine ⟨11574131662965714752686927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15432175550620953003582569 11574131662965714752686927)
          ·
            refine ⟨17361197494448572129030391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574131662965714752686927 17361197494448572129030391)
            ·
              refine ⟨26041796241672858193545587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17361197494448572129030391 26041796241672858193545587)
              ·
                refine ⟨39062694362509287290318381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26041796241672858193545587 39062694362509287290318381)
                ·
                  refine ⟨14648510385940982733869393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39062694362509287290318381 14648510385940982733869393)
                  ·
                    refine ⟨10986382789455737050402045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14648510385940982733869393 10986382789455737050402045)
                    ·
                      refine ⟨4119893546045901393900767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986382789455737050402045 4119893546045901393900767)
                      ·
                        rfl

theorem cell23_8023464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_8023464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023464 prefixEnd_8023464 := by exact prefixLift 8023464
  have htrace : WordTrace (prefixWord ++ tailWord_8023464) baseStart_8023464 baseEnd_8023464 := by
    simpa [prefixWord, tailWord_8023464, baseEnd_8023464] using wordTrace_append hprefix tailTrace_8023464
  have hstable : (prefixWord ++ tailWord_8023464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023464).length < 2 ^ (prefixWord ++ tailWord_8023464).sum := by decide
  have hdescent : baseEnd_8023464 < baseStart_8023464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023477 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_8023477 : Nat := 118140960795 + 8023477 * 2 ^ 59
def prefixEnd_8023477 : Nat := 4983230072969 + 3 ^ 40 * 8023477 * 2
def baseEnd_8023477 : Nat := 4119900221294409843038207

theorem tailTrace_8023477 : CollatzResearch.WordTrace tailWord_8023477 prefixEnd_8023477 4119900221294409843038207 := by
  unfold tailWord_8023477
  simp only [CollatzResearch.WordTrace]
  refine ⟨292640247553320604621492685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195093498368880403080995123 292640247553320604621492685)
  ·
    refine ⟨109740092832495226733059757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292640247553320604621492685 109740092832495226733059757)
    ·
      refine ⟨41152534812185710024897409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109740092832495226733059757 41152534812185710024897409)
      ·
        refine ⟨30864401109139282518673057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41152534812185710024897409 30864401109139282518673057)
        ·
          refine ⟨23148300831854461889004793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30864401109139282518673057 23148300831854461889004793)
          ·
            refine ⟨17361225623890846416753595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23148300831854461889004793 17361225623890846416753595)
            ·
              refine ⟨26041838435836269625130393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17361225623890846416753595 26041838435836269625130393)
              ·
                refine ⟨19531378826877202218847795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26041838435836269625130393 19531378826877202218847795)
                ·
                  refine ⟨29297068240315803328271693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19531378826877202218847795 29297068240315803328271693)
                  ·
                    refine ⟨10986400590118426248101885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29297068240315803328271693 10986400590118426248101885)
                    ·
                      refine ⟨4119900221294409843038207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986400590118426248101885 4119900221294409843038207)
                      ·
                        rfl

theorem cell23_8023477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_8023477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023477 prefixEnd_8023477 := by exact prefixLift 8023477
  have htrace : WordTrace (prefixWord ++ tailWord_8023477) baseStart_8023477 baseEnd_8023477 := by
    simpa [prefixWord, tailWord_8023477, baseEnd_8023477] using wordTrace_append hprefix tailTrace_8023477
  have hstable : (prefixWord ++ tailWord_8023477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023477).length < 2 ^ (prefixWord ++ tailWord_8023477).sum := by decide
  have hdescent : baseEnd_8023477 < baseStart_8023477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023487 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 1, 3, 2]
def baseStart_8023487 : Nat := 118140960795 + 8023487 * 2 ^ 59
def prefixEnd_8023487 : Nat := 4983230072969 + 3 ^ 40 * 8023487 * 2
def baseEnd_8023487 : Nat := 4119905356100954803913161

theorem tailTrace_8023487 : CollatzResearch.WordTrace tailWord_8023487 prefixEnd_8023487 4119905356100954803913161 := by
  unfold tailWord_8023487
  simp only [CollatzResearch.WordTrace]
  refine ⟨292640612283284376329356715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195093741522189584219571143 292640612283284376329356715)
  ·
    refine ⟨438960918424926564494035073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292640612283284376329356715 438960918424926564494035073)
    ·
      refine ⟨329220688818694923370526305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438960918424926564494035073 329220688818694923370526305)
      ·
        refine ⟨246915516614021192527894729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329220688818694923370526305 246915516614021192527894729)
        ·
          refine ⟨185186637460515894395921047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246915516614021192527894729 185186637460515894395921047)
          ·
            refine ⟨277779956190773841593881571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185186637460515894395921047 277779956190773841593881571)
            ·
              refine ⟨416669934286160762390822357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277779956190773841593881571 416669934286160762390822357)
              ·
                refine ⟨9765701584831892868534899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 416669934286160762390822357 9765701584831892868534899)
                ·
                  refine ⟨14648552377247839302802349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765701584831892868534899 14648552377247839302802349)
                  ·
                    refine ⟨5493207141467939738550881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14648552377247839302802349 5493207141467939738550881)
                    ·
                      refine ⟨4119905356100954803913161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493207141467939738550881 4119905356100954803913161)
                      ·
                        rfl

theorem cell23_8023487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_8023487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023487 prefixEnd_8023487 := by exact prefixLift 8023487
  have htrace : WordTrace (prefixWord ++ tailWord_8023487) baseStart_8023487 baseEnd_8023487 := by
    simpa [prefixWord, tailWord_8023487, baseEnd_8023487] using wordTrace_append hprefix tailTrace_8023487
  have hstable : (prefixWord ++ tailWord_8023487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023487).length < 2 ^ (prefixWord ++ tailWord_8023487).sum := by decide
  have hdescent : baseEnd_8023487 < baseStart_8023487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023500 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_8023500 : Nat := 118140960795 + 8023500 * 2 ^ 59
def prefixEnd_8023500 : Nat := 4983230072969 + 3 ^ 40 * 8023500 * 2
def baseEnd_8023500 : Nat := 4119912031349463253050601

theorem tailTrace_8023500 : CollatzResearch.WordTrace tailWord_8023500 prefixEnd_8023500 4119912031349463253050601 := by
  unfold tailWord_8023500
  simp only [CollatzResearch.WordTrace]
  refine ⟨146320543216118639774789977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195094057621491519699719969 146320543216118639774789977)
  ·
    refine ⟨109740407412088979831092483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146320543216118639774789977 109740407412088979831092483)
    ·
      refine ⟨164610611118133469746638725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109740407412088979831092483 164610611118133469746638725)
      ·
        refine ⟨30864489584650025577494761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164610611118133469746638725 30864489584650025577494761)
        ·
          refine ⟨23148367188487519183121071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30864489584650025577494761 23148367188487519183121071)
          ·
            refine ⟨34722550782731278774681607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23148367188487519183121071 34722550782731278774681607)
            ·
              refine ⟨52083826174096918162022411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34722550782731278774681607 52083826174096918162022411)
              ·
                refine ⟨78125739261145377243033617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52083826174096918162022411 78125739261145377243033617)
                ·
                  refine ⟨58594304445859032932275213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78125739261145377243033617 58594304445859032932275213)
                  ·
                    refine ⟨21972864167197137349603205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58594304445859032932275213 21972864167197137349603205)
                    ·
                      refine ⟨4119912031349463253050601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21972864167197137349603205 4119912031349463253050601)
                      ·
                        rfl

theorem cell23_8023500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_8023500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023500 prefixEnd_8023500 := by exact prefixLift 8023500
  have htrace : WordTrace (prefixWord ++ tailWord_8023500) baseStart_8023500 baseEnd_8023500 := by
    simpa [prefixWord, tailWord_8023500, baseEnd_8023500] using wordTrace_append hprefix tailTrace_8023500
  have hstable : (prefixWord ++ tailWord_8023500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023500).length < 2 ^ (prefixWord ++ tailWord_8023500).sum := by decide
  have hdescent : baseEnd_8023500 < baseStart_8023500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023503 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_8023503 : Nat := 118140960795 + 8023503 * 2 ^ 59
def prefixEnd_8023503 : Nat := 4983230072969 + 3 ^ 40 * 8023503 * 2
def baseEnd_8023503 : Nat := 4119913571791426741313087

theorem tailTrace_8023503 : CollatzResearch.WordTrace tailWord_8023503 prefixEnd_8023503 4119913571791426741313087 := by
  unfold tailWord_8023503
  simp only [CollatzResearch.WordTrace]
  refine ⟨292641195851226411061939163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195094130567484274041292775 292641195851226411061939163)
  ·
    refine ⟨438961793776839616592908745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292641195851226411061939163 438961793776839616592908745)
    ·
      refine ⟨329221345332629712444681559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438961793776839616592908745 329221345332629712444681559)
      ·
        refine ⟨493832017998944568667022339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329221345332629712444681559 493832017998944568667022339)
        ·
          refine ⟨740748026998416853000533509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493832017998944568667022339 740748026998416853000533509)
          ·
            refine ⟨138890255062203159937600033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 740748026998416853000533509 138890255062203159937600033)
            ·
              refine ⟨104167691296652369953200025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138890255062203159937600033 104167691296652369953200025)
              ·
                refine ⟨78125768472489277464900019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104167691296652369953200025 78125768472489277464900019)
                ·
                  refine ⟨117188652708733916197350029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78125768472489277464900019 117188652708733916197350029)
                  ·
                    refine ⟨43945744765775218574006261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117188652708733916197350029 43945744765775218574006261)
                    ·
                      refine ⟨4119913571791426741313087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43945744765775218574006261 4119913571791426741313087)
                      ·
                        rfl

theorem cell23_8023503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_8023503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023503 prefixEnd_8023503 := by exact prefixLift 8023503
  have htrace : WordTrace (prefixWord ++ tailWord_8023503) baseStart_8023503 baseEnd_8023503 := by
    simpa [prefixWord, tailWord_8023503, baseEnd_8023503] using wordTrace_append hprefix tailTrace_8023503
  have hstable : (prefixWord ++ tailWord_8023503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023503).length < 2 ^ (prefixWord ++ tailWord_8023503).sum := by decide
  have hdescent : baseEnd_8023503 < baseStart_8023503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023534 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_8023534 : Nat := 118140960795 + 8023534 * 2 ^ 59
def prefixEnd_8023534 : Nat := 4983230072969 + 3 ^ 40 * 8023534 * 2
def baseEnd_8023534 : Nat := 4119929489691716120025445

theorem tailTrace_8023534 : CollatzResearch.WordTrace tailWord_8023534 prefixEnd_8023534 4119929489691716120025445 := by
  unfold tailWord_8023534
  simp only [CollatzResearch.WordTrace]
  refine ⟨36580290814264262919539707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195094884342742735570878437 36580290814264262919539707)
  ·
    refine ⟨54870436221396394379309561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36580290814264262919539707 54870436221396394379309561)
    ·
      refine ⟨41152827166047295784482171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54870436221396394379309561 41152827166047295784482171)
      ·
        refine ⟨61729240749070943676723257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41152827166047295784482171 61729240749070943676723257)
        ·
          refine ⟨46296930561803207757542443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61729240749070943676723257 46296930561803207757542443)
          ·
            refine ⟨69445395842704811636313665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46296930561803207757542443 69445395842704811636313665)
            ·
              refine ⟨52084046882028608727235249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69445395842704811636313665 52084046882028608727235249)
              ·
                refine ⟨39063035161521456545426437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52084046882028608727235249 39063035161521456545426437)
                ·
                  refine ⟨7324319092785273102267457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39063035161521456545426437 7324319092785273102267457)
                  ·
                    refine ⟨5493239319588954826700593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324319092785273102267457 5493239319588954826700593)
                    ·
                      refine ⟨4119929489691716120025445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493239319588954826700593 4119929489691716120025445)
                      ·
                        rfl

theorem cell23_8023534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_8023534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023534 prefixEnd_8023534 := by exact prefixLift 8023534
  have htrace : WordTrace (prefixWord ++ tailWord_8023534) baseStart_8023534 baseEnd_8023534 := by
    simpa [prefixWord, tailWord_8023534, baseEnd_8023534] using wordTrace_append hprefix tailTrace_8023534
  have hstable : (prefixWord ++ tailWord_8023534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023534).length < 2 ^ (prefixWord ++ tailWord_8023534).sum := by decide
  have hdescent : baseEnd_8023534 < baseStart_8023534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023538 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_8023538 : Nat := 118140960795 + 8023538 * 2 ^ 59
def prefixEnd_8023538 : Nat := 4983230072969 + 3 ^ 40 * 8023538 * 2
def baseEnd_8023538 : Nat := 4119931543614334104375427

theorem tailTrace_8023538 : CollatzResearch.WordTrace tailWord_8023538 prefixEnd_8023538 4119931543614334104375427 := by
  unfold tailWord_8023538
  simp only [CollatzResearch.WordTrace]
  refine ⟨73160618101524903009865817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195094981604066408026308845 73160618101524903009865817)
  ·
    refine ⟨54870463576143677257399363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73160618101524903009865817 54870463576143677257399363)
    ·
      refine ⟨82305695364215515886099045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54870463576143677257399363 82305695364215515886099045)
      ·
        refine ⟨15432317880790409228643571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82305695364215515886099045 15432317880790409228643571)
        ·
          refine ⟨23148476821185613842965357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15432317880790409228643571 23148476821185613842965357)
          ·
            refine ⟨8680678807944605191112009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23148476821185613842965357 8680678807944605191112009)
            ·
              refine ⟨6510509105958453893334007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8680678807944605191112009 6510509105958453893334007)
              ·
                refine ⟨9765763658937680840001011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510509105958453893334007 9765763658937680840001011)
                ·
                  refine ⟨14648645488406521260001517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765763658937680840001011 14648645488406521260001517)
                  ·
                    refine ⟨5493242058152445472500569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14648645488406521260001517 5493242058152445472500569)
                    ·
                      refine ⟨4119931543614334104375427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493242058152445472500569 4119931543614334104375427)
                      ·
                        rfl

theorem cell23_8023538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_8023538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023538 prefixEnd_8023538 := by exact prefixLift 8023538
  have htrace : WordTrace (prefixWord ++ tailWord_8023538) baseStart_8023538 baseEnd_8023538 := by
    simpa [prefixWord, tailWord_8023538, baseEnd_8023538] using wordTrace_append hprefix tailTrace_8023538
  have hstable : (prefixWord ++ tailWord_8023538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023538).length < 2 ^ (prefixWord ++ tailWord_8023538).sum := by decide
  have hdescent : baseEnd_8023538 < baseStart_8023538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023607 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_8023607 : Nat := 118140960795 + 8023607 * 2 ^ 59
def prefixEnd_8023607 : Nat := 4983230072969 + 3 ^ 40 * 8023607 * 2
def baseEnd_8023607 : Nat := 4119966973779494334412609

theorem tailTrace_8023607 : CollatzResearch.WordTrace tailWord_8023607 prefixEnd_8023607 4119966973779494334412609 := by
  unfold tailWord_8023607
  simp only [CollatzResearch.WordTrace]
  refine ⟨292644989042849636823725075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195096659361899757882483383 292644989042849636823725075)
  ·
    refine ⟨438967483564274455235587613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292644989042849636823725075 438967483564274455235587613)
    ·
      refine ⟨164612806336602920713345355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438967483564274455235587613 164612806336602920713345355)
      ·
        refine ⟨246919209504904381070018033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164612806336602920713345355 246919209504904381070018033)
        ·
          refine ⟨185189407128678285802513525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246919209504904381070018033 185189407128678285802513525)
          ·
            refine ⟨17361506918313589293985643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185189407128678285802513525 17361506918313589293985643)
            ·
              refine ⟨26042260377470383940978465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17361506918313589293985643 26042260377470383940978465)
              ·
                refine ⟨19531695283102787955733849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26042260377470383940978465 19531695283102787955733849)
                ·
                  refine ⟨14648771462327090966800387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19531695283102787955733849 14648771462327090966800387)
                  ·
                    refine ⟨21973157193490636450200581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14648771462327090966800387 21973157193490636450200581)
                    ·
                      refine ⟨4119966973779494334412609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21973157193490636450200581 4119966973779494334412609)
                      ·
                        rfl

theorem cell23_8023607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_8023607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023607 prefixEnd_8023607 := by exact prefixLift 8023607
  have htrace : WordTrace (prefixWord ++ tailWord_8023607) baseStart_8023607 baseEnd_8023607 := by
    simpa [prefixWord, tailWord_8023607, baseEnd_8023607] using wordTrace_append hprefix tailTrace_8023607
  have hstable : (prefixWord ++ tailWord_8023607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023607).length < 2 ^ (prefixWord ++ tailWord_8023607).sum := by decide
  have hdescent : baseEnd_8023607 < baseStart_8023607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023638 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_8023638 : Nat := 118140960795 + 8023638 * 2 ^ 59
def prefixEnd_8023638 : Nat := 4983230072969 + 3 ^ 40 * 8023638 * 2
def baseEnd_8023638 : Nat := 1373327630559927904374989

theorem tailTrace_8023638 : CollatzResearch.WordTrace tailWord_8023638 prefixEnd_8023638 1373327630559927904374989 := by
  unfold tailWord_8023638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290382481608583069881473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195097413137158219412069045 18290382481608583069881473)
  ·
    refine ⟨13717786861206437302411105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18290382481608583069881473 13717786861206437302411105)
    ·
      refine ⟨10288340145904827976808329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13717786861206437302411105 10288340145904827976808329)
      ·
        refine ⟨7716255109428620982606247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10288340145904827976808329 7716255109428620982606247)
        ·
          refine ⟨11574382664142931473909371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716255109428620982606247 11574382664142931473909371)
          ·
            refine ⟨17361573996214397210864057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574382664142931473909371 17361573996214397210864057)
            ·
              refine ⟨13021180497160797908148043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17361573996214397210864057 13021180497160797908148043)
              ·
                refine ⟨19531770745741196862222065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13021180497160797908148043 19531770745741196862222065)
                ·
                  refine ⟨14648828059305897646666549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19531770745741196862222065 14648828059305897646666549)
                  ·
                    refine ⟨1373327630559927904374989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14648828059305897646666549 1373327630559927904374989)
                    ·
                      rfl

theorem cell23_8023638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_8023638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023638 prefixEnd_8023638 := by exact prefixLift 8023638
  have htrace : WordTrace (prefixWord ++ tailWord_8023638) baseStart_8023638 baseEnd_8023638 := by
    simpa [prefixWord, tailWord_8023638, baseEnd_8023638] using wordTrace_append hprefix tailTrace_8023638
  have hstable : (prefixWord ++ tailWord_8023638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023638).length < 2 ^ (prefixWord ++ tailWord_8023638).sum := by decide
  have hdescent : baseEnd_8023638 < baseStart_8023638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023644 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_8023644 : Nat := 118140960795 + 8023644 * 2 ^ 59
def prefixEnd_8023644 : Nat := 4983230072969 + 3 ^ 40 * 8023644 * 2
def baseEnd_8023644 : Nat := 4119985972563710689649939

theorem tailTrace_8023644 : CollatzResearch.WordTrace tailWord_8023644 prefixEnd_8023644 4119985972563710689649939 := by
  unfold tailWord_8023644
  simp only [CollatzResearch.WordTrace]
  refine ⟨146323169271857796071410993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195097559029143728095214657 146323169271857796071410993)
  ·
    refine ⟨109742376953893347053558245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146323169271857796071410993 109742376953893347053558245)
    ·
      refine ⟨20576695678855002572542171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109742376953893347053558245 20576695678855002572542171)
      ·
        refine ⟨30865043518282503858813257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20576695678855002572542171 30865043518282503858813257)
        ·
          refine ⟨23148782638711877894109943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30865043518282503858813257 23148782638711877894109943)
          ·
            refine ⟨34723173958067816841164915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23148782638711877894109943 34723173958067816841164915)
            ·
              refine ⟨52084760937101725261747373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34723173958067816841164915 52084760937101725261747373)
              ·
                refine ⟨19531785351413146973155265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52084760937101725261747373 19531785351413146973155265)
                ·
                  refine ⟨14648839013559860229866449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19531785351413146973155265 14648839013559860229866449)
                  ·
                    refine ⟨10986629260169895172399837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14648839013559860229866449 10986629260169895172399837)
                    ·
                      refine ⟨4119985972563710689649939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986629260169895172399837 4119985972563710689649939)
                      ·
                        rfl

theorem cell23_8023644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_8023644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023644 prefixEnd_8023644 := by exact prefixLift 8023644
  have htrace : WordTrace (prefixWord ++ tailWord_8023644) baseStart_8023644 baseEnd_8023644 := by
    simpa [prefixWord, tailWord_8023644, baseEnd_8023644] using wordTrace_append hprefix tailTrace_8023644
  have hstable : (prefixWord ++ tailWord_8023644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023644).length < 2 ^ (prefixWord ++ tailWord_8023644).sum := by decide
  have hdescent : baseEnd_8023644 < baseStart_8023644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023677 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_8023677 : Nat := 118140960795 + 8023677 * 2 ^ 59
def prefixEnd_8023677 : Nat := 4983230072969 + 3 ^ 40 * 8023677 * 2
def baseEnd_8023677 : Nat := 1373334305808436353512429

theorem tailTrace_8023677 : CollatzResearch.WordTrace tailWord_8023677 prefixEnd_8023677 1373334305808436353512429 := by
  unfold tailWord_8023677
  simp only [CollatzResearch.WordTrace]
  refine ⟨292647542152596038778773285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195098361435064025852515523 292647542152596038778773285)
  ·
    refine ⟨54871414153611757271019991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292647542152596038778773285 54871414153611757271019991)
    ·
      refine ⟨82307121230417635906529987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54871414153611757271019991 82307121230417635906529987)
      ·
        refine ⟨123460681845626453859794981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82307121230417635906529987 123460681845626453859794981)
        ·
          refine ⟨23148877846054960098711559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123460681845626453859794981 23148877846054960098711559)
          ·
            refine ⟨34723316769082440148067339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23148877846054960098711559 34723316769082440148067339)
            ·
              refine ⟨52084975153623660222101009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34723316769082440148067339 52084975153623660222101009)
              ·
                refine ⟨39063731365217745166575757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52084975153623660222101009 39063731365217745166575757)
                ·
                  refine ⟨14648899261956654437465909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39063731365217745166575757 14648899261956654437465909)
                  ·
                    refine ⟨1373334305808436353512429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14648899261956654437465909 1373334305808436353512429)
                    ·
                      rfl

theorem cell23_8023677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_8023677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023677 prefixEnd_8023677 := by exact prefixLift 8023677
  have htrace : WordTrace (prefixWord ++ tailWord_8023677) baseStart_8023677 baseEnd_8023677 := by
    simpa [prefixWord, tailWord_8023677, baseEnd_8023677] using wordTrace_append hprefix tailTrace_8023677
  have hstable : (prefixWord ++ tailWord_8023677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023677).length < 2 ^ (prefixWord ++ tailWord_8023677).sum := by decide
  have hdescent : baseEnd_8023677 < baseStart_8023677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023697 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 8, 2]
def baseStart_8023697 : Nat := 118140960795 + 8023697 * 2 ^ 59
def prefixEnd_8023697 : Nat := 4983230072969 + 3 ^ 40 * 8023697 * 2
def baseEnd_8023697 : Nat := 4120013187038398982287195

theorem tailTrace_8023697 : CollatzResearch.WordTrace tailWord_8023697 prefixEnd_8023697 4120013187038398982287195 := by
  unfold tailWord_8023697
  simp only [CollatzResearch.WordTrace]
  refine ⟨292648271612523582194501345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195098847741682388129667563 292648271612523582194501345)
  ·
    refine ⟨219486203709392686645876009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292648271612523582194501345 219486203709392686645876009)
    ·
      refine ⟨164614652782044514984407007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219486203709392686645876009 164614652782044514984407007)
      ·
        refine ⟨246921979173066772476610511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164614652782044514984407007 246921979173066772476610511)
        ·
          refine ⟨370382968759600158714915767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246921979173066772476610511 370382968759600158714915767)
          ·
            refine ⟨555574453139400238072373651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370382968759600158714915767 555574453139400238072373651)
            ·
              refine ⟨833361679709100357108560477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555574453139400238072373651 833361679709100357108560477)
              ·
                refine ⟨312510629890912633915710179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833361679709100357108560477 312510629890912633915710179)
                ·
                  refine ⟨468765944836368950873565269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312510629890912633915710179 468765944836368950873565269)
                  ·
                    refine ⟨5493350916051198643049593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 468765944836368950873565269 5493350916051198643049593)
                    ·
                      refine ⟨4120013187038398982287195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493350916051198643049593 4120013187038398982287195)
                      ·
                        rfl

theorem cell23_8023697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_8023697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023697 prefixEnd_8023697 := by exact prefixLift 8023697
  have htrace : WordTrace (prefixWord ++ tailWord_8023697) baseStart_8023697 baseEnd_8023697 := by
    simpa [prefixWord, tailWord_8023697, baseEnd_8023697] using wordTrace_append hprefix tailTrace_8023697
  have hstable : (prefixWord ++ tailWord_8023697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023697).length < 2 ^ (prefixWord ++ tailWord_8023697).sum := by decide
  have hdescent : baseEnd_8023697 < baseStart_8023697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023711 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 1, 5]
def baseStart_8023711 : Nat := 118140960795 + 8023711 * 2 ^ 59
def prefixEnd_8023711 : Nat := 4983230072969 + 3 ^ 40 * 8023711 * 2
def baseEnd_8023711 : Nat := 1373340125255853975837377

theorem tailTrace_8023711 : CollatzResearch.WordTrace tailWord_8023711 prefixEnd_8023711 1373340125255853975837377 := by
  unfold tailWord_8023711
  simp only [CollatzResearch.WordTrace]
  refine ⟨292648782234472862585510987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195099188156315241723673991 292648782234472862585510987)
  ·
    refine ⟨438973173351709293878266481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292648782234472862585510987 438973173351709293878266481)
    ·
      refine ⟨329229880013781970408699861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438973173351709293878266481 329229880013781970408699861)
      ·
        refine ⟨7716325312823014931453903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 329229880013781970408699861 7716325312823014931453903)
        ·
          refine ⟨11574487969234522397180855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716325312823014931453903 11574487969234522397180855)
          ·
            refine ⟨17361731953851783595771283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574487969234522397180855 17361731953851783595771283)
            ·
              refine ⟨26042597930777675393656925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17361731953851783595771283 26042597930777675393656925)
              ·
                refine ⟨9765974224041628272621347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26042597930777675393656925 9765974224041628272621347)
                ·
                  refine ⟨14648961336062442408932021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765974224041628272621347 14648961336062442408932021)
                  ·
                    refine ⟨1373340125255853975837377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14648961336062442408932021 1373340125255853975837377)
                    ·
                      rfl

theorem cell23_8023711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_8023711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023711 prefixEnd_8023711 := by exact prefixLift 8023711
  have htrace : WordTrace (prefixWord ++ tailWord_8023711) baseStart_8023711 baseEnd_8023711 := by
    simpa [prefixWord, tailWord_8023711, baseEnd_8023711] using wordTrace_append hprefix tailTrace_8023711
  have hstable : (prefixWord ++ tailWord_8023711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023711).length < 2 ^ (prefixWord ++ tailWord_8023711).sum := by decide
  have hdescent : baseEnd_8023711 < baseStart_8023711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023731 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 3, 2, 2]
def baseStart_8023731 : Nat := 118140960795 + 8023731 * 2 ^ 59
def prefixEnd_8023731 : Nat := 4983230072969 + 3 ^ 40 * 8023731 * 2
def baseEnd_8023731 : Nat := 4120030645380651849262039

theorem tailTrace_8023731 : CollatzResearch.WordTrace tailWord_8023731 prefixEnd_8023731 4120030645380651849262039 := by
  unfold tailWord_8023731
  simp only [CollatzResearch.WordTrace]
  refine ⟨292649511694400406001239047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195099674462933604000826031 292649511694400406001239047)
  ·
    refine ⟨438974267541600609001858571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292649511694400406001239047 438974267541600609001858571)
    ·
      refine ⟨658461401312400913502787857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438974267541600609001858571 658461401312400913502787857)
      ·
        refine ⟨493846050984300685127090893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658461401312400913502787857 493846050984300685127090893)
        ·
          refine ⟨185192269119112756922659085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493846050984300685127090893 185192269119112756922659085)
          ·
            refine ⟨69447100919667283845997157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185192269119112756922659085 69447100919667283845997157)
            ·
              refine ⟨13021331422437615721124467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69447100919667283845997157 13021331422437615721124467)
              ·
                refine ⟨19531997133656423581686701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13021331422437615721124467 19531997133656423581686701)
                ·
                  refine ⟨7324498925121158843132513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19531997133656423581686701 7324498925121158843132513)
                  ·
                    refine ⟨5493374193840869132349385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324498925121158843132513 5493374193840869132349385)
                    ·
                      refine ⟨4120030645380651849262039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493374193840869132349385 4120030645380651849262039)
                      ·
                        rfl

theorem cell23_8023731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 2, 2].length) (baseStart_8023731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023731 prefixEnd_8023731 := by exact prefixLift 8023731
  have htrace : WordTrace (prefixWord ++ tailWord_8023731) baseStart_8023731 baseEnd_8023731 := by
    simpa [prefixWord, tailWord_8023731, baseEnd_8023731] using wordTrace_append hprefix tailTrace_8023731
  have hstable : (prefixWord ++ tailWord_8023731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023731).length < 2 ^ (prefixWord ++ tailWord_8023731).sum := by decide
  have hdescent : baseEnd_8023731 < baseStart_8023731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023741 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_8023741 : Nat := 118140960795 + 8023741 * 2 ^ 59
def prefixEnd_8023741 : Nat := 4983230072969 + 3 ^ 40 * 8023741 * 2
def baseEnd_8023741 : Nat := 1373345260062398936712331

theorem tailTrace_8023741 : CollatzResearch.WordTrace tailWord_8023741 prefixEnd_8023741 1373345260062398936712331 := by
  unfold tailWord_8023741
  simp only [CollatzResearch.WordTrace]
  refine ⟨292649876424364177709103077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195099917616242785139402051 292649876424364177709103077)
  ·
    refine ⟨54871851829568283320456827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292649876424364177709103077 54871851829568283320456827)
    ·
      refine ⟨82307777744352424980685241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54871851829568283320456827 82307777744352424980685241)
      ·
        refine ⟨61730833308264318735513931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82307777744352424980685241 61730833308264318735513931)
        ·
          refine ⟨92596249962396478103270897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61730833308264318735513931 92596249962396478103270897)
          ·
            refine ⟨69447187471797358577453173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92596249962396478103270897 69447187471797358577453173)
            ·
              refine ⟨6510673825481002366636235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69447187471797358577453173 6510673825481002366636235)
              ·
                refine ⟨9766010738221503549954353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510673825481002366636235 9766010738221503549954353)
                ·
                  refine ⟨7324508053666127662465765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766010738221503549954353 7324508053666127662465765)
                  ·
                    refine ⟨1373345260062398936712331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324508053666127662465765 1373345260062398936712331)
                    ·
                      rfl

theorem cell23_8023741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_8023741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023741 prefixEnd_8023741 := by exact prefixLift 8023741
  have htrace : WordTrace (prefixWord ++ tailWord_8023741) baseStart_8023741 baseEnd_8023741 := by
    simpa [prefixWord, tailWord_8023741, baseEnd_8023741] using wordTrace_append hprefix tailTrace_8023741
  have hstable : (prefixWord ++ tailWord_8023741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023741).length < 2 ^ (prefixWord ++ tailWord_8023741).sum := by decide
  have hdescent : baseEnd_8023741 < baseStart_8023741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023781 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_8023781 : Nat := 118140960795 + 8023781 * 2 ^ 59
def prefixEnd_8023781 : Nat := 4983230072969 + 3 ^ 40 * 8023781 * 2
def baseEnd_8023781 : Nat := 4120056319413376653636809

theorem tailTrace_8023781 : CollatzResearch.WordTrace tailWord_8023781 prefixEnd_8023781 4120056319413376653636809 := by
  unfold tailWord_8023781
  simp only [CollatzResearch.WordTrace]
  refine ⟨292651335344219264540559197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195100890229479509693706131 292651335344219264540559197)
  ·
    refine ⟨109744250754082224202709699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292651335344219264540559197 109744250754082224202709699)
    ·
      refine ⟨164616376131123336304064549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109744250754082224202709699 164616376131123336304064549)
      ·
        refine ⟨30865570524585625557012103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164616376131123336304064549 30865570524585625557012103)
        ·
          refine ⟨46298355786878438335518155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30865570524585625557012103 46298355786878438335518155)
          ·
            refine ⟨69447533680317657503277233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46298355786878438335518155 69447533680317657503277233)
            ·
              refine ⟨52085650260238243127457925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69447533680317657503277233 52085650260238243127457925)
              ·
                refine ⟨9766059423794670586398361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52085650260238243127457925 9766059423794670586398361)
                ·
                  refine ⟨7324544567846002939798771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766059423794670586398361 7324544567846002939798771)
                  ·
                    refine ⟨10986816851769004409698157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7324544567846002939798771 10986816851769004409698157)
                    ·
                      refine ⟨4120056319413376653636809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986816851769004409698157 4120056319413376653636809)
                      ·
                        rfl

theorem cell23_8023781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_8023781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023781 prefixEnd_8023781 := by exact prefixLift 8023781
  have htrace : WordTrace (prefixWord ++ tailWord_8023781) baseStart_8023781 baseEnd_8023781 := by
    simpa [prefixWord, tailWord_8023781, baseEnd_8023781] using wordTrace_append hprefix tailTrace_8023781
  have hstable : (prefixWord ++ tailWord_8023781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023781).length < 2 ^ (prefixWord ++ tailWord_8023781).sum := by decide
  have hdescent : baseEnd_8023781 < baseStart_8023781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023798 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_8023798 : Nat := 118140960795 + 8023798 * 2 ^ 59
def prefixEnd_8023798 : Nat := 4983230072969 + 3 ^ 40 * 8023798 * 2
def baseEnd_8023798 : Nat := 4120065048584503087124231

theorem tailTrace_8023798 : CollatzResearch.WordTrace tailWord_8023798 prefixEnd_8023798 4120065048584503087124231 := by
  unfold tailWord_8023798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290747211572354777745503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195101303590105117629285365 18290747211572354777745503)
  ·
    refine ⟨27436120817358532166618255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18290747211572354777745503 27436120817358532166618255)
    ·
      refine ⟨41154181226037798249927383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27436120817358532166618255 41154181226037798249927383)
      ·
        refine ⟨61731271839056697374891075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41154181226037798249927383 61731271839056697374891075)
        ·
          refine ⟨92596907758585046062336613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61731271839056697374891075 92596907758585046062336613)
          ·
            refine ⟨17361920204734696136688115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92596907758585046062336613 17361920204734696136688115)
            ·
              refine ⟨26042880307102044205032173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17361920204734696136688115 26042880307102044205032173)
              ·
                refine ⟨9766080115163266576887065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26042880307102044205032173 9766080115163266576887065)
                ·
                  refine ⟨7324560086372449932665299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766080115163266576887065 7324560086372449932665299)
                  ·
                    refine ⟨10986840129558674898997949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7324560086372449932665299 10986840129558674898997949)
                    ·
                      refine ⟨4120065048584503087124231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10986840129558674898997949 4120065048584503087124231)
                      ·
                        rfl

theorem cell23_8023798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_8023798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023798 prefixEnd_8023798 := by exact prefixLift 8023798
  have htrace : WordTrace (prefixWord ++ tailWord_8023798) baseStart_8023798 baseEnd_8023798 := by
    simpa [prefixWord, tailWord_8023798, baseEnd_8023798] using wordTrace_append hprefix tailTrace_8023798
  have hstable : (prefixWord ++ tailWord_8023798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023798).length < 2 ^ (prefixWord ++ tailWord_8023798).sum := by decide
  have hdescent : baseEnd_8023798 < baseStart_8023798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023807 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_8023807 : Nat := 118140960795 + 8023807 * 2 ^ 59
def prefixEnd_8023807 : Nat := 4983230072969 + 3 ^ 40 * 8023807 * 2
def baseEnd_8023807 : Nat := 4120069669910393551911689

theorem tailTrace_8023807 : CollatzResearch.WordTrace tailWord_8023807 prefixEnd_8023807 4120069669910393551911689 := by
  unfold tailWord_8023807
  simp only [CollatzResearch.WordTrace]
  refine ⟨292652283642125070981005675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195101522428083380654003783 292652283642125070981005675)
  ·
    refine ⟨438978425463187606471508513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292652283642125070981005675 438978425463187606471508513)
    ·
      refine ⟨329233819097390704853631385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438978425463187606471508513 329233819097390704853631385)
      ·
        refine ⟨246925364323043028640223539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329233819097390704853631385 246925364323043028640223539)
        ·
          refine ⟨370388046484564542960335309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246925364323043028640223539 370388046484564542960335309)
          ·
            refine ⟨138895517431711703610125741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370388046484564542960335309 138895517431711703610125741)
            ·
              refine ⟨52085819036891888853797153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138895517431711703610125741 52085819036891888853797153)
              ·
                refine ⟨39064364277668916640347865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52085819036891888853797153 39064364277668916640347865)
                ·
                  refine ⟨29298273208251687480260899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39064364277668916640347865 29298273208251687480260899)
                  ·
                    refine ⟨43947409812377531220391349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29298273208251687480260899 43947409812377531220391349)
                    ·
                      refine ⟨4120069669910393551911689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43947409812377531220391349 4120069669910393551911689)
                      ·
                        rfl

theorem cell23_8023807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_8023807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023807 prefixEnd_8023807 := by exact prefixLift 8023807
  have htrace : WordTrace (prefixWord ++ tailWord_8023807) baseStart_8023807 baseEnd_8023807 := by
    simpa [prefixWord, tailWord_8023807, baseEnd_8023807] using wordTrace_append hprefix tailTrace_8023807
  have hstable : (prefixWord ++ tailWord_8023807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023807).length < 2 ^ (prefixWord ++ tailWord_8023807).sum := by decide
  have hdescent : baseEnd_8023807 < baseStart_8023807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023817 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_8023817 : Nat := 118140960795 + 8023817 * 2 ^ 59
def prefixEnd_8023817 : Nat := 4983230072969 + 3 ^ 40 * 8023817 * 2
def baseEnd_8023817 : Nat := 4120074804716938512786643

theorem tailTrace_8023817 : CollatzResearch.WordTrace tailWord_8023817 prefixEnd_8023817 4120074804716938512786643 := by
  unfold tailWord_8023817
  simp only [CollatzResearch.WordTrace]
  refine ⟨292652648372088842688869705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195101765581392561792579803 292652648372088842688869705)
  ·
    refine ⟨219489486279066632016652279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292652648372088842688869705 219489486279066632016652279)
    ·
      refine ⟨329234229418599948024978419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219489486279066632016652279 329234229418599948024978419)
      ·
        refine ⟨493851344127899922037467629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329234229418599948024978419 493851344127899922037467629)
        ·
          refine ⟨185194254047962470764050361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493851344127899922037467629 185194254047962470764050361)
          ·
            refine ⟨138895690535971853073037771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185194254047962470764050361 138895690535971853073037771)
            ·
              refine ⟨208343535803957779609556657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138895690535971853073037771 208343535803957779609556657)
              ·
                refine ⟨156257651852968334707167493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208343535803957779609556657 156257651852968334707167493)
                ·
                  refine ⟨29298309722431562757593905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156257651852968334707167493 29298309722431562757593905)
                  ·
                    refine ⟨21973732291823672068195429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29298309722431562757593905 21973732291823672068195429)
                    ·
                      refine ⟨4120074804716938512786643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21973732291823672068195429 4120074804716938512786643)
                      ·
                        rfl

theorem cell23_8023817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_8023817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023817 prefixEnd_8023817 := by exact prefixLift 8023817
  have htrace : WordTrace (prefixWord ++ tailWord_8023817) baseStart_8023817 baseEnd_8023817 := by
    simpa [prefixWord, tailWord_8023817, baseEnd_8023817] using wordTrace_append hprefix tailTrace_8023817
  have hstable : (prefixWord ++ tailWord_8023817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023817).length < 2 ^ (prefixWord ++ tailWord_8023817).sum := by decide
  have hdescent : baseEnd_8023817 < baseStart_8023817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023911 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_8023911 : Nat := 118140960795 + 8023911 * 2 ^ 59
def prefixEnd_8023911 : Nat := 4983230072969 + 3 ^ 40 * 8023911 * 2
def baseEnd_8023911 : Nat := 4120123071898461145011211

theorem tailTrace_8023911 : CollatzResearch.WordTrace tailWord_8023911 prefixEnd_8023911 4120123071898461145011211 := by
  unfold tailWord_8023911
  simp only [CollatzResearch.WordTrace]
  refine ⟨292656076833748296742791587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195104051222498864495194391 292656076833748296742791587)
  ·
    refine ⟨438984115250622445114187381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292656076833748296742791587 438984115250622445114187381)
    ·
      refine ⟨41154760804745854229455067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438984115250622445114187381 41154760804745854229455067)
      ·
        refine ⟨61732141207118781344182601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41154760804745854229455067 61732141207118781344182601)
        ·
          refine ⟨46299105905339086008136951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61732141207118781344182601 46299105905339086008136951)
          ·
            refine ⟨69448658858008629012205427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46299105905339086008136951 69448658858008629012205427)
            ·
              refine ⟨104172988287012943518308141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69448658858008629012205427 104172988287012943518308141)
              ·
                refine ⟨39064870607629853819365553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104172988287012943518308141 39064870607629853819365553)
                ·
                  refine ⟨29298652955722390364524165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39064870607629853819365553 29298652955722390364524165)
                  ·
                    refine ⟨5493497429197948193348281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29298652955722390364524165 5493497429197948193348281)
                    ·
                      refine ⟨4120123071898461145011211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493497429197948193348281 4120123071898461145011211)
                      ·
                        rfl

theorem cell23_8023911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_8023911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023911 prefixEnd_8023911 := by exact prefixLift 8023911
  have htrace : WordTrace (prefixWord ++ tailWord_8023911) baseStart_8023911 baseEnd_8023911 := by
    simpa [prefixWord, tailWord_8023911, baseEnd_8023911] using wordTrace_append hprefix tailTrace_8023911
  have hstable : (prefixWord ++ tailWord_8023911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023911).length < 2 ^ (prefixWord ++ tailWord_8023911).sum := by decide
  have hdescent : baseEnd_8023911 < baseStart_8023911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023927 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_8023927 : Nat := 118140960795 + 8023927 * 2 ^ 59
def prefixEnd_8023927 : Nat := 4983230072969 + 3 ^ 40 * 8023927 * 2
def baseEnd_8023927 : Nat := 4120131287588933082411137

theorem tailTrace_8023927 : CollatzResearch.WordTrace tailWord_8023927 prefixEnd_8023927 4120131287588933082411137 := by
  unfold tailWord_8023927
  simp only [CollatzResearch.WordTrace]
  refine ⟨292656660401690331475374035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195104440267793554316916023 292656660401690331475374035)
  ·
    refine ⟨438984990602535497213061053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292656660401690331475374035 438984990602535497213061053)
    ·
      refine ⟨164619371475950811454897895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438984990602535497213061053 164619371475950811454897895)
      ·
        refine ⟨246929057213926217182346843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164619371475950811454897895 246929057213926217182346843)
        ·
          refine ⟨370393585820889325773520265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246929057213926217182346843 370393585820889325773520265)
          ·
            refine ⟨277795189365666994330140199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370393585820889325773520265 277795189365666994330140199)
            ·
              refine ⟨416692784048500491495210299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277795189365666994330140199 416692784048500491495210299)
              ·
                refine ⟨625039176072750737242815449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416692784048500491495210299 625039176072750737242815449)
                ·
                  refine ⟨468779382054563052932111587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625039176072750737242815449 468779382054563052932111587)
                  ·
                    refine ⟨703169073081844579398167381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 468779382054563052932111587 703169073081844579398167381)
                    ·
                      refine ⟨4120131287588933082411137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 703169073081844579398167381 4120131287588933082411137)
                      ·
                        rfl

theorem cell23_8023927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_8023927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023927 prefixEnd_8023927 := by exact prefixLift 8023927
  have htrace : WordTrace (prefixWord ++ tailWord_8023927) baseStart_8023927 baseEnd_8023927 := by
    simpa [prefixWord, tailWord_8023927, baseEnd_8023927] using wordTrace_append hprefix tailTrace_8023927
  have hstable : (prefixWord ++ tailWord_8023927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023927).length < 2 ^ (prefixWord ++ tailWord_8023927).sum := by decide
  have hdescent : baseEnd_8023927 < baseStart_8023927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8023971 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 6, 3, 2]
def baseStart_8023971 : Nat := 118140960795 + 8023971 * 2 ^ 59
def prefixEnd_8023971 : Nat := 4983230072969 + 3 ^ 40 * 8023971 * 2
def baseEnd_8023971 : Nat := 4120153880737730910260935

theorem tailTrace_8023971 : CollatzResearch.WordTrace tailWord_8023971 prefixEnd_8023971 4120153880737730910260935 := by
  unfold tailWord_8023971
  simp only [CollatzResearch.WordTrace]
  refine ⟨292658265213530926989975767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195105510142353951326650511 292658265213530926989975767)
  ·
    refine ⟨438987397820296390484963651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292658265213530926989975767 438987397820296390484963651)
    ·
      refine ⟨658481096730444585727445477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438987397820296390484963651 658481096730444585727445477)
      ·
        refine ⟨123465205636958359823896027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 658481096730444585727445477 123465205636958359823896027)
        ·
          refine ⟨185197808455437539735844041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123465205636958359823896027 185197808455437539735844041)
          ·
            refine ⟨138898356341578154801883031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185197808455437539735844041 138898356341578154801883031)
            ·
              refine ⟨208347534512367232202824547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138898356341578154801883031 208347534512367232202824547)
              ·
                refine ⟨312521301768550848304236821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208347534512367232202824547 312521301768550848304236821)
                ·
                  refine ⟨14649436020400821014261101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312521301768550848304236821 14649436020400821014261101)
                  ·
                    refine ⟨5493538507650307880347913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14649436020400821014261101 5493538507650307880347913)
                    ·
                      refine ⟨4120153880737730910260935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493538507650307880347913 4120153880737730910260935)
                      ·
                        rfl

theorem cell23_8023971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_8023971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8023971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8023971 prefixEnd_8023971 := by exact prefixLift 8023971
  have htrace : WordTrace (prefixWord ++ tailWord_8023971) baseStart_8023971 baseEnd_8023971 := by
    simpa [prefixWord, tailWord_8023971, baseEnd_8023971] using wordTrace_append hprefix tailTrace_8023971
  have hstable : (prefixWord ++ tailWord_8023971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8023971).length < 2 ^ (prefixWord ++ tailWord_8023971).sum := by decide
  have hdescent : baseEnd_8023971 < baseStart_8023971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8023971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024012 : List Nat := [2, 2, 1, 4, 1, 2, 4, 2, 1, 1, 3]
def baseStart_8024012 : Nat := 118140960795 + 8024012 * 2 ^ 59
def prefixEnd_8024012 : Nat := 4983230072969 + 3 ^ 40 * 8024012 * 2
def baseEnd_8024012 : Nat := 4120174933444565249848247

theorem tailTrace_8024012 : CollatzResearch.WordTrace tailWord_8024012 prefixEnd_8024012 4120174933444565249848247 := by
  unfold tailWord_8024012
  simp only [CollatzResearch.WordTrace]
  refine ⟨146329880303191195496109145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195106507070921593994812193 146329880303191195496109145)
  ·
    refine ⟨109747410227393396622081859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146329880303191195496109145 109747410227393396622081859)
    ·
      refine ⟨164621115341090094933122789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109747410227393396622081859 164621115341090094933122789)
      ·
        refine ⟨30866459126454392799960523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164621115341090094933122789 30866459126454392799960523)
        ·
          refine ⟨46299688689681589199940785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30866459126454392799960523 46299688689681589199940785)
          ·
            refine ⟨34724766517261191899955589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46299688689681589199940785 34724766517261191899955589)
            ·
              refine ⟨6510893721986473481241673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34724766517261191899955589 6510893721986473481241673)
              ·
                refine ⟨4883170291489855110931255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6510893721986473481241673 4883170291489855110931255)
                ·
                  refine ⟨7324755437234782666396883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883170291489855110931255 7324755437234782666396883)
                  ·
                    refine ⟨10987133155852173999595325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7324755437234782666396883 10987133155852173999595325)
                    ·
                      refine ⟨4120174933444565249848247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987133155852173999595325 4120174933444565249848247)
                      ·
                        rfl

theorem cell23_8024012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_8024012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024012 prefixEnd_8024012 := by exact prefixLift 8024012
  have htrace : WordTrace (prefixWord ++ tailWord_8024012) baseStart_8024012 baseEnd_8024012 := by
    simpa [prefixWord, tailWord_8024012, baseEnd_8024012] using wordTrace_append hprefix tailTrace_8024012
  have hstable : (prefixWord ++ tailWord_8024012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024012).length < 2 ^ (prefixWord ++ tailWord_8024012).sum := by decide
  have hdescent : baseEnd_8024012 < baseStart_8024012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024031 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_8024031 : Nat := 118140960795 + 8024031 * 2 ^ 59
def prefixEnd_8024031 : Nat := 4983230072969 + 3 ^ 40 * 8024031 * 2
def baseEnd_8024031 : Nat := 4120184689577000675510659

theorem tailTrace_8024031 : CollatzResearch.WordTrace tailWord_8024031 prefixEnd_8024031 4120184689577000675510659 := by
  unfold tailWord_8024031
  simp only [CollatzResearch.WordTrace]
  refine ⟨292660453593313557237159947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195106969062209038158106631 292660453593313557237159947)
  ·
    refine ⟨438990680389970335855739921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292660453593313557237159947 438990680389970335855739921)
    ·
      refine ⟨329243010292477751891804941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438990680389970335855739921 329243010292477751891804941)
      ·
        refine ⟨123466128859679156959426853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329243010292477751891804941 123466128859679156959426853)
        ·
          refine ⟨23149899161189841929892535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123466128859679156959426853 23149899161189841929892535)
          ·
            refine ⟨34724848741784762894838803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23149899161189841929892535 34724848741784762894838803)
            ·
              refine ⟨52087273112677144342258205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34724848741784762894838803 52087273112677144342258205)
              ·
                refine ⟨19532727417253929128346827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52087273112677144342258205 19532727417253929128346827)
                ·
                  refine ⟨29299091125880893692520241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19532727417253929128346827 29299091125880893692520241)
                  ·
                    refine ⟨21974318344410670269390181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29299091125880893692520241 21974318344410670269390181)
                    ·
                      refine ⟨4120184689577000675510659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21974318344410670269390181 4120184689577000675510659)
                      ·
                        rfl

theorem cell23_8024031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_8024031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024031 prefixEnd_8024031 := by exact prefixLift 8024031
  have htrace : WordTrace (prefixWord ++ tailWord_8024031) baseStart_8024031 baseEnd_8024031 := by
    simpa [prefixWord, tailWord_8024031, baseEnd_8024031] using wordTrace_append hprefix tailTrace_8024031
  have hstable : (prefixWord ++ tailWord_8024031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024031).length < 2 ^ (prefixWord ++ tailWord_8024031).sum := by decide
  have hdescent : baseEnd_8024031 < baseStart_8024031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024035 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 3, 2, 2]
def baseStart_8024035 : Nat := 118140960795 + 8024035 * 2 ^ 59
def prefixEnd_8024035 : Nat := 4983230072969 + 3 ^ 40 * 8024035 * 2
def baseEnd_8024035 : Nat := 4120186743499618659860641

theorem tailTrace_8024035 : CollatzResearch.WordTrace tailWord_8024035 prefixEnd_8024035 4120186743499618659860641 := by
  unfold tailWord_8024035
  simp only [CollatzResearch.WordTrace]
  refine ⟨292660599485299065920305559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195107066323532710613537039 292660599485299065920305559)
  ·
    refine ⟨438990899227948598880458339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292660599485299065920305559 438990899227948598880458339)
    ·
      refine ⟨658486348841922898320687509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438990899227948598880458339 658486348841922898320687509)
      ·
        refine ⟨30866547601965135858782227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 658486348841922898320687509 30866547601965135858782227)
        ·
          refine ⟨46299821402947703788173341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30866547601965135858782227 46299821402947703788173341)
          ·
            refine ⟨17362433026105388920565003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46299821402947703788173341 17362433026105388920565003)
            ·
              refine ⟨26043649539158083380847505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17362433026105388920565003 26043649539158083380847505)
              ·
                refine ⟨19532737154368562535635629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26043649539158083380847505 19532737154368562535635629)
                ·
                  refine ⟨7324776432888210950863361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19532737154368562535635629 7324776432888210950863361)
                  ·
                    refine ⟨5493582324666158213147521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324776432888210950863361 5493582324666158213147521)
                    ·
                      refine ⟨4120186743499618659860641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493582324666158213147521 4120186743499618659860641)
                      ·
                        rfl

theorem cell23_8024035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_8024035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024035 prefixEnd_8024035 := by exact prefixLift 8024035
  have htrace : WordTrace (prefixWord ++ tailWord_8024035) baseStart_8024035 baseEnd_8024035 := by
    simpa [prefixWord, tailWord_8024035, baseEnd_8024035] using wordTrace_append hprefix tailTrace_8024035
  have hstable : (prefixWord ++ tailWord_8024035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024035).length < 2 ^ (prefixWord ++ tailWord_8024035).sum := by decide
  have hdescent : baseEnd_8024035 < baseStart_8024035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024062 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_8024062 : Nat := 118140960795 + 8024062 * 2 ^ 59
def prefixEnd_8024062 : Nat := 4983230072969 + 3 ^ 40 * 8024062 * 2
def baseEnd_8024062 : Nat := 1373400202492430018074339

theorem tailTrace_8024062 : CollatzResearch.WordTrace tailWord_8024062 prefixEnd_8024062 1373400202492430018074339 := by
  unfold tailWord_8024062
  simp only [CollatzResearch.WordTrace]
  refine ⟨36582698032025156191442305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195107722837467499687692293 36582698032025156191442305)
  ·
    refine ⟨27437023524018867143581729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36582698032025156191442305 27437023524018867143581729)
    ·
      refine ⟨20577767643014150357686297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27437023524018867143581729 20577767643014150357686297)
      ·
        refine ⟨15433325732260612768264723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20577767643014150357686297 15433325732260612768264723)
        ·
          refine ⟨23149988598390919152397085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15433325732260612768264723 23149988598390919152397085)
          ·
            refine ⟨8681245724396594682148907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23149988598390919152397085 8681245724396594682148907)
            ·
              refine ⟨13021868586594892023223361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681245724396594682148907 13021868586594892023223361)
              ·
                refine ⟨9766401439946169017417521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13021868586594892023223361 9766401439946169017417521)
                ·
                  refine ⟨7324801079959626763063141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766401439946169017417521 7324801079959626763063141)
                  ·
                    refine ⟨1373400202492430018074339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324801079959626763063141 1373400202492430018074339)
                    ·
                      rfl

theorem cell23_8024062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_8024062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024062 prefixEnd_8024062 := by exact prefixLift 8024062
  have htrace : WordTrace (prefixWord ++ tailWord_8024062) baseStart_8024062 baseEnd_8024062 := by
    simpa [prefixWord, tailWord_8024062, baseEnd_8024062] using wordTrace_append hprefix tailTrace_8024062
  have hstable : (prefixWord ++ tailWord_8024062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024062).length < 2 ^ (prefixWord ++ tailWord_8024062).sum := by decide
  have hdescent : baseEnd_8024062 < baseStart_8024062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024064 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_8024064 : Nat := 118140960795 + 8024064 * 2 ^ 59
def prefixEnd_8024064 : Nat := 4983230072969 + 3 ^ 40 * 8024064 * 2
def baseEnd_8024064 : Nat := 4120201634438599046398007

theorem tailTrace_8024064 : CollatzResearch.WordTrace tailWord_8024064 prefixEnd_8024064 4120201634438599046398007 := by
  unfold tailWord_8024064
  simp only [CollatzResearch.WordTrace]
  refine ⟨146330828601097001936555623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195107771468129335915407497 146330828601097001936555623)
  ·
    refine ⟨219496242901645502904833435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146330828601097001936555623 219496242901645502904833435)
    ·
      refine ⟨329244364352468254357250153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219496242901645502904833435 329244364352468254357250153)
      ·
        refine ⟨246933273264351190767937615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329244364352468254357250153 246933273264351190767937615)
        ·
          refine ⟨370399909896526786151906423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246933273264351190767937615 370399909896526786151906423)
          ·
            refine ⟨555599864844790179227859635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370399909896526786151906423 555599864844790179227859635)
            ·
              refine ⟨833399797267185268841789453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555599864844790179227859635 833399797267185268841789453)
              ·
                refine ⟨312524923975194475815671045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 833399797267185268841789453 312524923975194475815671045)
                ·
                  refine ⟨58598423245348964215438321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312524923975194475815671045 58598423245348964215438321)
                  ·
                    refine ⟨43948817434011723161578741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58598423245348964215438321 43948817434011723161578741)
                    ·
                      refine ⟨4120201634438599046398007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43948817434011723161578741 4120201634438599046398007)
                      ·
                        rfl

theorem cell23_8024064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_8024064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024064 prefixEnd_8024064 := by exact prefixLift 8024064
  have htrace : WordTrace (prefixWord ++ tailWord_8024064) baseStart_8024064 baseEnd_8024064 := by
    simpa [prefixWord, tailWord_8024064, baseEnd_8024064] using wordTrace_append hprefix tailTrace_8024064
  have hstable : (prefixWord ++ tailWord_8024064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024064).length < 2 ^ (prefixWord ++ tailWord_8024064).sum := by decide
  have hdescent : baseEnd_8024064 < baseStart_8024064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024085 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_8024085 : Nat := 118140960795 + 8024085 * 2 ^ 59
def prefixEnd_8024085 : Nat := 4983230072969 + 3 ^ 40 * 8024085 * 2
def baseEnd_8024085 : Nat := 4120212417532343464235411

theorem tailTrace_8024085 : CollatzResearch.WordTrace tailWord_8024085 prefixEnd_8024085 4120212417532343464235411 := by
  unfold tailWord_8024085
  simp only [CollatzResearch.WordTrace]
  refine ⟨292662423135117924459625709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195108282090078616306417139 292662423135117924459625709)
  ·
    refine ⟨109748408675669221672359641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292662423135117924459625709 109748408675669221672359641)
    ·
      refine ⟨82311306506751916254269731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109748408675669221672359641 82311306506751916254269731)
      ·
        refine ⟨123466959760127874381404597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82311306506751916254269731 123466959760127874381404597)
        ·
          refine ⟨11575027477511988223256681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123466959760127874381404597 11575027477511988223256681)
          ·
            refine ⟨8681270608133991167442511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11575027477511988223256681 8681270608133991167442511)
            ·
              refine ⟨13021905912200986751163767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681270608133991167442511 13021905912200986751163767)
              ·
                refine ⟨19532858868301480126745651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13021905912200986751163767 19532858868301480126745651)
                ·
                  refine ⟨29299288302452220190118477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19532858868301480126745651 29299288302452220190118477)
                  ·
                    refine ⟨10987233113419582571294429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29299288302452220190118477 10987233113419582571294429)
                    ·
                      refine ⟨4120212417532343464235411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987233113419582571294429 4120212417532343464235411)
                      ·
                        rfl

theorem cell23_8024085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_8024085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024085 prefixEnd_8024085 := by exact prefixLift 8024085
  have htrace : WordTrace (prefixWord ++ tailWord_8024085) baseStart_8024085 baseEnd_8024085 := by
    simpa [prefixWord, tailWord_8024085, baseEnd_8024085] using wordTrace_append hprefix tailTrace_8024085
  have hstable : (prefixWord ++ tailWord_8024085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024085).length < 2 ^ (prefixWord ++ tailWord_8024085).sum := by decide
  have hdescent : baseEnd_8024085 < baseStart_8024085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024095 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 1, 3, 2]
def baseStart_8024095 : Nat := 118140960795 + 8024095 * 2 ^ 59
def prefixEnd_8024095 : Nat := 4983230072969 + 3 ^ 40 * 8024095 * 2
def baseEnd_8024095 : Nat := 4120217552338888425110365

theorem tailTrace_8024095 : CollatzResearch.WordTrace tailWord_8024095 prefixEnd_8024095 4120217552338888425110365 := by
  unfold tailWord_8024095
  simp only [CollatzResearch.WordTrace]
  refine ⟨292662787865081696167489739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195108525243387797444993159 292662787865081696167489739)
  ·
    refine ⟨438994181797622544251234609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292662787865081696167489739 438994181797622544251234609)
    ·
      refine ⟨329245636348216908188425957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438994181797622544251234609 329245636348216908188425957)
      ·
        refine ⟨61733556815290670285329867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329245636348216908188425957 61733556815290670285329867)
        ·
          refine ⟨92600335222936005427994801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61733556815290670285329867 92600335222936005427994801)
          ·
            refine ⟨69450251417202004070996101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92600335222936005427994801 69450251417202004070996101)
            ·
              refine ⟨13021922140725375763311769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69450251417202004070996101 13021922140725375763311769)
              ·
                refine ⟨9766441605544031822483827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13021922140725375763311769 9766441605544031822483827)
                ·
                  refine ⟨14649662408316047733725741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9766441605544031822483827 14649662408316047733725741)
                  ·
                    refine ⟨5493623403118517900147153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14649662408316047733725741 5493623403118517900147153)
                    ·
                      refine ⟨4120217552338888425110365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493623403118517900147153 4120217552338888425110365)
                      ·
                        rfl

theorem cell23_8024095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_8024095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024095 prefixEnd_8024095 := by exact prefixLift 8024095
  have htrace : WordTrace (prefixWord ++ tailWord_8024095) baseStart_8024095 baseEnd_8024095 := by
    simpa [prefixWord, tailWord_8024095, baseEnd_8024095] using wordTrace_append hprefix tailTrace_8024095
  have hstable : (prefixWord ++ tailWord_8024095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024095).length < 2 ^ (prefixWord ++ tailWord_8024095).sum := by decide
  have hdescent : baseEnd_8024095 < baseStart_8024095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024103 : List Nat := [1, 1, 7, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_8024103 : Nat := 118140960795 + 8024103 * 2 ^ 59
def prefixEnd_8024103 : Nat := 4983230072969 + 3 ^ 40 * 8024103 * 2
def baseEnd_8024103 : Nat := 4120221660184124393810329

theorem tailTrace_8024103 : CollatzResearch.WordTrace tailWord_8024103 prefixEnd_8024103 4120221660184124393810329 := by
  unfold tailWord_8024103
  simp only [CollatzResearch.WordTrace]
  refine ⟨292663079649052713533780963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195108719766035142355853975 292663079649052713533780963)
  ·
    refine ⟨438994619473579070300671445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292663079649052713533780963 438994619473579070300671445)
    ·
      refine ⟨10288936393912009460171987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 438994619473579070300671445 10288936393912009460171987)
      ·
        refine ⟨15433404590868014190257981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10288936393912009460171987 15433404590868014190257981)
        ·
          refine ⟨5787526721575505321346743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15433404590868014190257981 5787526721575505321346743)
          ·
            refine ⟨8681290082363257982020115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787526721575505321346743 8681290082363257982020115)
            ·
              refine ⟨13021935123544886973030173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681290082363257982020115 13021935123544886973030173)
              ·
                refine ⟨4883225671329332614886315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13021935123544886973030173 4883225671329332614886315)
                ·
                  refine ⟨7324838506993998922329473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883225671329332614886315 7324838506993998922329473)
                  ·
                    refine ⟨5493628880245499191747105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324838506993998922329473 5493628880245499191747105)
                    ·
                      refine ⟨4120221660184124393810329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493628880245499191747105 4120221660184124393810329)
                      ·
                        rfl

theorem cell23_8024103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_8024103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024103 prefixEnd_8024103 := by exact prefixLift 8024103
  have htrace : WordTrace (prefixWord ++ tailWord_8024103) baseStart_8024103 baseEnd_8024103 := by
    simpa [prefixWord, tailWord_8024103, baseEnd_8024103] using wordTrace_append hprefix tailTrace_8024103
  have hstable : (prefixWord ++ tailWord_8024103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024103).length < 2 ^ (prefixWord ++ tailWord_8024103).sum := by decide
  have hdescent : baseEnd_8024103 < baseStart_8024103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024125 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_8024125 : Nat := 118140960795 + 8024125 * 2 ^ 59
def prefixEnd_8024125 : Nat := 4983230072969 + 3 ^ 40 * 8024125 * 2
def baseEnd_8024125 : Nat := 4120232956758523307735227

theorem tailTrace_8024125 : CollatzResearch.WordTrace tailWord_8024125 prefixEnd_8024125 4120232956758523307735227 := by
  unfold tailWord_8024125
  simp only [CollatzResearch.WordTrace]
  refine ⟨292663882054973011291081829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195109254703315340860721219 292663882054973011291081829)
  ·
    refine ⟨54874477885307439617077843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292663882054973011291081829 54874477885307439617077843)
    ·
      refine ⟨82311716827961159425616765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54874477885307439617077843 82311716827961159425616765)
      ·
        refine ⟨30866893810485434784606287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82311716827961159425616765 30866893810485434784606287)
        ·
          refine ⟨46300340715728152176909431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30866893810485434784606287 46300340715728152176909431)
          ·
            refine ⟨69450511073592228265364147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46300340715728152176909431 69450511073592228265364147)
            ·
              refine ⟨104175766610388342398046221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69450511073592228265364147 104175766610388342398046221)
              ·
                refine ⟨39065912478895628399267333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104175766610388342398046221 39065912478895628399267333)
                ·
                  refine ⟨7324858589792930324862625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39065912478895628399267333 7324858589792930324862625)
                  ·
                    refine ⟨5493643942344697743646969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324858589792930324862625 5493643942344697743646969)
                    ·
                      refine ⟨4120232956758523307735227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493643942344697743646969 4120232956758523307735227)
                      ·
                        rfl

theorem cell23_8024125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_8024125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024125 prefixEnd_8024125 := by exact prefixLift 8024125
  have htrace : WordTrace (prefixWord ++ tailWord_8024125) baseStart_8024125 baseEnd_8024125 := by
    simpa [prefixWord, tailWord_8024125, baseEnd_8024125] using wordTrace_append hprefix tailTrace_8024125
  have hstable : (prefixWord ++ tailWord_8024125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024125).length < 2 ^ (prefixWord ++ tailWord_8024125).sum := by decide
  have hdescent : baseEnd_8024125 < baseStart_8024125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024142 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_8024142 : Nat := 118140960795 + 8024142 * 2 ^ 59
def prefixEnd_8024142 : Nat := 4983230072969 + 3 ^ 40 * 8024142 * 2
def baseEnd_8024142 : Nat := 4120241685929649741222649

theorem tailTrace_8024142 : CollatzResearch.WordTrace tailWord_8024142 prefixEnd_8024142 4120241685929649741222649 := by
  unfold tailWord_8024142
  simp only [CollatzResearch.WordTrace]
  refine ⟨36583062761988927899306335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195109668063940948796300453 36583062761988927899306335)
  ·
    refine ⟨54874594142983391848959503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36583062761988927899306335 54874594142983391848959503)
    ·
      refine ⟨82311891214475087773439255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54874594142983391848959503 82311891214475087773439255)
      ·
        refine ⟨123467836821712631660158883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82311891214475087773439255 123467836821712631660158883)
        ·
          refine ⟨185201755232568947490238325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123467836821712631660158883 185201755232568947490238325)
          ·
            refine ⟨17362664553053338827209843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185201755232568947490238325 17362664553053338827209843)
            ·
              refine ⟨26043996829580008240814765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17362664553053338827209843 26043996829580008240814765)
              ·
                refine ⟨9766498811092503090305537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26043996829580008240814765 9766498811092503090305537)
                ·
                  refine ⟨7324874108319377317729153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766498811092503090305537 7324874108319377317729153)
                  ·
                    refine ⟨5493655581239532988296865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324874108319377317729153 5493655581239532988296865)
                    ·
                      refine ⟨4120241685929649741222649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5493655581239532988296865 4120241685929649741222649)
                      ·
                        rfl

theorem cell23_8024142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_8024142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024142 prefixEnd_8024142 := by exact prefixLift 8024142
  have htrace : WordTrace (prefixWord ++ tailWord_8024142) baseStart_8024142 baseEnd_8024142 := by
    simpa [prefixWord, tailWord_8024142, baseEnd_8024142] using wordTrace_append hprefix tailTrace_8024142
  have hstable : (prefixWord ++ tailWord_8024142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024142).length < 2 ^ (prefixWord ++ tailWord_8024142).sum := by decide
  have hdescent : baseEnd_8024142 < baseStart_8024142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024178 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_8024178 : Nat := 118140960795 + 8024178 * 2 ^ 59
def prefixEnd_8024178 : Nat := 4983230072969 + 3 ^ 40 * 8024178 * 2
def baseEnd_8024178 : Nat := 1373420057077737200124161

theorem tailTrace_8024178 : CollatzResearch.WordTrace tailWord_8024178 prefixEnd_8024178 1373420057077737200124161 := by
  unfold tailWord_8024178
  simp only [CollatzResearch.WordTrace]
  refine ⟨73166453780945250335690297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195110543415854000895174125 73166453780945250335690297)
  ·
    refine ⟨54874840335708937751767723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73166453780945250335690297 54874840335708937751767723)
    ·
      refine ⟨82312260503563406627651585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54874840335708937751767723 82312260503563406627651585)
      ·
        refine ⟨61734195377672554970738689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82312260503563406627651585 61734195377672554970738689)
        ·
          refine ⟨46300646533254416228054017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61734195377672554970738689 46300646533254416228054017)
          ·
            refine ⟨34725484899940812171040513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46300646533254416228054017 34725484899940812171040513)
            ·
              refine ⟨26044113674955609128280385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34725484899940812171040513 26044113674955609128280385)
              ·
                refine ⟨19533085256216706846210289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26044113674955609128280385 19533085256216706846210289)
                ·
                  refine ⟨14649813942162530134657717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19533085256216706846210289 14649813942162530134657717)
                  ·
                    refine ⟨1373420057077737200124161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14649813942162530134657717 1373420057077737200124161)
                    ·
                      rfl

theorem cell23_8024178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_8024178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024178 prefixEnd_8024178 := by exact prefixLift 8024178
  have htrace : WordTrace (prefixWord ++ tailWord_8024178) baseStart_8024178 baseEnd_8024178 := by
    simpa [prefixWord, tailWord_8024178, baseEnd_8024178] using wordTrace_append hprefix tailTrace_8024178
  have hstable : (prefixWord ++ tailWord_8024178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024178).length < 2 ^ (prefixWord ++ tailWord_8024178).sum := by decide
  have hdescent : baseEnd_8024178 < baseStart_8024178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024182 : List Nat := [5, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_8024182 : Nat := 118140960795 + 8024182 * 2 ^ 59
def prefixEnd_8024182 : Nat := 4983230072969 + 3 ^ 40 * 8024182 * 2
def baseEnd_8024182 : Nat := 457806913906203287191385

theorem tailTrace_8024182 : CollatzResearch.WordTrace tailWord_8024182 prefixEnd_8024182 457806913906203287191385 := by
  unfold tailWord_8024182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18291622563485406876619175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195110640677177673350604533 18291622563485406876619175)
  ·
    refine ⟨27437433845228110314928763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18291622563485406876619175 27437433845228110314928763)
    ·
      refine ⟨41156150767842165472393145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27437433845228110314928763 41156150767842165472393145)
      ·
        refine ⟨30867113075881624104294859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41156150767842165472393145 30867113075881624104294859)
        ·
          refine ⟨46300669613822436156442289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30867113075881624104294859 46300669613822436156442289)
          ·
            refine ⟨34725502210366827117331717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46300669613822436156442289 34725502210366827117331717)
            ·
              refine ⟨6511031664443780084499697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34725502210366827117331717 6511031664443780084499697)
              ·
                refine ⟨4883273748332835063374773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6511031664443780084499697 4883273748332835063374773)
                ·
                  refine ⟨457806913906203287191385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4883273748332835063374773 457806913906203287191385)
                  ·
                    rfl

theorem cell23_8024182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_8024182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024182 prefixEnd_8024182 := by exact prefixLift 8024182
  have htrace : WordTrace (prefixWord ++ tailWord_8024182) baseStart_8024182 baseEnd_8024182 := by
    simpa [prefixWord, tailWord_8024182, baseEnd_8024182] using wordTrace_append hprefix tailTrace_8024182
  have hstable : (prefixWord ++ tailWord_8024182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024182).length < 2 ^ (prefixWord ++ tailWord_8024182).sum := by decide
  have hdescent : baseEnd_8024182 < baseStart_8024182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024208 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 3, 4]
def baseStart_8024208 : Nat := 118140960795 + 8024208 * 2 ^ 59
def prefixEnd_8024208 : Nat := 4983230072969 + 3 ^ 40 * 8024208 * 2
def baseEnd_8024208 : Nat := 1373425191884282160999115

theorem tailTrace_8024208 : CollatzResearch.WordTrace tailWord_8024208 prefixEnd_8024208 1373425191884282160999115 := by
  unfold tailWord_8024208
  simp only [CollatzResearch.WordTrace]
  refine ⟨146333454656836158233176639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195111272875781544310902185 146333454656836158233176639)
  ·
    refine ⟨219500181985254237349764959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146333454656836158233176639 219500181985254237349764959)
    ·
      refine ⟨329250272977881356024647439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219500181985254237349764959 329250272977881356024647439)
      ·
        refine ⟨493875409466822034036971159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329250272977881356024647439 493875409466822034036971159)
        ·
          refine ⟨740813114200233051055456739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493875409466822034036971159 740813114200233051055456739)
          ·
            refine ⟨1111219671300349576583185109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740813114200233051055456739 1111219671300349576583185109)
            ·
              refine ⟨26044211046101943201168401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1111219671300349576583185109 26044211046101943201168401)
              ·
                refine ⟨19533158284576457400876301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26044211046101943201168401 19533158284576457400876301)
                ·
                  refine ⟨7324934356716171525328613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19533158284576457400876301 7324934356716171525328613)
                  ·
                    refine ⟨1373425191884282160999115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324934356716171525328613 1373425191884282160999115)
                    ·
                      rfl

theorem cell23_8024208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_8024208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024208 prefixEnd_8024208 := by exact prefixLift 8024208
  have htrace : WordTrace (prefixWord ++ tailWord_8024208) baseStart_8024208 baseEnd_8024208 := by
    simpa [prefixWord, tailWord_8024208, baseEnd_8024208] using wordTrace_append hprefix tailTrace_8024208
  have hstable : (prefixWord ++ tailWord_8024208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024208).length < 2 ^ (prefixWord ++ tailWord_8024208).sum := by decide
  have hdescent : baseEnd_8024208 < baseStart_8024208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024261 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_8024261 : Nat := 118140960795 + 8024261 * 2 ^ 59
def prefixEnd_8024261 : Nat := 4983230072969 + 3 ^ 40 * 8024261 * 2
def baseEnd_8024261 : Nat := 4120302790127534775634601

theorem tailTrace_8024261 : CollatzResearch.WordTrace tailWord_8024261 prefixEnd_8024261 4120302790127534775634601 := by
  unfold tailWord_8024261
  simp only [CollatzResearch.WordTrace]
  refine ⟨292668842382480306518032637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195112561588320204345355091 292668842382480306518032637)
  ·
    refine ⟨109750815893430114944262239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292668842382480306518032637 109750815893430114944262239)
    ·
      refine ⟨164626223840145172416393359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109750815893430114944262239 164626223840145172416393359)
      ·
        refine ⟨246939335760217758624590039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164626223840145172416393359 246939335760217758624590039)
        ·
          refine ⟨370409003640326637936885059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246939335760217758624590039 370409003640326637936885059)
          ·
            refine ⟨555613505460489956905327589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370409003640326637936885059 555613505460489956905327589)
            ·
              refine ⟨104177532273841866919748923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 555613505460489956905327589 104177532273841866919748923)
              ·
                refine ⟨156266298410762800379623385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104177532273841866919748923 156266298410762800379623385)
                ·
                  refine ⟨117199723808072100284717539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156266298410762800379623385 117199723808072100284717539)
                  ·
                    refine ⟨175799585712108150427076309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117199723808072100284717539 175799585712108150427076309)
                    ·
                      refine ⟨4120302790127534775634601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175799585712108150427076309 4120302790127534775634601)
                      ·
                        rfl

theorem cell23_8024261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_8024261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024261 prefixEnd_8024261 := by exact prefixLift 8024261
  have htrace : WordTrace (prefixWord ++ tailWord_8024261) baseStart_8024261 baseEnd_8024261 := by
    simpa [prefixWord, tailWord_8024261, baseEnd_8024261] using wordTrace_append hprefix tailTrace_8024261
  have hstable : (prefixWord ++ tailWord_8024261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024261).length < 2 ^ (prefixWord ++ tailWord_8024261).sum := by decide
  have hdescent : baseEnd_8024261 < baseStart_8024261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024299 : List Nat := [1, 1, 1, 1, 2, 5, 5, 2, 1, 1, 3]
def baseStart_8024299 : Nat := 118140960795 + 8024299 * 2 ^ 59
def prefixEnd_8024299 : Nat := 4983230072969 + 3 ^ 40 * 8024299 * 2
def baseEnd_8024299 : Nat := 4120322302392405626959427

theorem tailTrace_8024299 : CollatzResearch.WordTrace tailWord_8024299 prefixEnd_8024299 4120322302392405626959427 := by
  unfold tailWord_8024299
  simp only [CollatzResearch.WordTrace]
  refine ⟨292670228356342639007915951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195113485570895092671943967 292670228356342639007915951)
  ·
    refine ⟨439005342534513958511873927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292670228356342639007915951 439005342534513958511873927)
    ·
      refine ⟨658508013801770937767810891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439005342534513958511873927 658508013801770937767810891)
      ·
        refine ⟨987762020702656406651716337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658508013801770937767810891 987762020702656406651716337)
        ·
          refine ⟨740821515526992304988787253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987762020702656406651716337 740821515526992304988787253)
          ·
            refine ⟨69452017080655528592698805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 740821515526992304988787253 69452017080655528592698805)
            ·
              refine ⟨6511126601311455805565513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69452017080655528592698805 6511126601311455805565513)
              ·
                refine ⟨4883344950983591854174135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6511126601311455805565513 4883344950983591854174135)
                ·
                  refine ⟨7325017426475387781261203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883344950983591854174135 7325017426475387781261203)
                  ·
                    refine ⟨10987526139713081671891805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7325017426475387781261203 10987526139713081671891805)
                    ·
                      refine ⟨4120322302392405626959427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987526139713081671891805 4120322302392405626959427)
                      ·
                        rfl

theorem cell23_8024299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 1, 3].length) (baseStart_8024299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024299 prefixEnd_8024299 := by exact prefixLift 8024299
  have htrace : WordTrace (prefixWord ++ tailWord_8024299) baseStart_8024299 baseEnd_8024299 := by
    simpa [prefixWord, tailWord_8024299, baseEnd_8024299] using wordTrace_append hprefix tailTrace_8024299
  have hstable : (prefixWord ++ tailWord_8024299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024299).length < 2 ^ (prefixWord ++ tailWord_8024299).sum := by decide
  have hdescent : baseEnd_8024299 < baseStart_8024299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024322 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_8024322 : Nat := 118140960795 + 8024322 * 2 ^ 59
def prefixEnd_8024322 : Nat := 4983230072969 + 3 ^ 40 * 8024322 * 2
def baseEnd_8024322 : Nat := 4120334112447459036971821

theorem tailTrace_8024322 : CollatzResearch.WordTrace tailWord_8024322 prefixEnd_8024322 4120334112447459036971821 := by
  unfold tailWord_8024322
  simp only [CollatzResearch.WordTrace]
  refine ⟨73167766808814828484000805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195114044823506209290668813 73167766808814828484000805)
  ·
    refine ⟨13718956276652780340750151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73167766808814828484000805 13718956276652780340750151)
    ·
      refine ⟨20578434414979170511125227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13718956276652780340750151 20578434414979170511125227)
      ·
        refine ⟨30867651622468755766687841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20578434414979170511125227 30867651622468755766687841)
        ·
          refine ⟨23150738716851566825015881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30867651622468755766687841 23150738716851566825015881)
          ·
            refine ⟨17363054037638675118761911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23150738716851566825015881 17363054037638675118761911)
            ·
              refine ⟨26044581056458012678142867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17363054037638675118761911 26044581056458012678142867)
              ·
                refine ⟨39066871584687019017214301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26044581056458012678142867 39066871584687019017214301)
                ·
                  refine ⟨14650076844257632131455363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39066871584687019017214301 14650076844257632131455363)
                  ·
                    refine ⟨21975115266386448197183045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14650076844257632131455363 21975115266386448197183045)
                    ·
                      refine ⟨4120334112447459036971821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21975115266386448197183045 4120334112447459036971821)
                      ·
                        rfl

theorem cell23_8024322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_8024322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024322 prefixEnd_8024322 := by exact prefixLift 8024322
  have htrace : WordTrace (prefixWord ++ tailWord_8024322) baseStart_8024322 baseEnd_8024322 := by
    simpa [prefixWord, tailWord_8024322, baseEnd_8024322] using wordTrace_append hprefix tailTrace_8024322
  have hstable : (prefixWord ++ tailWord_8024322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024322).length < 2 ^ (prefixWord ++ tailWord_8024322).sum := by decide
  have hdescent : baseEnd_8024322 < baseStart_8024322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024325 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_8024325 : Nat := 118140960795 + 8024325 * 2 ^ 59
def prefixEnd_8024325 : Nat := 4983230072969 + 3 ^ 40 * 8024325 * 2
def baseEnd_8024325 : Nat := 4120335652889422525234307

theorem tailTrace_8024325 : CollatzResearch.WordTrace tailWord_8024325 prefixEnd_8024325 4120335652889422525234307 := by
  unfold tailWord_8024325
  simp only [CollatzResearch.WordTrace]
  refine ⟨292671176654248445448362429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195114117769498963632241619 292671176654248445448362429)
  ·
    refine ⟨109751691245343167043135911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292671176654248445448362429 109751691245343167043135911)
    ·
      refine ⟨164627536868014750564703867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109751691245343167043135911 164627536868014750564703867)
      ·
        refine ⟨246941305302022125847055801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164627536868014750564703867 246941305302022125847055801)
        ·
          refine ⟨185205978976516594385291851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246941305302022125847055801 185205978976516594385291851)
          ·
            refine ⟨277808968464774891577937777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185205978976516594385291851 277808968464774891577937777)
            ·
              refine ⟨208356726348581168683453333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277808968464774891577937777 208356726348581168683453333)
              ·
                refine ⟨9766721547589742282036875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208356726348581168683453333 9766721547589742282036875)
                ·
                  refine ⟨14650082321384613423055313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9766721547589742282036875 14650082321384613423055313)
                  ·
                    refine ⟨10987561741038460067291485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14650082321384613423055313 10987561741038460067291485)
                    ·
                      refine ⟨4120335652889422525234307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10987561741038460067291485 4120335652889422525234307)
                      ·
                        rfl

theorem cell23_8024325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_8024325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024325 prefixEnd_8024325 := by exact prefixLift 8024325
  have htrace : WordTrace (prefixWord ++ tailWord_8024325) baseStart_8024325 baseEnd_8024325 := by
    simpa [prefixWord, tailWord_8024325, baseEnd_8024325] using wordTrace_append hprefix tailTrace_8024325
  have hstable : (prefixWord ++ tailWord_8024325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024325).length < 2 ^ (prefixWord ++ tailWord_8024325).sum := by decide
  have hdescent : baseEnd_8024325 < baseStart_8024325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8024328 : List Nat := [2, 1, 3, 2, 3, 1, 2, 9]
def baseStart_8024328 : Nat := 118140960795 + 8024328 * 2 ^ 59
def prefixEnd_8024328 : Nat := 4983230072969 + 3 ^ 40 * 8024328 * 2
def baseEnd_8024328 : Nat := 152605081234495778277659

theorem tailTrace_8024328 : CollatzResearch.WordTrace tailWord_8024328 prefixEnd_8024328 152605081234495778277659 := by
  unfold tailWord_8024328
  simp only [CollatzResearch.WordTrace]
  refine ⟨146335643036618788480360819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195114190715491717973814425 146335643036618788480360819)
  ·
    refine ⟨219503464554928182720541229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146335643036618788480360819 219503464554928182720541229)
    ·
      refine ⟨82313799208098068520202961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219503464554928182720541229 82313799208098068520202961)
      ·
        refine ⟨61735349406073551390152221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82313799208098068520202961 61735349406073551390152221)
        ·
          refine ⟨23150756027277581771307083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61735349406073551390152221 23150756027277581771307083)
          ·
            refine ⟨34726134040916372656960625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23150756027277581771307083 34726134040916372656960625)
            ·
              refine ⟨26044600530687279492720469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34726134040916372656960625 26044600530687279492720469)
              ·
                refine ⟨152605081234495778277659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26044600530687279492720469 152605081234495778277659)
                ·
                  rfl

theorem cell23_8024328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 9].length) (baseStart_8024328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8024328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8024328 prefixEnd_8024328 := by exact prefixLift 8024328
  have htrace : WordTrace (prefixWord ++ tailWord_8024328) baseStart_8024328 baseEnd_8024328 := by
    simpa [prefixWord, tailWord_8024328, baseEnd_8024328] using wordTrace_append hprefix tailTrace_8024328
  have hstable : (prefixWord ++ tailWord_8024328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8024328).length < 2 ^ (prefixWord ++ tailWord_8024328).sum := by decide
  have hdescent : baseEnd_8024328 < baseStart_8024328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8024328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
