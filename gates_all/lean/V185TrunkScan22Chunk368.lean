import V185TrunkScan22Chunk367

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3282336 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 3, 3]
def baseStart_3282336 : Nat := 118140960795 + 3282336 * 2 ^ 59
def prefixEnd_3282336 : Nat := 4983230072969 + 3 ^ 40 * 3282336 * 2
def baseEnd_3282336 : Nat := 1123610691704116719336545

theorem tailTrace_3282336 : CollatzResearch.WordTrace tailWord_3282336 prefixEnd_3282336 1123610691704116719336545 := by
  unfold tailWord_3282336
  simp only [CollatzResearch.WordTrace]
  refine ⟨59858314518332362601993431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79811086024443150135991241 59858314518332362601993431)
  ·
    refine ⟨89787471777498543902990147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59858314518332362601993431 89787471777498543902990147)
    ·
      refine ⟨134681207666247815854485221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89787471777498543902990147 134681207666247815854485221)
      ·
        refine ⟨25252726437421465472715979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134681207666247815854485221 25252726437421465472715979)
        ·
          refine ⟨37879089656132198209073969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25252726437421465472715979 37879089656132198209073969)
          ·
            refine ⟨28409317242099148656805477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37879089656132198209073969 28409317242099148656805477)
            ·
              refine ⟨5326746982893590373151027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28409317242099148656805477 5326746982893590373151027)
              ·
                refine ⟨7990120474340385559726541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326746982893590373151027 7990120474340385559726541)
                ·
                  refine ⟨2996295177877644584897453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7990120474340385559726541 2996295177877644584897453)
                  ·
                    refine ⟨1123610691704116719336545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996295177877644584897453 1123610691704116719336545)
                    ·
                      rfl

theorem cell22_3282336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_3282336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282336 prefixEnd_3282336 := by exact prefixLift 3282336
  have htrace : WordTrace (prefixWord ++ tailWord_3282336) baseStart_3282336 baseEnd_3282336 := by
    simpa [prefixWord, tailWord_3282336, baseEnd_3282336] using wordTrace_append hprefix tailTrace_3282336
  have hstable : (prefixWord ++ tailWord_3282336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282336).length < 2 ^ (prefixWord ++ tailWord_3282336).sum := by decide
  have hdescent : baseEnd_3282336 < baseStart_3282336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282347 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 5, 7]
def baseStart_3282347 : Nat := 118140960795 + 3282347 * 2 ^ 59
def prefixEnd_3282347 : Nat := 4983230072969 + 3 ^ 40 * 3282347 * 2
def baseEnd_3282347 : Nat := 1123614457228916357311511

theorem tailTrace_3282347 : CollatzResearch.WordTrace tailWord_3282347 prefixEnd_3282347 1123614457228916357311511 := by
  unfold tailWord_3282347
  simp only [CollatzResearch.WordTrace]
  refine ⟨119717030239624874082637295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79811353493083249388424863 119717030239624874082637295)
  ·
    refine ⟨179575545359437311123955943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119717030239624874082637295 179575545359437311123955943)
    ·
      refine ⟨269363318039155966685933915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179575545359437311123955943 269363318039155966685933915)
      ·
        refine ⟨404044977058733950028900873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269363318039155966685933915 404044977058733950028900873)
        ·
          refine ⟨303033732794050462521675655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404044977058733950028900873 303033732794050462521675655)
          ·
            refine ⟨454550599191075693782513483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303033732794050462521675655 454550599191075693782513483)
            ·
              refine ⟨681825898786613540673770225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454550599191075693782513483 681825898786613540673770225)
              ·
                refine ⟨511369424089960155505327669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681825898786613540673770225 511369424089960155505327669)
                ·
                  refine ⟨47940883508433764578624469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 511369424089960155505327669 47940883508433764578624469)
                  ·
                    refine ⟨1123614457228916357311511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47940883508433764578624469 1123614457228916357311511)
                    ·
                      rfl

theorem cell22_3282347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_3282347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282347 prefixEnd_3282347 := by exact prefixLift 3282347
  have htrace : WordTrace (prefixWord ++ tailWord_3282347) baseStart_3282347 baseEnd_3282347 := by
    simpa [prefixWord, tailWord_3282347, baseEnd_3282347] using wordTrace_append hprefix tailTrace_3282347
  have hstable : (prefixWord ++ tailWord_3282347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282347).length < 2 ^ (prefixWord ++ tailWord_3282347).sum := by decide
  have hdescent : baseEnd_3282347 < baseStart_3282347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282413 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_3282413 : Nat := 118140960795 + 3282413 * 2 ^ 59
def prefixEnd_3282413 : Nat := 4983230072969 + 3 ^ 40 * 3282413 * 2
def baseEnd_3282413 : Nat := 1123637050377714185161309

theorem tailTrace_3282413 : CollatzResearch.WordTrace tailWord_3282413 prefixEnd_3282413 1123637050377714185161309 := by
  unfold tailWord_3282413
  simp only [CollatzResearch.WordTrace]
  refine ⟨119719437457385767354539893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79812958304923844903026595 119719437457385767354539893)
  ·
    refine ⟨11223697261629915689488115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119719437457385767354539893 11223697261629915689488115)
    ·
      refine ⟨16835545892444873534232173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11223697261629915689488115 16835545892444873534232173)
      ·
        refine ⟨6313329709666827575337065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16835545892444873534232173 6313329709666827575337065)
        ·
          refine ⟨4734997282250120681502799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6313329709666827575337065 4734997282250120681502799)
          ·
            refine ⟨7102495923375181022254199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4734997282250120681502799 7102495923375181022254199)
            ·
              refine ⟨10653743885062771533381299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7102495923375181022254199 10653743885062771533381299)
              ·
                refine ⟨15980615827594157300071949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10653743885062771533381299 15980615827594157300071949)
                ·
                  refine ⟨5992730935347808987526981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15980615827594157300071949 5992730935347808987526981)
                  ·
                    refine ⟨1123637050377714185161309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5992730935347808987526981 1123637050377714185161309)
                    ·
                      rfl

theorem cell22_3282413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_3282413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282413 prefixEnd_3282413 := by exact prefixLift 3282413
  have htrace : WordTrace (prefixWord ++ tailWord_3282413) baseStart_3282413 baseEnd_3282413 := by
    simpa [prefixWord, tailWord_3282413, baseEnd_3282413] using wordTrace_append hprefix tailTrace_3282413
  have hstable : (prefixWord ++ tailWord_3282413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282413).length < 2 ^ (prefixWord ++ tailWord_3282413).sum := by decide
  have hdescent : baseEnd_3282413 < baseStart_3282413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282438 : List Nat := [6, 2, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3282438 : Nat := 118140960795 + 3282438 * 2 ^ 59
def prefixEnd_3282438 : Nat := 4983230072969 + 3 ^ 40 * 3282438 * 2
def baseEnd_3282438 : Nat := 1123645608388622453286233

theorem tailTrace_3282438 : CollatzResearch.WordTrace tailWord_3282438 prefixEnd_3282438 1123645608388622453286233 := by
  unfold tailWord_3282438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741260915071724894506249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79813566188196797749466645 3741260915071724894506249)
  ·
    refine ⟨2805945686303793670879687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3741260915071724894506249 2805945686303793670879687)
    ·
      refine ⟨4208918529455690506319531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2805945686303793670879687 4208918529455690506319531)
      ·
        refine ⟨6313377794183535759479297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208918529455690506319531 6313377794183535759479297)
        ·
          refine ⟨4735033345637651819609473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6313377794183535759479297 4735033345637651819609473)
          ·
            refine ⟨3551275009228238864707105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735033345637651819609473 3551275009228238864707105)
            ·
              refine ⟨2663456256921179148530329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3551275009228238864707105 2663456256921179148530329)
              ·
                refine ⟨1997592192690884361397747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663456256921179148530329 1997592192690884361397747)
                ·
                  refine ⟨2996388289036326542096621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997592192690884361397747 2996388289036326542096621)
                  ·
                    refine ⟨1123645608388622453286233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996388289036326542096621 1123645608388622453286233)
                    ·
                      rfl

theorem cell22_3282438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3282438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282438 prefixEnd_3282438 := by exact prefixLift 3282438
  have htrace : WordTrace (prefixWord ++ tailWord_3282438) baseStart_3282438 baseEnd_3282438 := by
    simpa [prefixWord, tailWord_3282438, baseEnd_3282438] using wordTrace_append hprefix tailTrace_3282438
  have hstable : (prefixWord ++ tailWord_3282438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282438).length < 2 ^ (prefixWord ++ tailWord_3282438).sum := by decide
  have hdescent : baseEnd_3282438 < baseStart_3282438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282439 : List Nat := [1, 1, 4, 3, 2, 11]
def baseStart_3282439 : Nat := 118140960795 + 3282439 * 2 ^ 59
def prefixEnd_3282439 : Nat := 4983230072969 + 3 ^ 40 * 3282439 * 2
def baseEnd_3282439 : Nat := 13872172230976034370509

theorem tailTrace_3282439 : CollatzResearch.WordTrace tailWord_3282439 prefixEnd_3282439 13872172230976034370509 := by
  unfold tailWord_3282439
  simp only [CollatzResearch.WordTrace]
  refine ⟨119720385755291573794986371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79813590503527715863324247 119720385755291573794986371)
  ·
    refine ⟨179580578632937360692479557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119720385755291573794986371 179580578632937360692479557)
    ·
      refine ⟨33671358493675755129839917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179580578632937360692479557 33671358493675755129839917)
      ·
        refine ⟨12626759435128408173689969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33671358493675755129839917 12626759435128408173689969)
        ·
          refine ⟨9470069576346306130267477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12626759435128408173689969 9470069576346306130267477)
          ·
            refine ⟨13872172230976034370509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9470069576346306130267477 13872172230976034370509)
            ·
              rfl

theorem cell22_3282439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 11].length) (baseStart_3282439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282439 prefixEnd_3282439 := by exact prefixLift 3282439
  have htrace : WordTrace (prefixWord ++ tailWord_3282439) baseStart_3282439 baseEnd_3282439 := by
    simpa [prefixWord, tailWord_3282439, baseEnd_3282439] using wordTrace_append hprefix tailTrace_3282439
  have hstable : (prefixWord ++ tailWord_3282439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282439).length < 2 ^ (prefixWord ++ tailWord_3282439).sum := by decide
  have hdescent : baseEnd_3282439 < baseStart_3282439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282462 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3282462 : Nat := 118140960795 + 3282462 * 2 ^ 59
def prefixEnd_3282462 : Nat := 4983230072969 + 3 ^ 40 * 3282462 * 2
def baseEnd_3282462 : Nat := 374551274693031463562053

theorem tailTrace_3282462 : CollatzResearch.WordTrace tailWord_3282462 prefixEnd_3282462 374551274693031463562053 := by
  unfold tailWord_3282462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14965153079276031090384205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79814149756138832482049093 14965153079276031090384205)
  ·
    refine ⟨5611932404728511658894077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14965153079276031090384205 5611932404728511658894077)
    ·
      refine ⟨2104474651773191872085279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5611932404728511658894077 2104474651773191872085279)
      ·
        refine ⟨3156711977659787808127919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104474651773191872085279 3156711977659787808127919)
        ·
          refine ⟨4735067966489681712191879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156711977659787808127919 4735067966489681712191879)
          ·
            refine ⟨7102601949734522568287819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735067966489681712191879 7102601949734522568287819)
            ·
              refine ⟨10653902924601783852431729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7102601949734522568287819 10653902924601783852431729)
              ·
                refine ⟨7990427193451337889323797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10653902924601783852431729 7990427193451337889323797)
                ·
                  refine ⟨374551274693031463562053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7990427193451337889323797 374551274693031463562053)
                  ·
                    rfl

theorem cell22_3282462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3282462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282462 prefixEnd_3282462 := by exact prefixLift 3282462
  have htrace : WordTrace (prefixWord ++ tailWord_3282462) baseStart_3282462 baseEnd_3282462 := by
    simpa [prefixWord, tailWord_3282462, baseEnd_3282462] using wordTrace_append hprefix tailTrace_3282462
  have hstable : (prefixWord ++ tailWord_3282462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282462).length < 2 ^ (prefixWord ++ tailWord_3282462).sum := by decide
  have hdescent : baseEnd_3282462 < baseStart_3282462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282469 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_3282469 : Nat := 118140960795 + 3282469 * 2 ^ 59
def prefixEnd_3282469 : Nat := 4983230072969 + 3 ^ 40 * 3282469 * 2
def baseEnd_3282469 : Nat := 1123656220322148705761137

theorem tailTrace_3282469 : CollatzResearch.WordTrace tailWord_3282469 prefixEnd_3282469 1123656220322148705761137 := by
  unfold tailWord_3282469
  simp only [CollatzResearch.WordTrace]
  refine ⟨119721479945182888918578461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79814319963455259279052307 119721479945182888918578461)
  ·
    refine ⟨44895554979443583344466923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119721479945182888918578461 44895554979443583344466923)
    ·
      refine ⟨67343332469165375016700385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44895554979443583344466923 67343332469165375016700385)
      ·
        refine ⟨50507499351874031262525289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67343332469165375016700385 50507499351874031262525289)
        ·
          refine ⟨37880624513905523446893967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50507499351874031262525289 37880624513905523446893967)
          ·
            refine ⟨56820936770858285170340951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37880624513905523446893967 56820936770858285170340951)
            ·
              refine ⟨85231405156287427755511427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56820936770858285170340951 85231405156287427755511427)
              ·
                refine ⟨127847107734431141633267141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85231405156287427755511427 127847107734431141633267141)
                ·
                  refine ⟨23971332700205839056237589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127847107734431141633267141 23971332700205839056237589)
                  ·
                    refine ⟨1123656220322148705761137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23971332700205839056237589 1123656220322148705761137)
                    ·
                      rfl

theorem cell22_3282469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3282469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282469 prefixEnd_3282469 := by exact prefixLift 3282469
  have htrace : WordTrace (prefixWord ++ tailWord_3282469) baseStart_3282469 baseEnd_3282469 := by
    simpa [prefixWord, tailWord_3282469, baseEnd_3282469] using wordTrace_append hprefix tailTrace_3282469
  have hstable : (prefixWord ++ tailWord_3282469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282469).length < 2 ^ (prefixWord ++ tailWord_3282469).sum := by decide
  have hdescent : baseEnd_3282469 < baseStart_3282469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282516 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3282516 : Nat := 118140960795 + 3282516 * 2 ^ 59
def prefixEnd_3282516 : Nat := 4983230072969 + 3 ^ 40 * 3282516 * 2
def baseEnd_3282516 : Nat := 1123672309382656249835993

theorem tailTrace_3282516 : CollatzResearch.WordTrace tailWord_3282516 prefixEnd_3282516 1123672309382656249835993 := by
  unfold tailWord_3282516
  simp only [CollatzResearch.WordTrace]
  refine ⟨59861597088006307972769701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79815462784008410630359601 59861597088006307972769701)
  ·
    refine ⟨11224049454001182744894319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59861597088006307972769701 11224049454001182744894319)
    ·
      refine ⟨16836074181001774117341479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11224049454001182744894319 16836074181001774117341479)
      ·
        refine ⟨25254111271502661176012219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16836074181001774117341479 25254111271502661176012219)
        ·
          refine ⟨37881166907253991764018329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25254111271502661176012219 37881166907253991764018329)
          ·
            refine ⟨28410875180440493823013747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37881166907253991764018329 28410875180440493823013747)
            ·
              refine ⟨42616312770660740734520621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28410875180440493823013747 42616312770660740734520621)
              ·
                refine ⟨15981117288997777775445233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42616312770660740734520621 15981117288997777775445233)
                ·
                  refine ⟨11985837966748333331583925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15981117288997777775445233 11985837966748333331583925)
                  ·
                    refine ⟨1123672309382656249835993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11985837966748333331583925 1123672309382656249835993)
                    ·
                      rfl

theorem cell22_3282516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3282516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282516 prefixEnd_3282516 := by exact prefixLift 3282516
  have htrace : WordTrace (prefixWord ++ tailWord_3282516) baseStart_3282516 baseEnd_3282516 := by
    simpa [prefixWord, tailWord_3282516, baseEnd_3282516] using wordTrace_append hprefix tailTrace_3282516
  have hstable : (prefixWord ++ tailWord_3282516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282516).length < 2 ^ (prefixWord ++ tailWord_3282516).sum := by decide
  have hdescent : baseEnd_3282516 < baseStart_3282516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282593 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3282593 : Nat := 118140960795 + 3282593 * 2 ^ 59
def prefixEnd_3282593 : Nat := 4983230072969 + 3 ^ 40 * 3282593 * 2
def baseEnd_3282593 : Nat := 1123698668056253715660757

theorem tailTrace_3282593 : CollatzResearch.WordTrace tailWord_3282593 prefixEnd_3282593 1123698668056253715660757 := by
  unfold tailWord_3282593
  simp only [CollatzResearch.WordTrace]
  refine ⟨119726002596733658096092433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79817335064489105397394955 119726002596733658096092433)
  ·
    refine ⟨89794501947550243572069325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119726002596733658096092433 89794501947550243572069325)
    ·
      refine ⟨33672938230331341339525997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89794501947550243572069325 33672938230331341339525997)
      ·
        refine ⟨12627351836374253002322249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33672938230331341339525997 12627351836374253002322249)
        ·
          refine ⟨9470513877280689751741687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12627351836374253002322249 9470513877280689751741687)
          ·
            refine ⟨14205770815921034627612531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9470513877280689751741687 14205770815921034627612531)
            ·
              refine ⟨21308656223881551941418797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14205770815921034627612531 21308656223881551941418797)
              ·
                refine ⟨7990746083955581978032049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21308656223881551941418797 7990746083955581978032049)
                ·
                  refine ⟨5993059562966686483524037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7990746083955581978032049 5993059562966686483524037)
                  ·
                    refine ⟨1123698668056253715660757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993059562966686483524037 1123698668056253715660757)
                    ·
                      rfl

theorem cell22_3282593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3282593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282593 prefixEnd_3282593 := by exact prefixLift 3282593
  have htrace : WordTrace (prefixWord ++ tailWord_3282593) baseStart_3282593 baseEnd_3282593 := by
    simpa [prefixWord, tailWord_3282593, baseEnd_3282593] using wordTrace_append hprefix tailTrace_3282593
  have hstable : (prefixWord ++ tailWord_3282593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282593).length < 2 ^ (prefixWord ++ tailWord_3282593).sum := by decide
  have hdescent : baseEnd_3282593 < baseStart_3282593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282614 : List Nat := [5, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_3282614 : Nat := 118140960795 + 3282614 * 2 ^ 59
def prefixEnd_3282614 : Nat := 4983230072969 + 3 ^ 40 * 3282614 * 2
def baseEnd_3282614 : Nat := 374568618928472220295231

theorem tailTrace_3282614 : CollatzResearch.WordTrace tailWord_3282614 prefixEnd_3282614 374568618928472220295231 := by
  unfold tailWord_3282614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482923033103598667662931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79817845686438385788404597 7482923033103598667662931)
  ·
    refine ⟨11224384549655398001494397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7482923033103598667662931 11224384549655398001494397)
    ·
      refine ⟨4209144206120774250560399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11224384549655398001494397 4209144206120774250560399)
      ·
        refine ⟨6313716309181161375840599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209144206120774250560399 6313716309181161375840599)
        ·
          refine ⟨9470574463771742063760899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6313716309181161375840599 9470574463771742063760899)
          ·
            refine ⟨14205861695657613095641349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9470574463771742063760899 14205861695657613095641349)
            ·
              refine ⟨2663599067935802455432753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14205861695657613095641349 2663599067935802455432753)
              ·
                refine ⟨1997699300951851841574565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663599067935802455432753 1997699300951851841574565)
                ·
                  refine ⟨374568618928472220295231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997699300951851841574565 374568618928472220295231)
                  ·
                    rfl

theorem cell22_3282614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_3282614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282614 prefixEnd_3282614 := by exact prefixLift 3282614
  have htrace : WordTrace (prefixWord ++ tailWord_3282614) baseStart_3282614 baseEnd_3282614 := by
    simpa [prefixWord, tailWord_3282614, baseEnd_3282614] using wordTrace_append hprefix tailTrace_3282614
  have hstable : (prefixWord ++ tailWord_3282614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282614).length < 2 ^ (prefixWord ++ tailWord_3282614).sum := by decide
  have hdescent : baseEnd_3282614 < baseStart_3282614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282621 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_3282621 : Nat := 118140960795 + 3282621 * 2 ^ 59
def prefixEnd_3282621 : Nat := 4983230072969 + 3 ^ 40 * 3282621 * 2
def baseEnd_3282621 : Nat := 1123708253028470975960671

theorem tailTrace_3282621 : CollatzResearch.WordTrace tailWord_3282621 prefixEnd_3282621 1123708253028470975960671 := by
  unfold tailWord_3282621
  simp only [CollatzResearch.WordTrace]
  refine ⟨119727023840632218878111717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79818015893754812585407811 119727023840632218878111717)
  ·
    refine ⟨22448816970118541039645947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119727023840632218878111717 22448816970118541039645947)
    ·
      refine ⟨33673225455177811559468921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22448816970118541039645947 33673225455177811559468921)
      ·
        refine ⟨25254919091383358669601691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33673225455177811559468921 25254919091383358669601691)
        ·
          refine ⟨37882378637075038004402537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25254919091383358669601691 37882378637075038004402537)
          ·
            refine ⟨28411783977806278503301903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37882378637075038004402537 28411783977806278503301903)
            ·
              refine ⟨42617675966709417754952855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28411783977806278503301903 42617675966709417754952855)
              ·
                refine ⟨63926513950064126632429283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42617675966709417754952855 63926513950064126632429283)
                ·
                  refine ⟨95889770925096189948643925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63926513950064126632429283 95889770925096189948643925)
                  ·
                    refine ⟨1123708253028470975960671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95889770925096189948643925 1123708253028470975960671)
                    ·
                      rfl

theorem cell22_3282621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_3282621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282621 prefixEnd_3282621 := by exact prefixLift 3282621
  have htrace : WordTrace (prefixWord ++ tailWord_3282621) baseStart_3282621 baseEnd_3282621 := by
    simpa [prefixWord, tailWord_3282621, baseEnd_3282621] using wordTrace_append hprefix tailTrace_3282621
  have hstable : (prefixWord ++ tailWord_3282621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282621).length < 2 ^ (prefixWord ++ tailWord_3282621).sum := by decide
  have hdescent : baseEnd_3282621 < baseStart_3282621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282623 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 3, 3]
def baseStart_3282623 : Nat := 118140960795 + 3282623 * 2 ^ 59
def prefixEnd_3282623 : Nat := 4983230072969 + 3 ^ 40 * 3282623 * 2
def baseEnd_3282623 : Nat := 1123708937669343637410665

theorem tailTrace_3282623 : CollatzResearch.WordTrace tailWord_3282623 prefixEnd_3282623 1123708937669343637410665 := by
  unfold tailWord_3282623
  simp only [CollatzResearch.WordTrace]
  refine ⟨119727096786624973219684523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79818064524416648813123015 119727096786624973219684523)
  ·
    refine ⟨179590645179937459829526785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119727096786624973219684523 179590645179937459829526785)
    ·
      refine ⟨134692983884953094872145089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179590645179937459829526785 134692983884953094872145089)
      ·
        refine ⟨101019737913714821154108817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134692983884953094872145089 101019737913714821154108817)
        ·
          refine ⟨75764803435286115865581613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101019737913714821154108817 75764803435286115865581613)
          ·
            refine ⟨28411801288232293449593105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75764803435286115865581613 28411801288232293449593105)
            ·
              refine ⟨21308850966174220087194829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28411801288232293449593105 21308850966174220087194829)
              ·
                refine ⟨7990819112315332532698061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21308850966174220087194829 7990819112315332532698061)
                ·
                  refine ⟨2996557167118249699761773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7990819112315332532698061 2996557167118249699761773)
                  ·
                    refine ⟨1123708937669343637410665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996557167118249699761773 1123708937669343637410665)
                    ·
                      rfl

theorem cell22_3282623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_3282623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282623 prefixEnd_3282623 := by exact prefixLift 3282623
  have htrace : WordTrace (prefixWord ++ tailWord_3282623) baseStart_3282623 baseEnd_3282623 := by
    simpa [prefixWord, tailWord_3282623, baseEnd_3282623] using wordTrace_append hprefix tailTrace_3282623
  have hstable : (prefixWord ++ tailWord_3282623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282623).length < 2 ^ (prefixWord ++ tailWord_3282623).sum := by decide
  have hdescent : baseEnd_3282623 < baseStart_3282623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282698 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_3282698 : Nat := 118140960795 + 3282698 * 2 ^ 59
def prefixEnd_3282698 : Nat := 4983230072969 + 3 ^ 40 * 3282698 * 2
def baseEnd_3282698 : Nat := 374578203900689480595145

theorem tailTrace_3282698 : CollatzResearch.WordTrace tailWord_3282698 prefixEnd_3282698 374578203900689480595145 := by
  unfold tailWord_3282698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29932458065338315257166187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79819888174235507352443165 29932458065338315257166187)
  ·
    refine ⟨44898687098007472885749281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29932458065338315257166187 44898687098007472885749281)
    ·
      refine ⟨33674015323505604664311961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44898687098007472885749281 33674015323505604664311961)
      ·
        refine ⟨25255511492629203498233971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33674015323505604664311961 25255511492629203498233971)
        ·
          refine ⟨37883267238943805247350957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25255511492629203498233971 37883267238943805247350957)
          ·
            refine ⟨14206225214603926967756609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37883267238943805247350957 14206225214603926967756609)
            ·
              refine ⟨10654668910952945225817457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14206225214603926967756609 10654668910952945225817457)
              ·
                refine ⟨7991001683214708919363093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10654668910952945225817457 7991001683214708919363093)
                ·
                  refine ⟨374578203900689480595145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7991001683214708919363093 374578203900689480595145)
                  ·
                    rfl

theorem cell22_3282698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_3282698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282698 prefixEnd_3282698 := by exact prefixLift 3282698
  have htrace : WordTrace (prefixWord ++ tailWord_3282698) baseStart_3282698 baseEnd_3282698 := by
    simpa [prefixWord, tailWord_3282698, baseEnd_3282698] using wordTrace_append hprefix tailTrace_3282698
  have hstable : (prefixWord ++ tailWord_3282698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282698).length < 2 ^ (prefixWord ++ tailWord_3282698).sum := by decide
  have hdescent : baseEnd_3282698 < baseStart_3282698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282732 : List Nat := [2, 2, 1, 1, 1, 6, 3, 2, 4]
def baseStart_3282732 : Nat := 118140960795 + 3282732 * 2 ^ 59
def prefixEnd_3282732 : Nat := 4983230072969 + 3 ^ 40 * 3282732 * 2
def baseEnd_3282732 : Nat := 374582083532301228811777

theorem tailTrace_3282732 : CollatzResearch.WordTrace tailWord_3282732 prefixEnd_3282732 374582083532301228811777 := by
  unfold tailWord_3282732
  simp only [CollatzResearch.WordTrace]
  refine ⟨59865536171615042417701225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79820714895486723223601633 59865536171615042417701225)
  ·
    refine ⟨44899152128711281813275919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59865536171615042417701225 44899152128711281813275919)
    ·
      refine ⟨67348728193066922719913879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44899152128711281813275919 67348728193066922719913879)
      ·
        refine ⟨101023092289600384079870819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67348728193066922719913879 101023092289600384079870819)
        ·
          refine ⟨151534638434400576119806229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101023092289600384079870819 151534638434400576119806229)
          ·
            refine ⟨7103186176612527005615917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151534638434400576119806229 7103186176612527005615917)
            ·
              refine ⟨2663694816229697627105969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7103186176612527005615917 2663694816229697627105969)
              ·
                refine ⟨1997771112172273220329477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663694816229697627105969 1997771112172273220329477)
                ·
                  refine ⟨374582083532301228811777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997771112172273220329477 374582083532301228811777)
                  ·
                    rfl

theorem cell22_3282732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_3282732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282732 prefixEnd_3282732 := by exact prefixLift 3282732
  have htrace : WordTrace (prefixWord ++ tailWord_3282732) baseStart_3282732 baseEnd_3282732 := by
    simpa [prefixWord, tailWord_3282732, baseEnd_3282732] using wordTrace_append hprefix tailTrace_3282732
  have hstable : (prefixWord ++ tailWord_3282732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282732).length < 2 ^ (prefixWord ++ tailWord_3282732).sum := by decide
  have hdescent : baseEnd_3282732 < baseStart_3282732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282794 : List Nat := [3, 1, 3, 4, 2, 1, 1, 7]
def baseStart_3282794 : Nat := 118140960795 + 3282794 * 2 ^ 59
def prefixEnd_3282794 : Nat := 4983230072969 + 3 ^ 40 * 3282794 * 2
def baseEnd_3282794 : Nat := 124863052718217354598349

theorem tailTrace_3282794 : CollatzResearch.WordTrace tailWord_3282794 prefixEnd_3282794 124863052718217354598349 := by
  unfold tailWord_3282794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933333417251367356039859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79822222446003646282772957 29933333417251367356039859)
  ·
    refine ⟨44900000125877051034059789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29933333417251367356039859 44900000125877051034059789)
    ·
      refine ⟨16837500047203894137772421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44900000125877051034059789 16837500047203894137772421)
      ·
        refine ⟨3157031258850730150832329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16837500047203894137772421 3157031258850730150832329)
        ·
          refine ⟨2367773444138047613124247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3157031258850730150832329 2367773444138047613124247)
          ·
            refine ⟨3551660166207071419686371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367773444138047613124247 3551660166207071419686371)
            ·
              refine ⟨5327490249310607129529557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3551660166207071419686371 5327490249310607129529557)
              ·
                refine ⟨124863052718217354598349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5327490249310607129529557 124863052718217354598349)
                ·
                  rfl

theorem cell22_3282794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_3282794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282794 prefixEnd_3282794 := by exact prefixLift 3282794
  have htrace : WordTrace (prefixWord ++ tailWord_3282794) baseStart_3282794 baseEnd_3282794 := by
    simpa [prefixWord, tailWord_3282794, baseEnd_3282794] using wordTrace_append hprefix tailTrace_3282794
  have hstable : (prefixWord ++ tailWord_3282794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282794).length < 2 ^ (prefixWord ++ tailWord_3282794).sum := by decide
  have hdescent : baseEnd_3282794 < baseStart_3282794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282805 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 5]
def baseStart_3282805 : Nat := 118140960795 + 3282805 * 2 ^ 59
def prefixEnd_3282805 : Nat := 4983230072969 + 3 ^ 40 * 3282805 * 2
def baseEnd_3282805 : Nat := 374590413329585276453369

theorem tailTrace_3282805 : CollatzResearch.WordTrace tailWord_3282805 prefixEnd_3282805 374590413329585276453369 := by
  unfold tailWord_3282805
  simp only [CollatzResearch.WordTrace]
  refine ⟨119733734871965618302809869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79822489914643745535206579 119733734871965618302809869)
  ·
    refine ⟨44900150576987106863553701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119733734871965618302809869 44900150576987106863553701)
    ·
      refine ⟨8418778233185082536916319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44900150576987106863553701 8418778233185082536916319)
      ·
        refine ⟨12628167349777623805374479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8418778233185082536916319 12628167349777623805374479)
        ·
          refine ⟨18942251024666435708061719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12628167349777623805374479 18942251024666435708061719)
          ·
            refine ⟨28413376536999653562092579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18942251024666435708061719 28413376536999653562092579)
            ·
              refine ⟨42620064805499480343138869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28413376536999653562092579 42620064805499480343138869)
              ·
                refine ⟨3995631075515576282169269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42620064805499480343138869 3995631075515576282169269)
                ·
                  refine ⟨374590413329585276453369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3995631075515576282169269 374590413329585276453369)
                  ·
                    rfl

theorem cell22_3282805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_3282805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282805 prefixEnd_3282805 := by exact prefixLift 3282805
  have htrace : WordTrace (prefixWord ++ tailWord_3282805) baseStart_3282805 baseEnd_3282805 := by
    simpa [prefixWord, tailWord_3282805, baseEnd_3282805] using wordTrace_append hprefix tailTrace_3282805
  have hstable : (prefixWord ++ tailWord_3282805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282805).length < 2 ^ (prefixWord ++ tailWord_3282805).sum := by decide
  have hdescent : baseEnd_3282805 < baseStart_3282805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282826 : List Nat := [3, 1, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_3282826 : Nat := 118140960795 + 3282826 * 2 ^ 59
def prefixEnd_3282826 : Nat := 4983230072969 + 3 ^ 40 * 3282826 * 2
def baseEnd_3282826 : Nat := 1123778428717918774585043

theorem tailTrace_3282826 : CollatzResearch.WordTrace tailWord_3282826 prefixEnd_3282826 1123778428717918774585043 := by
  unfold tailWord_3282826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933625201222384722331083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79823000536593025926216221 29933625201222384722331083)
  ·
    refine ⟨44900437801833577083496625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29933625201222384722331083 44900437801833577083496625)
    ·
      refine ⟨33675328351375182812622469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44900437801833577083496625 33675328351375182812622469)
      ·
        refine ⟨6314124065882846777366713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33675328351375182812622469 6314124065882846777366713)
        ·
          refine ⟨4735593049412135083025035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6314124065882846777366713 4735593049412135083025035)
          ·
            refine ⟨7103389574118202624537553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735593049412135083025035 7103389574118202624537553)
            ·
              refine ⟨5327542180588651968403165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7103389574118202624537553 5327542180588651968403165)
              ·
                refine ⟨1997828317720744488151187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5327542180588651968403165 1997828317720744488151187)
                ·
                  refine ⟨2996742476581116732226781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997828317720744488151187 2996742476581116732226781)
                  ·
                    refine ⟨1123778428717918774585043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996742476581116732226781 1123778428717918774585043)
                    ·
                      rfl

theorem cell22_3282826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_3282826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282826 prefixEnd_3282826 := by exact prefixLift 3282826
  have htrace : WordTrace (prefixWord ++ tailWord_3282826) baseStart_3282826 baseEnd_3282826 := by
    simpa [prefixWord, tailWord_3282826, baseEnd_3282826] using wordTrace_append hprefix tailTrace_3282826
  have hstable : (prefixWord ++ tailWord_3282826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282826).length < 2 ^ (prefixWord ++ tailWord_3282826).sum := by decide
  have hdescent : baseEnd_3282826 < baseStart_3282826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282856 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 5]
def baseStart_3282856 : Nat := 118140960795 + 3282856 * 2 ^ 59
def prefixEnd_3282856 : Nat := 4983230072969 + 3 ^ 40 * 3282856 * 2
def baseEnd_3282856 : Nat := 374596232777002898778317

theorem tailTrace_3282856 : CollatzResearch.WordTrace tailWord_3282856 prefixEnd_3282856 374596232777002898778317 := by
  unfold tailWord_3282856
  simp only [CollatzResearch.WordTrace]
  refine ⟨59867797497390427006458211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79823729996520569341944281 59867797497390427006458211)
  ·
    refine ⟨89801696246085640509687317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59867797497390427006458211 89801696246085640509687317)
    ·
      refine ⟨4209454511535264398891593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89801696246085640509687317 4209454511535264398891593)
      ·
        refine ⟨3157090883651448299168695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4209454511535264398891593 3157090883651448299168695)
        ·
          refine ⟨4735636325477172448753043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157090883651448299168695 4735636325477172448753043)
          ·
            refine ⟨7103454488215758673129565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735636325477172448753043 7103454488215758673129565)
            ·
              refine ⟨2663795433080909502423587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7103454488215758673129565 2663795433080909502423587)
              ·
                refine ⟨3995693149621364253635381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663795433080909502423587 3995693149621364253635381)
                ·
                  refine ⟨374596232777002898778317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3995693149621364253635381 374596232777002898778317)
                  ·
                    rfl

theorem cell22_3282856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_3282856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282856 prefixEnd_3282856 := by exact prefixLift 3282856
  have htrace : WordTrace (prefixWord ++ tailWord_3282856) baseStart_3282856 baseEnd_3282856 := by
    simpa [prefixWord, tailWord_3282856, baseEnd_3282856] using wordTrace_append hprefix tailTrace_3282856
  have hstable : (prefixWord ++ tailWord_3282856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282856).length < 2 ^ (prefixWord ++ tailWord_3282856).sum := by decide
  have hdescent : baseEnd_3282856 < baseStart_3282856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282863 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 3, 6]
def baseStart_3282863 : Nat := 118140960795 + 3282863 * 2 ^ 59
def prefixEnd_3282863 : Nat := 4983230072969 + 3 ^ 40 * 3282863 * 2
def baseEnd_3282863 : Nat := 1123791094574063011409929

theorem tailTrace_3282863 : CollatzResearch.WordTrace tailWord_3282863 prefixEnd_3282863 1123791094574063011409929 := by
  unfold tailWord_3282863
  simp only [CollatzResearch.WordTrace]
  refine ⟨119735850305755494208421243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79823900203836996138947495 119735850305755494208421243)
  ·
    refine ⟨179603775458633241312631865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119735850305755494208421243 179603775458633241312631865)
    ·
      refine ⟨134702831593974930984473899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179603775458633241312631865 134702831593974930984473899)
      ·
        refine ⟨202054247390962396476710849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134702831593974930984473899 202054247390962396476710849)
        ·
          refine ⟨151540685543221797357533137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202054247390962396476710849 151540685543221797357533137)
          ·
            refine ⟨113655514157416348018149853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151540685543221797357533137 113655514157416348018149853)
            ·
              refine ⟨42620817809031130506806195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113655514157416348018149853 42620817809031130506806195)
              ·
                refine ⟨63931226713546695760209293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42620817809031130506806195 63931226713546695760209293)
                ·
                  refine ⟨23974210017580010910078485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63931226713546695760209293 23974210017580010910078485)
                  ·
                    refine ⟨1123791094574063011409929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23974210017580010910078485 1123791094574063011409929)
                    ·
                      rfl

theorem cell22_3282863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_3282863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282863 prefixEnd_3282863 := by exact prefixLift 3282863
  have htrace : WordTrace (prefixWord ++ tailWord_3282863) baseStart_3282863 baseEnd_3282863 := by
    simpa [prefixWord, tailWord_3282863, baseEnd_3282863] using wordTrace_append hprefix tailTrace_3282863
  have hstable : (prefixWord ++ tailWord_3282863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282863).length < 2 ^ (prefixWord ++ tailWord_3282863).sum := by decide
  have hdescent : baseEnd_3282863 < baseStart_3282863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282880 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_3282880 : Nat := 118140960795 + 3282880 * 2 ^ 59
def prefixEnd_3282880 : Nat := 4983230072969 + 3 ^ 40 * 3282880 * 2
def baseEnd_3282880 : Nat := 1123796914021480633734877

theorem tailTrace_3282880 : CollatzResearch.WordTrace tailWord_3282880 prefixEnd_3282880 1123796914021480633734877 := by
  unfold tailWord_3282880
  simp only [CollatzResearch.WordTrace]
  refine ⟨59868235173346953055895047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79824313564462604074526729 59868235173346953055895047)
  ·
    refine ⟨89802352760020429583842571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59868235173346953055895047 89802352760020429583842571)
    ·
      refine ⟨134703529140030644375763857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89802352760020429583842571 134703529140030644375763857)
      ·
        refine ⟨101027646855022983281822893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134703529140030644375763857 101027646855022983281822893)
        ·
          refine ⟨37885367570633618730683585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101027646855022983281822893 37885367570633618730683585)
          ·
            refine ⟨28414025677975214048012689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37885367570633618730683585 28414025677975214048012689)
            ·
              refine ⟨21310519258481410536009517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28414025677975214048012689 21310519258481410536009517)
              ·
                refine ⟨7991444721930528951003569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21310519258481410536009517 7991444721930528951003569)
                ·
                  refine ⟨5993583541447896713252677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7991444721930528951003569 5993583541447896713252677)
                  ·
                    refine ⟨1123796914021480633734877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993583541447896713252677 1123796914021480633734877)
                    ·
                      rfl

theorem cell22_3282880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_3282880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282880 prefixEnd_3282880 := by exact prefixLift 3282880
  have htrace : WordTrace (prefixWord ++ tailWord_3282880) baseStart_3282880 baseEnd_3282880 := by
    simpa [prefixWord, tailWord_3282880, baseEnd_3282880] using wordTrace_append hprefix tailTrace_3282880
  have hstable : (prefixWord ++ tailWord_3282880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282880).length < 2 ^ (prefixWord ++ tailWord_3282880).sum := by decide
  have hdescent : baseEnd_3282880 < baseStart_3282880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282955 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 2, 5]
def baseStart_3282955 : Nat := 118140960795 + 3282955 * 2 ^ 59
def prefixEnd_3282955 : Nat := 4983230072969 + 3 ^ 40 * 3282955 * 2
def baseEnd_3282955 : Nat := 1123822588054205438109647

theorem tailTrace_3282955 : CollatzResearch.WordTrace tailWord_3282955 prefixEnd_3282955 1123822588054205438109647 := by
  unfold tailWord_3282955
  simp only [CollatzResearch.WordTrace]
  refine ⟨119739205821422193920770319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79826137214281462613846879 119739205821422193920770319)
  ·
    refine ⟨179608808732133290881155479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119739205821422193920770319 179608808732133290881155479)
    ·
      refine ⟨269413213098199936321733219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179608808732133290881155479 269413213098199936321733219)
      ·
        refine ⟨404119819647299904482599829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269413213098199936321733219 404119819647299904482599829)
        ·
          refine ⟨18943116545967183022621867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 404119819647299904482599829 18943116545967183022621867)
          ·
            refine ⟨28414674818950774533932801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18943116545967183022621867 28414674818950774533932801)
            ·
              refine ⟨21311006114213080900449601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28414674818950774533932801 21311006114213080900449601)
              ·
                refine ⟨15983254585659810675337201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21311006114213080900449601 15983254585659810675337201)
                ·
                  refine ⟨11987440939244858006502901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15983254585659810675337201 11987440939244858006502901)
                  ·
                    refine ⟨1123822588054205438109647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11987440939244858006502901 1123822588054205438109647)
                    ·
                      rfl

theorem cell22_3282955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_3282955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282955 prefixEnd_3282955 := by exact prefixLift 3282955
  have htrace : WordTrace (prefixWord ++ tailWord_3282955) baseStart_3282955 baseEnd_3282955 := by
    simpa [prefixWord, tailWord_3282955, baseEnd_3282955] using wordTrace_append hprefix tailTrace_3282955
  have hstable : (prefixWord ++ tailWord_3282955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282955).length < 2 ^ (prefixWord ++ tailWord_3282955).sum := by decide
  have hdescent : baseEnd_3282955 < baseStart_3282955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3282972 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3282972 : Nat := 118140960795 + 3282972 * 2 ^ 59
def prefixEnd_3282972 : Nat := 4983230072969 + 3 ^ 40 * 3282972 * 2
def baseEnd_3282972 : Nat := 1123828407501623060434595

theorem tailTrace_3282972 : CollatzResearch.WordTrace tailWord_3282972 prefixEnd_3282972 1123828407501623060434595 := by
  unfold tailWord_3282972
  simp only [CollatzResearch.WordTrace]
  refine ⟨59869912931180302912069585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79826550574907070549426113 59869912931180302912069585)
  ·
    refine ⟨44902434698385227184052189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59869912931180302912069585 44902434698385227184052189)
    ·
      refine ⟨16838413011894460194019571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44902434698385227184052189 16838413011894460194019571)
      ·
        refine ⟨25257619517841690291029357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16838413011894460194019571 25257619517841690291029357)
        ·
          refine ⟨9471607319190633859136009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25257619517841690291029357 9471607319190633859136009)
          ·
            refine ⟨7103705489392975394352007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9471607319190633859136009 7103705489392975394352007)
            ·
              refine ⟨10655558234089463091528011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103705489392975394352007 10655558234089463091528011)
              ·
                refine ⟨15983337351134194637292017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10655558234089463091528011 15983337351134194637292017)
                ·
                  refine ⟨11987503013350645977969013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15983337351134194637292017 11987503013350645977969013)
                  ·
                    refine ⟨1123828407501623060434595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11987503013350645977969013 1123828407501623060434595)
                    ·
                      rfl

theorem cell22_3282972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3282972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3282972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3282972 prefixEnd_3282972 := by exact prefixLift 3282972
  have htrace : WordTrace (prefixWord ++ tailWord_3282972) baseStart_3282972 baseEnd_3282972 := by
    simpa [prefixWord, tailWord_3282972, baseEnd_3282972] using wordTrace_append hprefix tailTrace_3282972
  have hstable : (prefixWord ++ tailWord_3282972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3282972).length < 2 ^ (prefixWord ++ tailWord_3282972).sum := by decide
  have hdescent : baseEnd_3282972 < baseStart_3282972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3282972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283017 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 4, 3]
def baseStart_3283017 : Nat := 118140960795 + 3283017 * 2 ^ 59
def prefixEnd_3283017 : Nat := 4983230072969 + 3 ^ 40 * 3283017 * 2
def baseEnd_3283017 : Nat := 1123843811921257943059457

theorem tailTrace_3283017 : CollatzResearch.WordTrace tailWord_3283017 prefixEnd_3283017 1123843811921257943059457 := by
  unfold tailWord_3283017
  simp only [CollatzResearch.WordTrace]
  refine ⟨119741467147197578509527305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79827644764798385673018203 119741467147197578509527305)
  ·
    refine ⟨89806100360398183882145479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119741467147197578509527305 89806100360398183882145479)
    ·
      refine ⟨134709150540597275823218219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89806100360398183882145479 134709150540597275823218219)
      ·
        refine ⟨202063725810895913734827329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134709150540597275823218219 202063725810895913734827329)
        ·
          refine ⟨151547794358171935301120497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202063725810895913734827329 151547794358171935301120497)
          ·
            refine ⟨113660845768628951475840373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151547794358171935301120497 113660845768628951475840373)
            ·
              refine ⟨10655704290808964200860035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113660845768628951475840373 10655704290808964200860035)
              ·
                refine ⟨15983556436213446301290053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10655704290808964200860035 15983556436213446301290053)
                ·
                  refine ⟨2996916831790021181491885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15983556436213446301290053 2996916831790021181491885)
                  ·
                    refine ⟨1123843811921257943059457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996916831790021181491885 1123843811921257943059457)
                    ·
                      rfl

theorem cell22_3283017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_3283017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283017 prefixEnd_3283017 := by exact prefixLift 3283017
  have htrace : WordTrace (prefixWord ++ tailWord_3283017) baseStart_3283017 baseEnd_3283017 := by
    simpa [prefixWord, tailWord_3283017, baseEnd_3283017] using wordTrace_append hprefix tailTrace_3283017
  have hstable : (prefixWord ++ tailWord_3283017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283017).length < 2 ^ (prefixWord ++ tailWord_3283017).sum := by decide
  have hdescent : baseEnd_3283017 < baseStart_3283017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283079 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 3, 3]
def baseStart_3283079 : Nat := 118140960795 + 3283079 * 2 ^ 59
def prefixEnd_3283079 : Nat := 4983230072969 + 3 ^ 40 * 3283079 * 2
def baseEnd_3283079 : Nat := 1123865035788310448009267

theorem tailTrace_3283079 : CollatzResearch.WordTrace tailWord_3283079 prefixEnd_3283079 1123865035788310448009267 := by
  unfold tailWord_3283079
  simp only [CollatzResearch.WordTrace]
  refine ⟨119743728472972963098284291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79829152315315308732189527 119743728472972963098284291)
  ·
    refine ⟨179615592709459444647426437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119743728472972963098284291 179615592709459444647426437)
    ·
      refine ⟨33677923633023645871392457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179615592709459444647426437 33677923633023645871392457)
      ·
        refine ⟨25258442724767734403544343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33677923633023645871392457 25258442724767734403544343)
        ·
          refine ⟨37887664087151601605316515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25258442724767734403544343 37887664087151601605316515)
          ·
            refine ⟨56831496130727402407974773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37887664087151601605316515 56831496130727402407974773)
            ·
              refine ⟨5327952762255693975747635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56831496130727402407974773 5327952762255693975747635)
              ·
                refine ⟨7991929143383540963621453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5327952762255693975747635 7991929143383540963621453)
                ·
                  refine ⟨2996973428768827861358045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7991929143383540963621453 2996973428768827861358045)
                  ·
                    refine ⟨1123865035788310448009267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996973428768827861358045 1123865035788310448009267)
                    ·
                      rfl

theorem cell22_3283079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_3283079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283079 prefixEnd_3283079 := by exact prefixLift 3283079
  have htrace : WordTrace (prefixWord ++ tailWord_3283079) baseStart_3283079 baseEnd_3283079 := by
    simpa [prefixWord, tailWord_3283079, baseEnd_3283079] using wordTrace_append hprefix tailTrace_3283079
  have hstable : (prefixWord ++ tailWord_3283079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283079).length < 2 ^ (prefixWord ++ tailWord_3283079).sum := by decide
  have hdescent : baseEnd_3283079 < baseStart_3283079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283154 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_3283154 : Nat := 118140960795 + 3283154 * 2 ^ 59
def prefixEnd_3283154 : Nat := 4983230072969 + 3 ^ 40 * 3283154 * 2
def baseEnd_3283154 : Nat := 374630236607011750794679

theorem tailTrace_3283154 : CollatzResearch.WordTrace tailWord_3283154 prefixEnd_3283154 374630236607011750794679 := by
  unfold tailWord_3283154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29936615986925312726816129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79830975965134167271509677 29936615986925312726816129)
  ·
    refine ⟨22452461990193984545112097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29936615986925312726816129 22452461990193984545112097)
    ·
      refine ⟨16839346492645488408834073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22452461990193984545112097 16839346492645488408834073)
      ·
        refine ⟨12629509869484116306625555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16839346492645488408834073 12629509869484116306625555)
        ·
          refine ⟨18944264804226174459938333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12629509869484116306625555 18944264804226174459938333)
          ·
            refine ⟨7104099301584815422476875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18944264804226174459938333 7104099301584815422476875)
            ·
              refine ⟨10656148952377223133715313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104099301584815422476875 10656148952377223133715313)
              ·
                refine ⟨7992111714282917350286485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10656148952377223133715313 7992111714282917350286485)
                ·
                  refine ⟨374630236607011750794679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7992111714282917350286485 374630236607011750794679)
                  ·
                    rfl

theorem cell22_3283154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_3283154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283154 prefixEnd_3283154 := by exact prefixLift 3283154
  have htrace : WordTrace (prefixWord ++ tailWord_3283154) baseStart_3283154 baseEnd_3283154 := by
    simpa [prefixWord, tailWord_3283154, baseEnd_3283154] using wordTrace_append hprefix tailTrace_3283154
  have hstable : (prefixWord ++ tailWord_3283154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283154).length < 2 ^ (prefixWord ++ tailWord_3283154).sum := by decide
  have hdescent : baseEnd_3283154 < baseStart_3283154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283169 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 4, 3]
def baseStart_3283169 : Nat := 118140960795 + 3283169 * 2 ^ 59
def prefixEnd_3283169 : Nat := 4983230072969 + 3 ^ 40 * 3283169 * 2
def baseEnd_3283169 : Nat := 1123895844627580213258991

theorem tailTrace_3283169 : CollatzResearch.WordTrace tailWord_3283169 prefixEnd_3283169 1123895844627580213258991 := by
  unfold tailWord_3283169
  simp only [CollatzResearch.WordTrace]
  refine ⟨119747011042646908469060561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79831340695097938979373707 119747011042646908469060561)
  ·
    refine ⟨89810258281985181351795421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119747011042646908469060561 89810258281985181351795421)
    ·
      refine ⟨33678846855744443006923283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89810258281985181351795421 33678846855744443006923283)
      ·
        refine ⟨50518270283616664510384925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33678846855744443006923283 50518270283616664510384925)
        ·
          refine ⟨18944351356356249191394347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50518270283616664510384925 18944351356356249191394347)
          ·
            refine ⟨28416527034534373787091521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18944351356356249191394347 28416527034534373787091521)
            ·
              refine ⟨21312395275900780340318641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28416527034534373787091521 21312395275900780340318641)
              ·
                refine ⟨15984296456925585255238981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21312395275900780340318641 15984296456925585255238981)
                ·
                  refine ⟨2997055585673547235357309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15984296456925585255238981 2997055585673547235357309)
                  ·
                    refine ⟨1123895844627580213258991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997055585673547235357309 1123895844627580213258991)
                    ·
                      rfl

theorem cell22_3283169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_3283169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283169 prefixEnd_3283169 := by exact prefixLift 3283169
  have htrace : WordTrace (prefixWord ++ tailWord_3283169) baseStart_3283169 baseEnd_3283169 := by
    simpa [prefixWord, tailWord_3283169, baseEnd_3283169] using wordTrace_append hprefix tailTrace_3283169
  have hstable : (prefixWord ++ tailWord_3283169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283169).length < 2 ^ (prefixWord ++ tailWord_3283169).sum := by decide
  have hdescent : baseEnd_3283169 < baseStart_3283169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283173 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_3283173 : Nat := 118140960795 + 3283173 * 2 ^ 59
def prefixEnd_3283173 : Nat := 4983230072969 + 3 ^ 40 * 3283173 * 2
def baseEnd_3283173 : Nat := 1123897213909325536158979

theorem tailTrace_3283173 : CollatzResearch.WordTrace tailWord_3283173 prefixEnd_3283173 1123897213909325536158979 := by
  unfold tailWord_3283173
  simp only [CollatzResearch.WordTrace]
  refine ⟨119747156934632417152206173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79831437956421611434804115 119747156934632417152206173)
  ·
    refine ⟨44905183850487156432077315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119747156934632417152206173 44905183850487156432077315)
    ·
      refine ⟨67357775775730734648115973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44905183850487156432077315 67357775775730734648115973)
      ·
        refine ⟨12629582957949512746521745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67357775775730734648115973 12629582957949512746521745)
        ·
          refine ⟨9472187218462134559891309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12629582957949512746521745 9472187218462134559891309)
          ·
            refine ⟨3552070206923300459959241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9472187218462134559891309 3552070206923300459959241)
            ·
              refine ⟨2664052655192475344969431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3552070206923300459959241 2664052655192475344969431)
              ·
                refine ⟨3996078982788713017454147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664052655192475344969431 3996078982788713017454147)
                ·
                  refine ⟨5994118474183069526181221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996078982788713017454147 5994118474183069526181221)
                  ·
                    refine ⟨1123897213909325536158979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994118474183069526181221 1123897213909325536158979)
                    ·
                      rfl

theorem cell22_3283173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_3283173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283173 prefixEnd_3283173 := by exact prefixLift 3283173
  have htrace : WordTrace (prefixWord ++ tailWord_3283173) baseStart_3283173 baseEnd_3283173 := by
    simpa [prefixWord, tailWord_3283173, baseEnd_3283173] using wordTrace_append hprefix tailTrace_3283173
  have hstable : (prefixWord ++ tailWord_3283173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283173).length < 2 ^ (prefixWord ++ tailWord_3283173).sum := by decide
  have hdescent : baseEnd_3283173 < baseStart_3283173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283186 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_3283186 : Nat := 118140960795 + 3283186 * 2 ^ 59
def prefixEnd_3283186 : Nat := 4983230072969 + 3 ^ 40 * 3283186 * 2
def baseEnd_3283186 : Nat := 1123901664074997835583939

theorem tailTrace_3283186 : CollatzResearch.WordTrace tailWord_3283186 prefixEnd_3283186 1123901664074997835583939 := by
  unfold tailWord_3283186
  simp only [CollatzResearch.WordTrace]
  refine ⟨29936907770896330093107353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79831754055723546914952941 29936907770896330093107353)
  ·
    refine ⟨22452680828172247569830515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29936907770896330093107353 22452680828172247569830515)
    ·
      refine ⟨33679021242258371354745773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22452680828172247569830515 33679021242258371354745773)
      ·
        refine ⟨12629632965846889258029665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33679021242258371354745773 12629632965846889258029665)
        ·
          refine ⟨9472224724385166943522249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12629632965846889258029665 9472224724385166943522249)
          ·
            refine ⟨7104168543288875207641687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9472224724385166943522249 7104168543288875207641687)
            ·
              refine ⟨10656252814933312811462531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104168543288875207641687 10656252814933312811462531)
              ·
                refine ⟨15984379222399969217193797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10656252814933312811462531 15984379222399969217193797)
                ·
                  refine ⟨2997071104199994228223837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15984379222399969217193797 2997071104199994228223837)
                  ·
                    refine ⟨1123901664074997835583939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997071104199994228223837 1123901664074997835583939)
                    ·
                      rfl

theorem cell22_3283186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_3283186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283186 prefixEnd_3283186 := by exact prefixLift 3283186
  have htrace : WordTrace (prefixWord ++ tailWord_3283186) baseStart_3283186 baseEnd_3283186 := by
    simpa [prefixWord, tailWord_3283186, baseEnd_3283186] using wordTrace_append hprefix tailTrace_3283186
  have hstable : (prefixWord ++ tailWord_3283186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283186).length < 2 ^ (prefixWord ++ tailWord_3283186).sum := by decide
  have hdescent : baseEnd_3283186 < baseStart_3283186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283227 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 7]
def baseStart_3283227 : Nat := 118140960795 + 3283227 * 2 ^ 59
def prefixEnd_3283227 : Nat := 4983230072969 + 3 ^ 40 * 3283227 * 2
def baseEnd_3283227 : Nat := 374638566404295798436271

theorem tailTrace_3283227 : CollatzResearch.WordTrace tailWord_3283227 prefixEnd_3283227 374638566404295798436271 := by
  unfold tailWord_3283227
  simp only [CollatzResearch.WordTrace]
  refine ⟨119749126476436784374671935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79832750984291189583114623 119749126476436784374671935)
  ·
    refine ⟨179623689714655176562007903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119749126476436784374671935 179623689714655176562007903)
    ·
      refine ⟨269435534571982764843011855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179623689714655176562007903 269435534571982764843011855)
      ·
        refine ⟨404153301857974147264517783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269435534571982764843011855 404153301857974147264517783)
        ·
          refine ⟨606229952786961220896776675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404153301857974147264517783 606229952786961220896776675)
          ·
            refine ⟨909344929180441831345165013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606229952786961220896776675 909344929180441831345165013)
            ·
              refine ⟨21312771777666605422152305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 909344929180441831345165013 21312771777666605422152305)
              ·
                refine ⟨15984578833249954066614229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21312771777666605422152305 15984578833249954066614229)
                ·
                  refine ⟨374638566404295798436271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15984578833249954066614229 374638566404295798436271)
                  ·
                    rfl

theorem cell22_3283227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_3283227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283227 prefixEnd_3283227 := by exact prefixLift 3283227
  have htrace : WordTrace (prefixWord ++ tailWord_3283227) baseStart_3283227 baseEnd_3283227 := by
    simpa [prefixWord, tailWord_3283227, baseEnd_3283227] using wordTrace_append hprefix tailTrace_3283227
  have hstable : (prefixWord ++ tailWord_3283227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283227).length < 2 ^ (prefixWord ++ tailWord_3283227).sum := by decide
  have hdescent : baseEnd_3283227 < baseStart_3283227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283364 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_3283364 : Nat := 118140960795 + 3283364 * 2 ^ 59
def prefixEnd_3283364 : Nat := 4983230072969 + 3 ^ 40 * 3283364 * 2
def baseEnd_3283364 : Nat := 1123962597112664704633393

theorem tailTrace_3283364 : CollatzResearch.WordTrace tailWord_3283364 prefixEnd_3283364 1123962597112664704633393 := by
  unfold tailWord_3283364
  simp only [CollatzResearch.WordTrace]
  refine ⟨59877061638470228386204573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79836082184626971181606097 59877061638470228386204573)
  ·
    refine ⟨22453898114426335644826715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59877061638470228386204573 22453898114426335644826715)
    ·
      refine ⟨33680847171639503467240073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22453898114426335644826715 33680847171639503467240073)
      ·
        refine ⟨25260635378729627600430055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33680847171639503467240073 25260635378729627600430055)
        ·
          refine ⟨37890953068094441400645083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25260635378729627600430055 37890953068094441400645083)
          ·
            refine ⟨56836429602141662100967625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37890953068094441400645083 56836429602141662100967625)
            ·
              refine ⟨42627322201606246575725719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56836429602141662100967625 42627322201606246575725719)
              ·
                refine ⟨63940983302409369863588579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42627322201606246575725719 63940983302409369863588579)
                ·
                  refine ⟨95911474953614054795382869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63940983302409369863588579 95911474953614054795382869)
                  ·
                    refine ⟨1123962597112664704633393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95911474953614054795382869 1123962597112664704633393)
                    ·
                      rfl

theorem cell22_3283364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_3283364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283364 prefixEnd_3283364 := by exact prefixLift 3283364
  have htrace : WordTrace (prefixWord ++ tailWord_3283364) baseStart_3283364 baseEnd_3283364 := by
    simpa [prefixWord, tailWord_3283364, baseEnd_3283364] using wordTrace_append hprefix tailTrace_3283364
  have hstable : (prefixWord ++ tailWord_3283364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283364).length < 2 ^ (prefixWord ++ tailWord_3283364).sum := by decide
  have hdescent : baseEnd_3283364 < baseStart_3283364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283400 : List Nat := [2, 1, 3, 1, 3, 2, 3, 3, 1, 3]
def baseStart_3283400 : Nat := 118140960795 + 3283400 * 2 ^ 59
def prefixEnd_3283400 : Nat := 4983230072969 + 3 ^ 40 * 3283400 * 2
def baseEnd_3283400 : Nat := 1123974920648372610733283

theorem tailTrace_3283400 : CollatzResearch.WordTrace tailWord_3283400 prefixEnd_3283400 1123974920648372610733283 := by
  unfold tailWord_3283400
  simp only [CollatzResearch.WordTrace]
  refine ⟨59877718152405017460359827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79836957536540023280479769 59877718152405017460359827)
  ·
    refine ⟨89816577228607526190539741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59877718152405017460359827 89816577228607526190539741)
    ·
      refine ⟨33681216460727822321452403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89816577228607526190539741 33681216460727822321452403)
      ·
        refine ⟨50521824691091733482178605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33681216460727822321452403 50521824691091733482178605)
        ·
          refine ⟨18945684259159400055816977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50521824691091733482178605 18945684259159400055816977)
          ·
            refine ⟨14209263194369550041862733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18945684259159400055816977 14209263194369550041862733)
            ·
              refine ⟨5328473697888581265698525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14209263194369550041862733 5328473697888581265698525)
              ·
                refine ⟨1998177636708217974636947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5328473697888581265698525 1998177636708217974636947)
                ·
                  refine ⟨2997266455062326961955421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998177636708217974636947 2997266455062326961955421)
                  ·
                    refine ⟨1123974920648372610733283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997266455062326961955421 1123974920648372610733283)
                    ·
                      rfl

theorem cell22_3283400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_3283400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283400 prefixEnd_3283400 := by exact prefixLift 3283400
  have htrace : WordTrace (prefixWord ++ tailWord_3283400) baseStart_3283400 baseEnd_3283400 := by
    simpa [prefixWord, tailWord_3283400, baseEnd_3283400] using wordTrace_append hprefix tailTrace_3283400
  have hstable : (prefixWord ++ tailWord_3283400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283400).length < 2 ^ (prefixWord ++ tailWord_3283400).sum := by decide
  have hdescent : baseEnd_3283400 < baseStart_3283400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283524 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3283524 : Nat := 118140960795 + 3283524 * 2 ^ 59
def prefixEnd_3283524 : Nat := 4983230072969 + 3 ^ 40 * 3283524 * 2
def baseEnd_3283524 : Nat := 1124017368382477620632903

theorem tailTrace_3283524 : CollatzResearch.WordTrace tailWord_3283524 prefixEnd_3283524 1124017368382477620632903 := by
  unfold tailWord_3283524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59879979478180402049116813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79839972637573869398822417 59879979478180402049116813)
  ·
    refine ⟨22454992304317650768418805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59879979478180402049116813 22454992304317650768418805)
    ·
      refine ⟨2105155528529779759539263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22454992304317650768418805 2105155528529779759539263)
      ·
        refine ⟨3157733292794669639308895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105155528529779759539263 3157733292794669639308895)
        ·
          refine ⟨4736599939192004458963343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157733292794669639308895 4736599939192004458963343)
          ·
            refine ⟨7104899908788006688445015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736599939192004458963343 7104899908788006688445015)
            ·
              refine ⟨10657349863182010032667523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104899908788006688445015 10657349863182010032667523)
              ·
                refine ⟨15986024794773015049001285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10657349863182010032667523 15986024794773015049001285)
                ·
                  refine ⟨2997379649019940321687741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15986024794773015049001285 2997379649019940321687741)
                  ·
                    refine ⟨1124017368382477620632903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997379649019940321687741 1124017368382477620632903)
                    ·
                      rfl

theorem cell22_3283524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3283524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283524 prefixEnd_3283524 := by exact prefixLift 3283524
  have htrace : WordTrace (prefixWord ++ tailWord_3283524) baseStart_3283524 baseEnd_3283524 := by
    simpa [prefixWord, tailWord_3283524, baseEnd_3283524] using wordTrace_append hprefix tailTrace_3283524
  have hstable : (prefixWord ++ tailWord_3283524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283524).length < 2 ^ (prefixWord ++ tailWord_3283524).sum := by decide
  have hdescent : baseEnd_3283524 < baseStart_3283524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283535 : List Nat := [1, 1, 2, 1, 1, 2, 6, 4, 1, 3]
def baseStart_3283535 : Nat := 118140960795 + 3283535 * 2 ^ 59
def prefixEnd_3283535 : Nat := 4983230072969 + 3 ^ 40 * 3283535 * 2
def baseEnd_3283535 : Nat := 1124021133907277258607869

theorem tailTrace_3283535 : CollatzResearch.WordTrace tailWord_3283535 prefixEnd_3283535 1124021133907277258607869 := by
  unfold tailWord_3283535
  simp only [CollatzResearch.WordTrace]
  refine ⟨119760360159320952976884059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79840240106213968651256039 119760360159320952976884059)
  ·
    refine ⟨179640540238981429465326089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119760360159320952976884059 179640540238981429465326089)
    ·
      refine ⟨134730405179236072098994567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179640540238981429465326089 134730405179236072098994567)
      ·
        refine ⟨202095607768854108148491851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134730405179236072098994567 202095607768854108148491851)
        ·
          refine ⟨303143411653281162222737777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202095607768854108148491851 303143411653281162222737777)
          ·
            refine ⟨227357558739960871667053333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303143411653281162222737777 227357558739960871667053333)
            ·
              refine ⟨10657385565935665859393125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 227357558739960871667053333 10657385565935665859393125)
              ·
                refine ⟨1998259793612937348636211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10657385565935665859393125 1998259793612937348636211)
                ·
                  refine ⟨2997389690419406022954317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998259793612937348636211 2997389690419406022954317)
                  ·
                    refine ⟨1124021133907277258607869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997389690419406022954317 1124021133907277258607869)
                    ·
                      rfl

theorem cell22_3283535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 3].length) (baseStart_3283535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283535 prefixEnd_3283535 := by exact prefixLift 3283535
  have htrace : WordTrace (prefixWord ++ tailWord_3283535) baseStart_3283535 baseEnd_3283535 := by
    simpa [prefixWord, tailWord_3283535, baseEnd_3283535] using wordTrace_append hprefix tailTrace_3283535
  have hstable : (prefixWord ++ tailWord_3283535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283535).length < 2 ^ (prefixWord ++ tailWord_3283535).sum := by decide
  have hdescent : baseEnd_3283535 < baseStart_3283535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283554 : List Nat := [3, 3, 2, 3, 2, 1, 2, 6]
def baseStart_3283554 : Nat := 118140960795 + 3283554 * 2 ^ 59
def prefixEnd_3283554 : Nat := 4983230072969 + 3 ^ 40 * 3283554 * 2
def baseEnd_3283554 : Nat := 124891959777285282486979

theorem tailTrace_3283554 : CollatzResearch.WordTrace tailWord_3283554 prefixEnd_3283554 124891959777285282486979 := by
  unfold tailWord_3283554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29940263286563029805456429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79840702097501412814550477 29940263286563029805456429)
  ·
    refine ⟨11227598732461136177046161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29940263286563029805456429 11227598732461136177046161)
    ·
      refine ⟨8420699049345852132784621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11227598732461136177046161 8420699049345852132784621)
      ·
        refine ⟨3157762143504694549794233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8420699049345852132784621 3157762143504694549794233)
        ·
          refine ⟨2368321607628520912345675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3157762143504694549794233 2368321607628520912345675)
          ·
            refine ⟨3552482411442781368518513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368321607628520912345675 3552482411442781368518513)
            ·
              refine ⟨2664361808582086026388885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3552482411442781368518513 2664361808582086026388885)
              ·
                refine ⟨124891959777285282486979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2664361808582086026388885 124891959777285282486979)
                ·
                  rfl

theorem cell22_3283554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_3283554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283554 prefixEnd_3283554 := by exact prefixLift 3283554
  have htrace : WordTrace (prefixWord ++ tailWord_3283554) baseStart_3283554 baseEnd_3283554 := by
    simpa [prefixWord, tailWord_3283554, baseEnd_3283554] using wordTrace_append hprefix tailTrace_3283554
  have hstable : (prefixWord ++ tailWord_3283554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283554).length < 2 ^ (prefixWord ++ tailWord_3283554).sum := by decide
  have hdescent : baseEnd_3283554 < baseStart_3283554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283608 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_3283608 : Nat := 118140960795 + 3283608 * 2 ^ 59
def prefixEnd_3283608 : Nat := 4983230072969 + 3 ^ 40 * 3283608 * 2
def baseEnd_3283608 : Nat := 1124046123299129401532645

theorem tailTrace_3283608 : CollatzResearch.WordTrace tailWord_3283608 prefixEnd_3283608 1124046123299129401532645 := by
  unfold tailWord_3283608
  simp only [CollatzResearch.WordTrace]
  refine ⟨59881511344028243222145739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79842015125370990962860985 59881511344028243222145739)
  ·
    refine ⟨89822267016042364833218609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59881511344028243222145739 89822267016042364833218609)
    ·
      refine ⟨67366700262031773624913957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89822267016042364833218609 67366700262031773624913957)
      ·
        refine ⟨12631256299130957554671367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67366700262031773624913957 12631256299130957554671367)
        ·
          refine ⟨18946884448696436332007051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12631256299130957554671367 18946884448696436332007051)
          ·
            refine ⟨28420326673044654498010577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18946884448696436332007051 28420326673044654498010577)
            ·
              refine ⟨21315245004783490873507933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28420326673044654498010577 21315245004783490873507933)
              ·
                refine ⟨7993216876793809077565475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21315245004783490873507933 7993216876793809077565475)
                ·
                  refine ⟨11989825315190713616348213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993216876793809077565475 11989825315190713616348213)
                  ·
                    refine ⟨1124046123299129401532645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11989825315190713616348213 1124046123299129401532645)
                    ·
                      rfl

theorem cell22_3283608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_3283608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283608 prefixEnd_3283608 := by exact prefixLift 3283608
  have htrace : WordTrace (prefixWord ++ tailWord_3283608) baseStart_3283608 baseEnd_3283608 := by
    simpa [prefixWord, tailWord_3283608, baseEnd_3283608] using wordTrace_append hprefix tailTrace_3283608
  have hstable : (prefixWord ++ tailWord_3283608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283608).length < 2 ^ (prefixWord ++ tailWord_3283608).sum := by decide
  have hdescent : baseEnd_3283608 < baseStart_3283608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283612 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_3283612 : Nat := 118140960795 + 3283612 * 2 ^ 59
def prefixEnd_3283612 : Nat := 4983230072969 + 3 ^ 40 * 3283612 * 2
def baseEnd_3283612 : Nat := 1124047492580874724432633

theorem tailTrace_3283612 : CollatzResearch.WordTrace tailWord_3283612 prefixEnd_3283612 1124047492580874724432633 := by
  unfold tailWord_3283612
  simp only [CollatzResearch.WordTrace]
  refine ⟨59881584290020997563718545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79842112386694663418291393 59881584290020997563718545)
  ·
    refine ⟨44911188217515748172788909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59881584290020997563718545 44911188217515748172788909)
    ·
      refine ⟨16841695581568405564795841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44911188217515748172788909 16841695581568405564795841)
      ·
        refine ⟨12631271686176304173596881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16841695581568405564795841 12631271686176304173596881)
        ·
          refine ⟨9473453764632228130197661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12631271686176304173596881 9473453764632228130197661)
          ·
            refine ⟨3552545161737085548824123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9473453764632228130197661 3552545161737085548824123)
            ·
              refine ⟨5328817742605628323236185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552545161737085548824123 5328817742605628323236185)
              ·
                refine ⟨3996613306954221242427139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328817742605628323236185 3996613306954221242427139)
                ·
                  refine ⟨5994919960431331863640709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996613306954221242427139 5994919960431331863640709)
                  ·
                    refine ⟨1124047492580874724432633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994919960431331863640709 1124047492580874724432633)
                    ·
                      rfl

theorem cell22_3283612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_3283612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283612 prefixEnd_3283612 := by exact prefixLift 3283612
  have htrace : WordTrace (prefixWord ++ tailWord_3283612) baseStart_3283612 baseEnd_3283612 := by
    simpa [prefixWord, tailWord_3283612, baseEnd_3283612] using wordTrace_append hprefix tailTrace_3283612
  have hstable : (prefixWord ++ tailWord_3283612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283612).length < 2 ^ (prefixWord ++ tailWord_3283612).sum := by decide
  have hdescent : baseEnd_3283612 < baseStart_3283612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283835 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 5]
def baseStart_3283835 : Nat := 118140960795 + 3283835 * 2 ^ 59
def prefixEnd_3283835 : Nat := 4983230072969 + 3 ^ 40 * 3283835 * 2
def baseEnd_3283835 : Nat := 374707943346058825368983

theorem tailTrace_3283835 : CollatzResearch.WordTrace tailWord_3283835 prefixEnd_3283835 374707943346058825368983 := by
  unfold tailWord_3283835
  simp only [CollatzResearch.WordTrace]
  refine ⟨119771302058234104212804959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79847534705489402808536639 119771302058234104212804959)
  ·
    refine ⟨179656953087351156319207439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119771302058234104212804959 179656953087351156319207439)
    ·
      refine ⟨269485429631026734478811159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179656953087351156319207439 269485429631026734478811159)
      ·
        refine ⟨404228144446540101718216739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269485429631026734478811159 404228144446540101718216739)
        ·
          refine ⟨606342216669810152577325109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404228144446540101718216739 606342216669810152577325109)
          ·
            refine ⟨56844582812794701804124229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 606342216669810152577325109 56844582812794701804124229)
            ·
              refine ⟨10658359277399006588273293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56844582812794701804124229 10658359277399006588273293)
              ·
                refine ⟨3996884729024627470602485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10658359277399006588273293 3996884729024627470602485)
                ·
                  refine ⟨374707943346058825368983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3996884729024627470602485 374707943346058825368983)
                  ·
                    rfl

theorem cell22_3283835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 5].length) (baseStart_3283835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283835 prefixEnd_3283835 := by exact prefixLift 3283835
  have htrace : WordTrace (prefixWord ++ tailWord_3283835) baseStart_3283835 baseEnd_3283835 := by
    simpa [prefixWord, tailWord_3283835, baseEnd_3283835] using wordTrace_append hprefix tailTrace_3283835
  have hstable : (prefixWord ++ tailWord_3283835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283835).length < 2 ^ (prefixWord ++ tailWord_3283835).sum := by decide
  have hdescent : baseEnd_3283835 < baseStart_3283835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283940 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_3283940 : Nat := 118140960795 + 3283940 * 2 ^ 59
def prefixEnd_3283940 : Nat := 4983230072969 + 3 ^ 40 * 3283940 * 2
def baseEnd_3283940 : Nat := 1124159773683991202231627

theorem tailTrace_3283940 : CollatzResearch.WordTrace tailWord_3283940 prefixEnd_3283940 1124159773683991202231627 := by
  unfold tailWord_3283940
  simp only [CollatzResearch.WordTrace]
  refine ⟨59887565861426853572688637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79850087815235804763584849 59887565861426853572688637)
  ·
    refine ⟨22457837198035070089758239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59887565861426853572688637 22457837198035070089758239)
    ·
      refine ⟨33686755797052605134637359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22457837198035070089758239 33686755797052605134637359)
      ·
        refine ⟨50530133695578907701956039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33686755797052605134637359 50530133695578907701956039)
        ·
          refine ⟨75795200543368361552934059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50530133695578907701956039 75795200543368361552934059)
          ·
            refine ⟨113692800815052542329401089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75795200543368361552934059 113692800815052542329401089)
            ·
              refine ⟨85269600611289406747050817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113692800815052542329401089 85269600611289406747050817)
              ·
                refine ⟨63952200458467055060288113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85269600611289406747050817 63952200458467055060288113)
                ·
                  refine ⟨47964150343850291295216085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63952200458467055060288113 47964150343850291295216085)
                  ·
                    refine ⟨1124159773683991202231627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47964150343850291295216085 1124159773683991202231627)
                    ·
                      rfl

theorem cell22_3283940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_3283940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283940 prefixEnd_3283940 := by exact prefixLift 3283940
  have htrace : WordTrace (prefixWord ++ tailWord_3283940) baseStart_3283940 baseEnd_3283940 := by
    simpa [prefixWord, tailWord_3283940, baseEnd_3283940] using wordTrace_append hprefix tailTrace_3283940
  have hstable : (prefixWord ++ tailWord_3283940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283940).length < 2 ^ (prefixWord ++ tailWord_3283940).sum := by decide
  have hdescent : baseEnd_3283940 < baseStart_3283940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283946 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_3283946 : Nat := 118140960795 + 3283946 * 2 ^ 59
def prefixEnd_3283946 : Nat := 4983230072969 + 3 ^ 40 * 3283946 * 2
def baseEnd_3283946 : Nat := 1124161827606609186581609

theorem tailTrace_3283946 : CollatzResearch.WordTrace tailWord_3283946 prefixEnd_3283946 1124161827606609186581609 := by
  unfold tailWord_3283946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29943837640207992542523923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79850233707221313446730461 29943837640207992542523923)
  ·
    refine ⟨44915756460311988813785885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29943837640207992542523923 44915756460311988813785885)
    ·
      refine ⟨16843408672616995805169707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44915756460311988813785885 16843408672616995805169707)
      ·
        refine ⟨25265113008925493707754561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16843408672616995805169707 25265113008925493707754561)
        ·
          refine ⟨18948834756694120280815921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25265113008925493707754561 18948834756694120280815921)
          ·
            refine ⟨14211626067520590210611941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18948834756694120280815921 14211626067520590210611941)
            ·
              refine ⟨2664679887660110664489739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14211626067520590210611941 2664679887660110664489739)
              ·
                refine ⟨3997019831490165996734609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664679887660110664489739 3997019831490165996734609)
                ·
                  refine ⟨2997764873617624497550957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3997019831490165996734609 2997764873617624497550957)
                  ·
                    refine ⟨1124161827606609186581609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997764873617624497550957 1124161827606609186581609)
                    ·
                      rfl

theorem cell22_3283946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_3283946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283946 prefixEnd_3283946 := by exact prefixLift 3283946
  have htrace : WordTrace (prefixWord ++ tailWord_3283946) baseStart_3283946 baseEnd_3283946 := by
    simpa [prefixWord, tailWord_3283946, baseEnd_3283946] using wordTrace_append hprefix tailTrace_3283946
  have hstable : (prefixWord ++ tailWord_3283946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283946).length < 2 ^ (prefixWord ++ tailWord_3283946).sum := by decide
  have hdescent : baseEnd_3283946 < baseStart_3283946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3283985 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3283985 : Nat := 118140960795 + 3283985 * 2 ^ 59
def prefixEnd_3283985 : Nat := 4983230072969 + 3 ^ 40 * 3283985 * 2
def baseEnd_3283985 : Nat := 1124175178103626084856489

theorem tailTrace_3283985 : CollatzResearch.WordTrace tailWord_3283985 prefixEnd_3283985 1124175178103626084856489 := by
  unfold tailWord_3283985
  simp only [CollatzResearch.WordTrace]
  refine ⟨119776773007690679830765409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79851182005127119887176939 119776773007690679830765409)
  ·
    refine ⟨89832579755768009873074057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119776773007690679830765409 89832579755768009873074057)
    ·
      refine ⟨67374434816826007404805543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89832579755768009873074057 67374434816826007404805543)
      ·
        refine ⟨101061652225239011107208315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67374434816826007404805543 101061652225239011107208315)
        ·
          refine ⟨151592478337858516660812473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101061652225239011107208315 151592478337858516660812473)
          ·
            refine ⟨113694358753393887495609355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151592478337858516660812473 113694358753393887495609355)
            ·
              refine ⟨170541538130090831243414033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113694358753393887495609355 170541538130090831243414033)
              ·
                refine ⟨127906153597568123432560525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170541538130090831243414033 127906153597568123432560525)
                ·
                  refine ⟨47964807599088046287210197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127906153597568123432560525 47964807599088046287210197)
                  ·
                    refine ⟨1124175178103626084856489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47964807599088046287210197 1124175178103626084856489)
                    ·
                      rfl

theorem cell22_3283985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3283985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3283985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3283985 prefixEnd_3283985 := by exact prefixLift 3283985
  have htrace : WordTrace (prefixWord ++ tailWord_3283985) baseStart_3283985 baseEnd_3283985 := by
    simpa [prefixWord, tailWord_3283985, baseEnd_3283985] using wordTrace_append hprefix tailTrace_3283985
  have hstable : (prefixWord ++ tailWord_3283985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3283985).length < 2 ^ (prefixWord ++ tailWord_3283985).sum := by decide
  have hdescent : baseEnd_3283985 < baseStart_3283985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3283985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284002 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3284002 : Nat := 118140960795 + 3284002 * 2 ^ 59
def prefixEnd_3284002 : Nat := 4983230072969 + 3 ^ 40 * 3284002 * 2
def baseEnd_3284002 : Nat := 1124180997551043707181437

theorem tailTrace_3284002 : CollatzResearch.WordTrace tailWord_3284002 prefixEnd_3284002 1124180997551043707181437 := by
  unfold tailWord_3284002
  simp only [CollatzResearch.WordTrace]
  refine ⟨29944348262157272933533565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79851595365752727822756173 29944348262157272933533565)
  ·
    refine ⟨11229130598308977350075087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29944348262157272933533565 11229130598308977350075087)
    ·
      refine ⟨16843695897463466025112631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11229130598308977350075087 16843695897463466025112631)
      ·
        refine ⟨25265543846195199037668947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16843695897463466025112631 25265543846195199037668947)
        ·
          refine ⟨37898315769292798556503421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25265543846195199037668947 37898315769292798556503421)
          ·
            refine ⟨14211868413484799458688783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37898315769292798556503421 14211868413484799458688783)
            ·
              refine ⟨21317802620227199188033175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14211868413484799458688783 21317802620227199188033175)
              ·
                refine ⟨31976703930340798782049763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21317802620227199188033175 31976703930340798782049763)
                ·
                  refine ⟨47965055895511198173074645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31976703930340798782049763 47965055895511198173074645)
                  ·
                    refine ⟨1124180997551043707181437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47965055895511198173074645 1124180997551043707181437)
                    ·
                      rfl

theorem cell22_3284002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3284002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284002 prefixEnd_3284002 := by exact prefixLift 3284002
  have htrace : WordTrace (prefixWord ++ tailWord_3284002) baseStart_3284002 baseEnd_3284002 := by
    simpa [prefixWord, tailWord_3284002, baseEnd_3284002] using wordTrace_append hprefix tailTrace_3284002
  have hstable : (prefixWord ++ tailWord_3284002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284002).length < 2 ^ (prefixWord ++ tailWord_3284002).sum := by decide
  have hdescent : baseEnd_3284002 < baseStart_3284002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284004 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 5]
def baseStart_3284004 : Nat := 118140960795 + 3284004 * 2 ^ 59
def prefixEnd_3284004 : Nat := 4983230072969 + 3 ^ 40 * 3284004 * 2
def baseEnd_3284004 : Nat := 374727227397305456210477

theorem tailTrace_3284004 : CollatzResearch.WordTrace tailWord_3284004 prefixEnd_3284004 374727227397305456210477 := by
  unfold tailWord_3284004
  simp only [CollatzResearch.WordTrace]
  refine ⟨59888732997310923037853533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79851643996414564050471377 59888732997310923037853533)
  ·
    refine ⟨22458274873991596139195075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59888732997310923037853533 22458274873991596139195075)
    ·
      refine ⟨33687412310987394208792613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22458274873991596139195075 33687412310987394208792613)
      ·
        refine ⟨6316389808310136414148615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33687412310987394208792613 6316389808310136414148615)
        ·
          refine ⟨9474584712465204621222923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6316389808310136414148615 9474584712465204621222923)
          ·
            refine ⟨14211877068697806931834385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9474584712465204621222923 14211877068697806931834385)
            ·
              refine ⟨10658907801523355198875789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14211877068697806931834385 10658907801523355198875789)
              ·
                refine ⟨3997090425571258199578421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10658907801523355198875789 3997090425571258199578421)
                ·
                  refine ⟨374727227397305456210477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3997090425571258199578421 374727227397305456210477)
                  ·
                    rfl

theorem cell22_3284004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_3284004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284004 prefixEnd_3284004 := by exact prefixLift 3284004
  have htrace : WordTrace (prefixWord ++ tailWord_3284004) baseStart_3284004 baseEnd_3284004 := by
    simpa [prefixWord, tailWord_3284004, baseEnd_3284004] using wordTrace_append hprefix tailTrace_3284004
  have hstable : (prefixWord ++ tailWord_3284004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284004).length < 2 ^ (prefixWord ++ tailWord_3284004).sum := by decide
  have hdescent : baseEnd_3284004 < baseStart_3284004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284017 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_3284017 : Nat := 118140960795 + 3284017 * 2 ^ 59
def prefixEnd_3284017 : Nat := 4983230072969 + 3 ^ 40 * 3284017 * 2
def baseEnd_3284017 : Nat := 1124186132357588668056391

theorem tailTrace_3284017 : CollatzResearch.WordTrace tailWord_3284017 prefixEnd_3284017 1124186132357588668056391 := by
  unfold tailWord_3284017
  simp only [CollatzResearch.WordTrace]
  refine ⟨119777940143574749295930305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79851960095716499530620203 119777940143574749295930305)
  ·
    refine ⟨89833455107681061971947729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119777940143574749295930305 89833455107681061971947729)
    ·
      refine ⟨67375091330760796478960797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89833455107681061971947729 67375091330760796478960797)
      ·
        refine ⟨25265659249035298679610299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67375091330760796478960797 25265659249035298679610299)
        ·
          refine ⟨37898488873552948019415449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25265659249035298679610299 37898488873552948019415449)
          ·
            refine ⟨28423866655164711014561587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37898488873552948019415449 28423866655164711014561587)
            ·
              refine ⟨42635799982747066521842381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28423866655164711014561587 42635799982747066521842381)
              ·
                refine ⟨15988424993530149945690893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42635799982747066521842381 15988424993530149945690893)
                ·
                  refine ⟨5995659372573806229634085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15988424993530149945690893 5995659372573806229634085)
                  ·
                    refine ⟨1124186132357588668056391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5995659372573806229634085 1124186132357588668056391)
                    ·
                      rfl

theorem cell22_3284017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_3284017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284017 prefixEnd_3284017 := by exact prefixLift 3284017
  have htrace : WordTrace (prefixWord ++ tailWord_3284017) baseStart_3284017 baseEnd_3284017 := by
    simpa [prefixWord, tailWord_3284017, baseEnd_3284017] using wordTrace_append hprefix tailTrace_3284017
  have hstable : (prefixWord ++ tailWord_3284017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284017).length < 2 ^ (prefixWord ++ tailWord_3284017).sum := by decide
  have hdescent : baseEnd_3284017 < baseStart_3284017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284038 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3284038 : Nat := 118140960795 + 3284038 * 2 ^ 59
def prefixEnd_3284038 : Nat := 4983230072969 + 3 ^ 40 * 3284038 * 2
def baseEnd_3284038 : Nat := 374731107028917204427109

theorem tailTrace_3284038 : CollatzResearch.WordTrace tailWord_3284038 prefixEnd_3284038 374731107028917204427109 := by
  unfold tailWord_3284038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743084564890583433826399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79852470717665779921629845 3743084564890583433826399)
  ·
    refine ⟨5614626847335875150739599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3743084564890583433826399 5614626847335875150739599)
    ·
      refine ⟨8421940271003812726109399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5614626847335875150739599 8421940271003812726109399)
      ·
        refine ⟨12632910406505719089164099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8421940271003812726109399 12632910406505719089164099)
        ·
          refine ⟨18949365609758578633746149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12632910406505719089164099 18949365609758578633746149)
          ·
            refine ⟨3553006051829733493827403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18949365609758578633746149 3553006051829733493827403)
            ·
              refine ⟨5329509077744600240741105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553006051829733493827403 5329509077744600240741105)
              ·
                refine ⟨3997131808308450180555829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5329509077744600240741105 3997131808308450180555829)
                ·
                  refine ⟨374731107028917204427109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3997131808308450180555829 374731107028917204427109)
                  ·
                    rfl

theorem cell22_3284038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3284038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284038 prefixEnd_3284038 := by exact prefixLift 3284038
  have htrace : WordTrace (prefixWord ++ tailWord_3284038) baseStart_3284038 baseEnd_3284038 := by
    simpa [prefixWord, tailWord_3284038, baseEnd_3284038] using wordTrace_append hprefix tailTrace_3284038
  have hstable : (prefixWord ++ tailWord_3284038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284038).length < 2 ^ (prefixWord ++ tailWord_3284038).sum := by decide
  have hdescent : baseEnd_3284038 < baseStart_3284038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284049 : List Nat := [1, 2, 2, 1, 3, 1, 4, 4, 4]
def baseStart_3284049 : Nat := 118140960795 + 3284049 * 2 ^ 59
def prefixEnd_3284049 : Nat := 4983230072969 + 3 ^ 40 * 3284049 * 2
def baseEnd_3284049 : Nat := 374732362203850417085431

theorem tailTrace_3284049 : CollatzResearch.WordTrace tailWord_3284049 prefixEnd_3284049 374732362203850417085431 := by
  unfold tailWord_3284049
  simp only [CollatzResearch.WordTrace]
  refine ⟨119779107279458818761095201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79852738186305879174063467 119779107279458818761095201)
  ·
    refine ⟨89834330459594114070821401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119779107279458818761095201 89834330459594114070821401)
    ·
      refine ⟨67375747844695585553116051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89834330459594114070821401 67375747844695585553116051)
      ·
        refine ⟨101063621767043378329674077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67375747844695585553116051 101063621767043378329674077)
        ·
          refine ⟨37898858162641266873627779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101063621767043378329674077 37898858162641266873627779)
          ·
            refine ⟨56848287243961900310441669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37898858162641266873627779 56848287243961900310441669)
            ·
              refine ⟨10659053858242856308207813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56848287243961900310441669 10659053858242856308207813)
              ·
                refine ⟨1998572598420535557788965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10659053858242856308207813 1998572598420535557788965)
                ·
                  refine ⟨374732362203850417085431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1998572598420535557788965 374732362203850417085431)
                  ·
                    rfl

theorem cell22_3284049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_3284049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284049 prefixEnd_3284049 := by exact prefixLift 3284049
  have htrace : WordTrace (prefixWord ++ tailWord_3284049) baseStart_3284049 baseEnd_3284049 := by
    simpa [prefixWord, tailWord_3284049, baseEnd_3284049] using wordTrace_append hprefix tailTrace_3284049
  have hstable : (prefixWord ++ tailWord_3284049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284049).length < 2 ^ (prefixWord ++ tailWord_3284049).sum := by decide
  have hdescent : baseEnd_3284049 < baseStart_3284049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284156 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 5]
def baseStart_3284156 : Nat := 118140960795 + 3284156 * 2 ^ 59
def prefixEnd_3284156 : Nat := 4983230072969 + 3 ^ 40 * 3284156 * 2
def baseEnd_3284156 : Nat := 374744571632746212943655

theorem tailTrace_3284156 : CollatzResearch.WordTrace tailWord_3284156 prefixEnd_3284156 374744571632746212943655 := by
  unfold tailWord_3284156
  simp only [CollatzResearch.WordTrace]
  refine ⟨59891504945035588017620161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79855339926714117356826881 59891504945035588017620161)
  ·
    refine ⟨44918628708776691013215121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59891504945035588017620161 44918628708776691013215121)
    ·
      refine ⟨33688971531582518259911341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44918628708776691013215121 33688971531582518259911341)
      ·
        refine ⟨12633364324343444347466753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33688971531582518259911341 12633364324343444347466753)
        ·
          refine ⟨9475023243257583260600065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12633364324343444347466753 9475023243257583260600065)
          ·
            refine ⟨7106267432443187445450049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9475023243257583260600065 7106267432443187445450049)
            ·
              refine ⟨5329700574332390584087537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7106267432443187445450049 5329700574332390584087537)
              ·
                refine ⟨3997275430749292938065653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5329700574332390584087537 3997275430749292938065653)
                ·
                  refine ⟨374744571632746212943655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3997275430749292938065653 374744571632746212943655)
                  ·
                    rfl

theorem cell22_3284156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_3284156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284156 prefixEnd_3284156 := by exact prefixLift 3284156
  have htrace : WordTrace (prefixWord ++ tailWord_3284156) baseStart_3284156 baseEnd_3284156 := by
    simpa [prefixWord, tailWord_3284156, baseEnd_3284156] using wordTrace_append hprefix tailTrace_3284156
  have hstable : (prefixWord ++ tailWord_3284156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284156).length < 2 ^ (prefixWord ++ tailWord_3284156).sum := by decide
  have hdescent : baseEnd_3284156 < baseStart_3284156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284167 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 10]
def baseStart_3284167 : Nat := 118140960795 + 3284167 * 2 ^ 59
def prefixEnd_3284167 : Nat := 4983230072969 + 3 ^ 40 * 3284167 * 2
def baseEnd_3284167 : Nat := 374745826807679425601977

theorem tailTrace_3284167 : CollatzResearch.WordTrace tailWord_3284167 prefixEnd_3284167 374745826807679425601977 := by
  unfold tailWord_3284167
  simp only [CollatzResearch.WordTrace]
  refine ⟨119783411093031324913890755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79855607395354216609260503 119783411093031324913890755)
  ·
    refine ⟨179675116639546987370836133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119783411093031324913890755 179675116639546987370836133)
    ·
      refine ⟨33689084369915060132031775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179675116639546987370836133 33689084369915060132031775)
      ·
        refine ⟨50533626554872590198047663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33689084369915060132031775 50533626554872590198047663)
        ·
          refine ⟨75800439832308885297071495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50533626554872590198047663 75800439832308885297071495)
          ·
            refine ⟨113700659748463327945607243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75800439832308885297071495 113700659748463327945607243)
            ·
              refine ⟨170550989622694991918410865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113700659748463327945607243 170550989622694991918410865)
              ·
                refine ⟨127913242217021243938808149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170550989622694991918410865 127913242217021243938808149)
                ·
                  refine ⟨374745826807679425601977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127913242217021243938808149 374745826807679425601977)
                  ·
                    rfl

theorem cell22_3284167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 10].length) (baseStart_3284167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284167 prefixEnd_3284167 := by exact prefixLift 3284167
  have htrace : WordTrace (prefixWord ++ tailWord_3284167) baseStart_3284167 baseEnd_3284167 := by
    simpa [prefixWord, tailWord_3284167, baseEnd_3284167] using wordTrace_append hprefix tailTrace_3284167
  have hstable : (prefixWord ++ tailWord_3284167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284167).length < 2 ^ (prefixWord ++ tailWord_3284167).sum := by decide
  have hdescent : baseEnd_3284167 < baseStart_3284167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284203 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 1, 4]
def baseStart_3284203 : Nat := 118140960795 + 3284203 * 2 ^ 59
def prefixEnd_3284203 : Nat := 4983230072969 + 3 ^ 40 * 3284203 * 2
def baseEnd_3284203 : Nat := 1124249803958746182905821

theorem tailTrace_3284203 : CollatzResearch.WordTrace tailWord_3284203 prefixEnd_3284203 1124249803958746182905821 := by
  unfold tailWord_3284203
  simp only [CollatzResearch.WordTrace]
  refine ⟨119784724120900903062201263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79856482747267268708134175 119784724120900903062201263)
  ·
    refine ⟨179677086181351354593301895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119784724120900903062201263 179677086181351354593301895)
    ·
      refine ⟨269515629272027031889952843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179677086181351354593301895 269515629272027031889952843)
      ·
        refine ⟨404273443908040547834929265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269515629272027031889952843 404273443908040547834929265)
        ·
          refine ⟨303205082931030410876196949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404273443908040547834929265 303205082931030410876196949)
          ·
            refine ⟨3553184565598012627455433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 303205082931030410876196949 3553184565598012627455433)
            ·
              refine ⟨2664888424198509470591575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553184565598012627455433 2664888424198509470591575)
              ·
                refine ⟨3997332636297764205887363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664888424198509470591575 3997332636297764205887363)
                ·
                  refine ⟨5995998954446646308831045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997332636297764205887363 5995998954446646308831045)
                  ·
                    refine ⟨1124249803958746182905821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5995998954446646308831045 1124249803958746182905821)
                    ·
                      rfl

theorem cell22_3284203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 4].length) (baseStart_3284203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284203 prefixEnd_3284203 := by exact prefixLift 3284203
  have htrace : WordTrace (prefixWord ++ tailWord_3284203) baseStart_3284203 baseEnd_3284203 := by
    simpa [prefixWord, tailWord_3284203, baseEnd_3284203] using wordTrace_append hprefix tailTrace_3284203
  have hstable : (prefixWord ++ tailWord_3284203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284203).length < 2 ^ (prefixWord ++ tailWord_3284203).sum := by decide
  have hdescent : baseEnd_3284203 < baseStart_3284203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284233 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 2, 3]
def baseStart_3284233 : Nat := 118140960795 + 3284233 * 2 ^ 59
def prefixEnd_3284233 : Nat := 4983230072969 + 3 ^ 40 * 3284233 * 2
def baseEnd_3284233 : Nat := 1124260073571836104655729

theorem tailTrace_3284233 : CollatzResearch.WordTrace tailWord_3284233 prefixEnd_3284233 1124260073571836104655729 := by
  unfold tailWord_3284233
  simp only [CollatzResearch.WordTrace]
  refine ⟨119785818310792218185793353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79857212207194812123862235 119785818310792218185793353)
  ·
    refine ⟨89839363733094163639345015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119785818310792218185793353 89839363733094163639345015)
    ·
      refine ⟨134759045599641245459017523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89839363733094163639345015 134759045599641245459017523)
      ·
        refine ⟨202138568399461868188526285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134759045599641245459017523 202138568399461868188526285)
        ·
          refine ⟨75801963149798200570697357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202138568399461868188526285 75801963149798200570697357)
          ·
            refine ⟨28425736181174325214011509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75801963149798200570697357 28425736181174325214011509)
            ·
              refine ⟨2664912766985092988813579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28425736181174325214011509 2664912766985092988813579)
              ·
                refine ⟨3997369150477639483220369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664912766985092988813579 3997369150477639483220369)
                ·
                  refine ⟨2998026862858229612415277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3997369150477639483220369 2998026862858229612415277)
                  ·
                    refine ⟨1124260073571836104655729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998026862858229612415277 1124260073571836104655729)
                    ·
                      rfl

theorem cell22_3284233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_3284233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284233 prefixEnd_3284233 := by exact prefixLift 3284233
  have htrace : WordTrace (prefixWord ++ tailWord_3284233) baseStart_3284233 baseEnd_3284233 := by
    simpa [prefixWord, tailWord_3284233, baseEnd_3284233] using wordTrace_append hprefix tailTrace_3284233
  have hstable : (prefixWord ++ tailWord_3284233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284233).length < 2 ^ (prefixWord ++ tailWord_3284233).sum := by decide
  have hdescent : baseEnd_3284233 < baseStart_3284233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284276 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3284276 : Nat := 118140960795 + 3284276 * 2 ^ 59
def prefixEnd_3284276 : Nat := 4983230072969 + 3 ^ 40 * 3284276 * 2
def baseEnd_3284276 : Nat := 1124274793350598325830597

theorem tailTrace_3284276 : CollatzResearch.WordTrace tailWord_3284276 prefixEnd_3284276 1124274793350598325830597 := by
  unfold tailWord_3284276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59893693324818218264804341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79858257766424291019739121 59893693324818218264804341)
  ·
    refine ⟨5615033749201707962325407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59893693324818218264804341 5615033749201707962325407)
    ·
      refine ⟨8422550623802561943488111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5615033749201707962325407 8422550623802561943488111)
      ·
        refine ⟨12633825935703842915232167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8422550623802561943488111 12633825935703842915232167)
        ·
          refine ⟨18950738903555764372848251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12633825935703842915232167 18950738903555764372848251)
          ·
            refine ⟨28426108355333646559272377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18950738903555764372848251 28426108355333646559272377)
            ·
              refine ⟨21319581266500234919454283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28426108355333646559272377 21319581266500234919454283)
              ·
                refine ⟨31979371899750352379181425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21319581266500234919454283 31979371899750352379181425)
                ·
                  refine ⟨23984528924812764284386069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31979371899750352379181425 23984528924812764284386069)
                  ·
                    refine ⟨1124274793350598325830597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23984528924812764284386069 1124274793350598325830597)
                    ·
                      rfl

theorem cell22_3284276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3284276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284276 prefixEnd_3284276 := by exact prefixLift 3284276
  have htrace : WordTrace (prefixWord ++ tailWord_3284276) baseStart_3284276 baseEnd_3284276 := by
    simpa [prefixWord, tailWord_3284276, baseEnd_3284276] using wordTrace_append hprefix tailTrace_3284276
  have hstable : (prefixWord ++ tailWord_3284276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284276).length < 2 ^ (prefixWord ++ tailWord_3284276).sum := by decide
  have hdescent : baseEnd_3284276 < baseStart_3284276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284321 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3284321 : Nat := 118140960795 + 3284321 * 2 ^ 59
def prefixEnd_3284321 : Nat := 4983230072969 + 3 ^ 40 * 3284321 * 2
def baseEnd_3284321 : Nat := 1124290197770233208455459

theorem tailTrace_3284321 : CollatzResearch.WordTrace tailWord_3284321 prefixEnd_3284321 1124290197770233208455459 := by
  unfold tailWord_3284321
  simp only [CollatzResearch.WordTrace]
  refine ⟨119789027934473409214996817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79859351956315606143331211 119789027934473409214996817)
  ·
    refine ⟨89841770950855056911247613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119789027934473409214996817 89841770950855056911247613)
    ·
      refine ⟨33690664106570646341717855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89841770950855056911247613 33690664106570646341717855)
      ·
        refine ⟨50535996159855969512576783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33690664106570646341717855 50535996159855969512576783)
        ·
          refine ⟨75803994239783954268865175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50535996159855969512576783 75803994239783954268865175)
          ·
            refine ⟨113705991359675931403297763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75803994239783954268865175 113705991359675931403297763)
            ·
              refine ⟨170558987039513897104946645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113705991359675931403297763 170558987039513897104946645)
              ·
                refine ⟨3997476258738606963397187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 170558987039513897104946645 3997476258738606963397187)
                ·
                  refine ⟨5996214388107910445095781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997476258738606963397187 5996214388107910445095781)
                  ·
                    refine ⟨1124290197770233208455459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5996214388107910445095781 1124290197770233208455459)
                    ·
                      rfl

theorem cell22_3284321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3284321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284321 prefixEnd_3284321 := by exact prefixLift 3284321
  have htrace : WordTrace (prefixWord ++ tailWord_3284321) baseStart_3284321 baseEnd_3284321 := by
    simpa [prefixWord, tailWord_3284321, baseEnd_3284321] using wordTrace_append hprefix tailTrace_3284321
  have hstable : (prefixWord ++ tailWord_3284321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284321).length < 2 ^ (prefixWord ++ tailWord_3284321).sum := by decide
  have hdescent : baseEnd_3284321 < baseStart_3284321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284353 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 6]
def baseStart_3284353 : Nat := 118140960795 + 3284353 * 2 ^ 59
def prefixEnd_3284353 : Nat := 4983230072969 + 3 ^ 40 * 3284353 * 2
def baseEnd_3284353 : Nat := 374767050674731930551787

theorem tailTrace_3284353 : CollatzResearch.WordTrace tailWord_3284353 prefixEnd_3284353 374767050674731930551787 := by
  unfold tailWord_3284353
  simp only [CollatzResearch.WordTrace]
  refine ⟨119790195070357478680161713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79860130046904985786774475 119790195070357478680161713)
  ·
    refine ⟨89842646302768109010121285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119790195070357478680161713 89842646302768109010121285)
    ·
      refine ⟨16845496181769020439397741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89842646302768109010121285 16845496181769020439397741)
      ·
        refine ⟨6317061068163382664774153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16845496181769020439397741 6317061068163382664774153)
        ·
          refine ⟨4737795801122536998580615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6317061068163382664774153 4737795801122536998580615)
          ·
            refine ⟨7106693701683805497870923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4737795801122536998580615 7106693701683805497870923)
            ·
              refine ⟨10660040552525708246806385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106693701683805497870923 10660040552525708246806385)
              ·
                refine ⟨7995030414394281185104789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10660040552525708246806385 7995030414394281185104789)
                ·
                  refine ⟨374767050674731930551787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7995030414394281185104789 374767050674731930551787)
                  ·
                    rfl

theorem cell22_3284353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_3284353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284353 prefixEnd_3284353 := by exact prefixLift 3284353
  have htrace : WordTrace (prefixWord ++ tailWord_3284353) baseStart_3284353 baseEnd_3284353 := by
    simpa [prefixWord, tailWord_3284353, baseEnd_3284353] using wordTrace_append hprefix tailTrace_3284353
  have hstable : (prefixWord ++ tailWord_3284353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284353).length < 2 ^ (prefixWord ++ tailWord_3284353).sum := by decide
  have hdescent : baseEnd_3284353 < baseStart_3284353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284372 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3284372 : Nat := 118140960795 + 3284372 * 2 ^ 59
def prefixEnd_3284372 : Nat := 4983230072969 + 3 ^ 40 * 3284372 * 2
def baseEnd_3284372 : Nat := 1124307656112486075430303

theorem tailTrace_3284372 : CollatzResearch.WordTrace tailWord_3284372 prefixEnd_3284372 1124307656112486075430303 := by
  unfold tailWord_3284372
  simp only [CollatzResearch.WordTrace]
  refine ⟨59895444028644322462551685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79860592038192429950068913 59895444028644322462551685)
  ·
    refine ⟨11230395755370810461728441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59895444028644322462551685 11230395755370810461728441)
    ·
      refine ⟨8422796816528107846296331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11230395755370810461728441 8422796816528107846296331)
      ·
        refine ⟨12634195224792161769444497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8422796816528107846296331 12634195224792161769444497)
        ·
          refine ⟨9475646418594121327083373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12634195224792161769444497 9475646418594121327083373)
          ·
            refine ⟨3553367406972795497656265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9475646418594121327083373 3553367406972795497656265)
            ·
              refine ⟨2665025555229596623242199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553367406972795497656265 2665025555229596623242199)
              ·
                refine ⟨3997538332844394934863299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665025555229596623242199 3997538332844394934863299)
                ·
                  refine ⟨5996307499266592402294949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997538332844394934863299 5996307499266592402294949)
                  ·
                    refine ⟨1124307656112486075430303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5996307499266592402294949 1124307656112486075430303)
                    ·
                      rfl

theorem cell22_3284372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3284372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284372 prefixEnd_3284372 := by exact prefixLift 3284372
  have htrace : WordTrace (prefixWord ++ tailWord_3284372) baseStart_3284372 baseEnd_3284372 := by
    simpa [prefixWord, tailWord_3284372, baseEnd_3284372] using wordTrace_append hprefix tailTrace_3284372
  have hstable : (prefixWord ++ tailWord_3284372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284372).length < 2 ^ (prefixWord ++ tailWord_3284372).sum := by decide
  have hdescent : baseEnd_3284372 < baseStart_3284372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284379 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 6, 7]
def baseStart_3284379 : Nat := 118140960795 + 3284379 * 2 ^ 59
def prefixEnd_3284379 : Nat := 4983230072969 + 3 ^ 40 * 3284379 * 2
def baseEnd_3284379 : Nat := 1124310052355540390505281

theorem tailTrace_3284379 : CollatzResearch.WordTrace tailWord_3284379 prefixEnd_3284379 1124310052355540390505281 := by
  unfold tailWord_3284379
  simp only [CollatzResearch.WordTrace]
  refine ⟨119791143368263285120608191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79860762245508856747072127 119791143368263285120608191)
  ·
    refine ⟨179686715052394927680912287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119791143368263285120608191 179686715052394927680912287)
    ·
      refine ⟨269530072578592391521368431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179686715052394927680912287 269530072578592391521368431)
      ·
        refine ⟨404295108867888587282052647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269530072578592391521368431 404295108867888587282052647)
        ·
          refine ⟨606442663301832880923078971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404295108867888587282052647 606442663301832880923078971)
          ·
            refine ⟨909663994952749321384618457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606442663301832880923078971 909663994952749321384618457)
            ·
              refine ⟨682247996214561991038463843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909663994952749321384618457 682247996214561991038463843)
              ·
                refine ⟨1023371994321842986557695765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682247996214561991038463843 1023371994321842986557695765)
                ·
                  refine ⟨47970562233836389994891989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1023371994321842986557695765 47970562233836389994891989)
                  ·
                    refine ⟨1124310052355540390505281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47970562233836389994891989 1124310052355540390505281)
                    ·
                      rfl

theorem cell22_3284379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_3284379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284379 prefixEnd_3284379 := by exact prefixLift 3284379
  have htrace : WordTrace (prefixWord ++ tailWord_3284379) baseStart_3284379 baseEnd_3284379 := by
    simpa [prefixWord, tailWord_3284379, baseEnd_3284379] using wordTrace_append hprefix tailTrace_3284379
  have hstable : (prefixWord ++ tailWord_3284379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284379).length < 2 ^ (prefixWord ++ tailWord_3284379).sum := by decide
  have hdescent : baseEnd_3284379 < baseStart_3284379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284381 : List Nat := [1, 4, 2, 1, 3, 2, 9]
def baseStart_3284381 : Nat := 118140960795 + 3284381 * 2 ^ 59
def prefixEnd_3284381 : Nat := 4983230072969 + 3 ^ 40 * 3284381 * 2
def baseEnd_3284381 : Nat := 41641138407274557479825

theorem tailTrace_3284381 : CollatzResearch.WordTrace tailWord_3284381 prefixEnd_3284381 41641138407274557479825 := by
  unfold tailWord_3284381
  simp only [CollatzResearch.WordTrace]
  refine ⟨119791216314256039462180997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79860810876170692974787331 119791216314256039462180997)
  ·
    refine ⟨22460853058923007399158937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119791216314256039462180997 22460853058923007399158937)
    ·
      refine ⟨16845639794192255549369203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22460853058923007399158937 16845639794192255549369203)
      ·
        refine ⟨25268459691288383324053805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16845639794192255549369203 25268459691288383324053805)
        ·
          refine ⟨9475672384233143746520177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25268459691288383324053805 9475672384233143746520177)
          ·
            refine ⟨7106754288174857809890133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9475672384233143746520177 7106754288174857809890133)
            ·
              refine ⟨41641138407274557479825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7106754288174857809890133 41641138407274557479825)
              ·
                rfl

theorem cell22_3284381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 9].length) (baseStart_3284381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284381 prefixEnd_3284381 := by exact prefixLift 3284381
  have htrace : WordTrace (prefixWord ++ tailWord_3284381) baseStart_3284381 baseEnd_3284381 := by
    simpa [prefixWord, tailWord_3284381, baseEnd_3284381] using wordTrace_append hprefix tailTrace_3284381
  have hstable : (prefixWord ++ tailWord_3284381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284381).length < 2 ^ (prefixWord ++ tailWord_3284381).sum := by decide
  have hdescent : baseEnd_3284381 < baseStart_3284381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284413 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_3284413 : Nat := 118140960795 + 3284413 * 2 ^ 59
def prefixEnd_3284413 : Nat := 4983230072969 + 3 ^ 40 * 3284413 * 2
def baseEnd_3284413 : Nat := 1124321691250375635155177

theorem tailTrace_3284413 : CollatzResearch.WordTrace tailWord_3284413 prefixEnd_3284413 1124321691250375635155177 := by
  unfold tailWord_3284413
  simp only [CollatzResearch.WordTrace]
  refine ⟨119792383450140108927345893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79861588966760072618230595 119792383450140108927345893)
  ·
    refine ⟨22461071896901270423877355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119792383450140108927345893 22461071896901270423877355)
    ·
      refine ⟨33691607845351905635816033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22461071896901270423877355 33691607845351905635816033)
      ·
        refine ⟨25268705884013929226862025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33691607845351905635816033 25268705884013929226862025)
        ·
          refine ⟨18951529413010446920146519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25268705884013929226862025 18951529413010446920146519)
          ·
            refine ⟨28427294119515670380219779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18951529413010446920146519 28427294119515670380219779)
            ·
              refine ⟨42640941179273505570329669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28427294119515670380219779 42640941179273505570329669)
              ·
                refine ⟨7995176471113782294436813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42640941179273505570329669 7995176471113782294436813)
                ·
                  refine ⟨2998191176667668360413805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7995176471113782294436813 2998191176667668360413805)
                  ·
                    refine ⟨1124321691250375635155177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998191176667668360413805 1124321691250375635155177)
                    ·
                      rfl

theorem cell22_3284413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_3284413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284413 prefixEnd_3284413 := by exact prefixLift 3284413
  have htrace : WordTrace (prefixWord ++ tailWord_3284413) baseStart_3284413 baseEnd_3284413 := by
    simpa [prefixWord, tailWord_3284413, baseEnd_3284413] using wordTrace_append hprefix tailTrace_3284413
  have hstable : (prefixWord ++ tailWord_3284413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284413).length < 2 ^ (prefixWord ++ tailWord_3284413).sum := by decide
  have hdescent : baseEnd_3284413 < baseStart_3284413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284426 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_3284426 : Nat := 118140960795 + 3284426 * 2 ^ 59
def prefixEnd_3284426 : Nat := 4983230072969 + 3 ^ 40 * 3284426 * 2
def baseEnd_3284426 : Nat := 374775380472015978193379

theorem tailTrace_3284426 : CollatzResearch.WordTrace tailWord_3284426 prefixEnd_3284426 374775380472015978193379 := by
  unfold tailWord_3284426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29948214399773253036892283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79861905066062008098379421 29948214399773253036892283)
  ·
    refine ⟨44922321599659879555338425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29948214399773253036892283 44922321599659879555338425)
    ·
      refine ⟨33691741199744909666503819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44922321599659879555338425 33691741199744909666503819)
      ·
        refine ⟨50537611799617364499755729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33691741199744909666503819 50537611799617364499755729)
        ·
          refine ⟨37903208849713023374816797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50537611799617364499755729 37903208849713023374816797)
          ·
            refine ⟨14213703318642383765556299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37903208849713023374816797 14213703318642383765556299)
            ·
              refine ⟨21320554977963575648334449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14213703318642383765556299 21320554977963575648334449)
              ·
                refine ⟨15990416233472681736250837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21320554977963575648334449 15990416233472681736250837)
                ·
                  refine ⟨374775380472015978193379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15990416233472681736250837 374775380472015978193379)
                  ·
                    rfl

theorem cell22_3284426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_3284426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284426 prefixEnd_3284426 := by exact prefixLift 3284426
  have htrace : WordTrace (prefixWord ++ tailWord_3284426) baseStart_3284426 baseEnd_3284426 := by
    simpa [prefixWord, tailWord_3284426, baseEnd_3284426] using wordTrace_append hprefix tailTrace_3284426
  have hstable : (prefixWord ++ tailWord_3284426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284426).length < 2 ^ (prefixWord ++ tailWord_3284426).sum := by decide
  have hdescent : baseEnd_3284426 < baseStart_3284426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284447 : List Nat := [1, 1, 2, 3, 3, 1, 5, 2, 1, 3]
def baseStart_3284447 : Nat := 118140960795 + 3284447 * 2 ^ 59
def prefixEnd_3284447 : Nat := 4983230072969 + 3 ^ 40 * 3284447 * 2
def baseEnd_3284447 : Nat := 1124333330145210879805073

theorem tailTrace_3284447 : CollatzResearch.WordTrace tailWord_3284447 prefixEnd_3284447 1124333330145210879805073 := by
  unfold tailWord_3284447
  simp only [CollatzResearch.WordTrace]
  refine ⟨119793623532016932734083595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79862415688011288489389063 119793623532016932734083595)
  ·
    refine ⟨179690435298025399101125393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119793623532016932734083595 179690435298025399101125393)
    ·
      refine ⟨134767826473519049325844045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179690435298025399101125393 134767826473519049325844045)
      ·
        refine ⟨50537934927569643497191517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134767826473519049325844045 50537934927569643497191517)
        ·
          refine ⟨18951725597838616311446819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50537934927569643497191517 18951725597838616311446819)
          ·
            refine ⟨28427588396757924467170229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18951725597838616311446819 28427588396757924467170229)
            ·
              refine ⟨2665086412196055418797209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28427588396757924467170229 2665086412196055418797209)
              ·
                refine ⟨1998814809147041564097907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665086412196055418797209 1998814809147041564097907)
                ·
                  refine ⟨2998222213720562346146861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998814809147041564097907 2998222213720562346146861)
                  ·
                    refine ⟨1124333330145210879805073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998222213720562346146861 1124333330145210879805073)
                    ·
                      rfl

theorem cell22_3284447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 3].length) (baseStart_3284447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284447 prefixEnd_3284447 := by exact prefixLift 3284447
  have htrace : WordTrace (prefixWord ++ tailWord_3284447) baseStart_3284447 baseEnd_3284447 := by
    simpa [prefixWord, tailWord_3284447, baseEnd_3284447] using wordTrace_append hprefix tailTrace_3284447
  have hstable : (prefixWord ++ tailWord_3284447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284447).length < 2 ^ (prefixWord ++ tailWord_3284447).sum := by decide
  have hdescent : baseEnd_3284447 < baseStart_3284447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284535 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 2, 4]
def baseStart_3284535 : Nat := 118140960795 + 3284535 * 2 ^ 59
def prefixEnd_3284535 : Nat := 4983230072969 + 3 ^ 40 * 3284535 * 2
def baseEnd_3284535 : Nat := 1124363454343607983604803

theorem tailTrace_3284535 : CollatzResearch.WordTrace tailWord_3284535 prefixEnd_3284535 1124363454343607983604803 := by
  unfold tailWord_3284535
  simp only [CollatzResearch.WordTrace]
  refine ⟨119796833155698123763287059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79864555437132082508858039 119796833155698123763287059)
  ·
    refine ⟨179695249733547185644930589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119796833155698123763287059 179695249733547185644930589)
    ·
      refine ⟨67385718650080194616848971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179695249733547185644930589 67385718650080194616848971)
      ·
        refine ⟨101078577975120291925273457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67385718650080194616848971 101078577975120291925273457)
        ·
          refine ⟨75808933481340218943955093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101078577975120291925273457 75808933481340218943955093)
          ·
            refine ⟨3553543756937822762997895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75808933481340218943955093 3553543756937822762997895)
            ·
              refine ⟨5330315635406734144496843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553543756937822762997895 5330315635406734144496843)
              ·
                refine ⟨7995473453110101216745265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330315635406734144496843 7995473453110101216745265)
                ·
                  refine ⟨5996605089832575912558949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7995473453110101216745265 5996605089832575912558949)
                  ·
                    refine ⟨1124363454343607983604803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5996605089832575912558949 1124363454343607983604803)
                    ·
                      rfl

theorem cell22_3284535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_3284535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284535 prefixEnd_3284535 := by exact prefixLift 3284535
  have htrace : WordTrace (prefixWord ++ tailWord_3284535) baseStart_3284535 baseEnd_3284535 := by
    simpa [prefixWord, tailWord_3284535, baseEnd_3284535] using wordTrace_append hprefix tailTrace_3284535
  have hstable : (prefixWord ++ tailWord_3284535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284535).length < 2 ^ (prefixWord ++ tailWord_3284535).sum := by decide
  have hdescent : baseEnd_3284535 < baseStart_3284535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284616 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 3, 3]
def baseStart_3284616 : Nat := 118140960795 + 3284616 * 2 ^ 59
def prefixEnd_3284616 : Nat := 4983230072969 + 3 ^ 40 * 3284616 * 2
def baseEnd_3284616 : Nat := 1124391182298950772329555

theorem tailTrace_3284616 : CollatzResearch.WordTrace tailWord_3284616 prefixEnd_3284616 1124391182298950772329555 := by
  unfold tailWord_3284616
  simp only [CollatzResearch.WordTrace]
  refine ⟨59899893734202337298492851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79866524978936449731323801 59899893734202337298492851)
  ·
    refine ⟨89849840601303505947739277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59899893734202337298492851 89849840601303505947739277)
    ·
      refine ⟨33693690225488814730402229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89849840601303505947739277 33693690225488814730402229)
      ·
        refine ⟨3158783458639576380975209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33693690225488814730402229 3158783458639576380975209)
        ·
          refine ⟨2369087593979682285731407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3158783458639576380975209 2369087593979682285731407)
          ·
            refine ⟨3553631390969523428597111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369087593979682285731407 3553631390969523428597111)
            ·
              refine ⟨5330447086454285142895667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553631390969523428597111 5330447086454285142895667)
              ·
                refine ⟨7995670629681427714343501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330447086454285142895667 7995670629681427714343501)
                ·
                  refine ⟨2998376486130535392878813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7995670629681427714343501 2998376486130535392878813)
                  ·
                    refine ⟨1124391182298950772329555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998376486130535392878813 1124391182298950772329555)
                    ·
                      rfl

theorem cell22_3284616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_3284616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284616 prefixEnd_3284616 := by exact prefixLift 3284616
  have htrace : WordTrace (prefixWord ++ tailWord_3284616) baseStart_3284616 baseEnd_3284616 := by
    simpa [prefixWord, tailWord_3284616, baseEnd_3284616] using wordTrace_append hprefix tailTrace_3284616
  have hstable : (prefixWord ++ tailWord_3284616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284616).length < 2 ^ (prefixWord ++ tailWord_3284616).sum := by decide
  have hdescent : baseEnd_3284616 < baseStart_3284616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284668 : List Nat := [2, 2, 2, 3, 1, 12]
def baseStart_3284668 : Nat := 118140960795 + 3284668 * 2 ^ 59
def prefixEnd_3284668 : Nat := 4983230072969 + 3 ^ 40 * 3284668 * 2
def baseEnd_3284668 : Nat := 13881592382242468765795

theorem tailTrace_3284668 : CollatzResearch.WordTrace tailWord_3284668 prefixEnd_3284668 13881592382242468765795 := by
  unfold tailWord_3284668
  simp only [CollatzResearch.WordTrace]
  refine ⟨59900842032108143738939329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79867789376144191651919105 59900842032108143738939329)
  ·
    refine ⟨44925631524081107804204497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59900842032108143738939329 44925631524081107804204497)
    ·
      refine ⟨33694223643060830853153373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44925631524081107804204497 33694223643060830853153373)
      ·
        refine ⟨12635333866147811569932515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33694223643060830853153373 12635333866147811569932515)
        ·
          refine ⟨18953000799221717354898773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12635333866147811569932515 18953000799221717354898773)
          ·
            refine ⟨13881592382242468765795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18953000799221717354898773 13881592382242468765795)
            ·
              rfl

theorem cell22_3284668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 12].length) (baseStart_3284668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284668 prefixEnd_3284668 := by exact prefixLift 3284668
  have htrace : WordTrace (prefixWord ++ tailWord_3284668) baseStart_3284668 baseEnd_3284668 := by
    simpa [prefixWord, tailWord_3284668, baseEnd_3284668] using wordTrace_append hprefix tailTrace_3284668
  have hstable : (prefixWord ++ tailWord_3284668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284668).length < 2 ^ (prefixWord ++ tailWord_3284668).sum := by decide
  have hdescent : baseEnd_3284668 < baseStart_3284668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284672 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 2, 3]
def baseStart_3284672 : Nat := 118140960795 + 3284672 * 2 ^ 59
def prefixEnd_3284672 : Nat := 4983230072969 + 3 ^ 40 * 3284672 * 2
def baseEnd_3284672 : Nat := 1124410352243385292929383

theorem tailTrace_3284672 : CollatzResearch.WordTrace tailWord_3284672 prefixEnd_3284672 1124410352243385292929383 := by
  unfold tailWord_3284672
  simp only [CollatzResearch.WordTrace]
  refine ⟨59900914978100898080512135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79867886637467864107349513 59900914978100898080512135)
  ·
    refine ⟨89851372467151347120768203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59900914978100898080512135 89851372467151347120768203)
    ·
      refine ⟨134777058700727020681152305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89851372467151347120768203 134777058700727020681152305)
      ·
        refine ⟨101082794025545265510864229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134777058700727020681152305 101082794025545265510864229)
        ·
          refine ⟨18953023879789737283287043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101082794025545265510864229 18953023879789737283287043)
          ·
            refine ⟨28429535819684605924930565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18953023879789737283287043 28429535819684605924930565)
            ·
              refine ⟨5330537966190863610924481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28429535819684605924930565 5330537966190863610924481)
              ·
                refine ⟨3997903474643147708193361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5330537966190863610924481 3997903474643147708193361)
                ·
                  refine ⟨2998427605982360781145021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3997903474643147708193361 2998427605982360781145021)
                  ·
                    refine ⟨1124410352243385292929383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998427605982360781145021 1124410352243385292929383)
                    ·
                      rfl

theorem cell22_3284672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_3284672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284672 prefixEnd_3284672 := by exact prefixLift 3284672
  have htrace : WordTrace (prefixWord ++ tailWord_3284672) baseStart_3284672 baseEnd_3284672 := by
    simpa [prefixWord, tailWord_3284672, baseEnd_3284672] using wordTrace_append hprefix tailTrace_3284672
  have hstable : (prefixWord ++ tailWord_3284672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284672).length < 2 ^ (prefixWord ++ tailWord_3284672).sum := by decide
  have hdescent : baseEnd_3284672 < baseStart_3284672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284713 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 7]
def baseStart_3284713 : Nat := 118140960795 + 3284713 * 2 ^ 59
def prefixEnd_3284713 : Nat := 4983230072969 + 3 ^ 40 * 3284713 * 2
def baseEnd_3284713 : Nat := 374808129127091617551419

theorem tailTrace_3284713 : CollatzResearch.WordTrace tailWord_3284713 prefixEnd_3284713 374808129127091617551419 := by
  unfold tailWord_3284713
  simp only [CollatzResearch.WordTrace]
  refine ⟨119803325349053260163266793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79868883566035506775511195 119803325349053260163266793)
  ·
    refine ⟨89852494011789945122450095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119803325349053260163266793 89852494011789945122450095)
    ·
      refine ⟨134778741017684917683675143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89852494011789945122450095 134778741017684917683675143)
      ·
        refine ⟨202168111526527376525512715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134778741017684917683675143 202168111526527376525512715)
        ·
          refine ⟨303252167289791064788269073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202168111526527376525512715 303252167289791064788269073)
          ·
            refine ⟨227439125467343298591201805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303252167289791064788269073 227439125467343298591201805)
            ·
              refine ⟨85289672050253736971700677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227439125467343298591201805 85289672050253736971700677)
              ·
                refine ⟨15991813509422575682193877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85289672050253736971700677 15991813509422575682193877)
                ·
                  refine ⟨374808129127091617551419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15991813509422575682193877 374808129127091617551419)
                  ·
                    rfl

theorem cell22_3284713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_3284713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284713 prefixEnd_3284713 := by exact prefixLift 3284713
  have htrace : WordTrace (prefixWord ++ tailWord_3284713) baseStart_3284713 baseEnd_3284713 := by
    simpa [prefixWord, tailWord_3284713, baseEnd_3284713] using wordTrace_append hprefix tailTrace_3284713
  have hstable : (prefixWord ++ tailWord_3284713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284713).length < 2 ^ (prefixWord ++ tailWord_3284713).sum := by decide
  have hdescent : baseEnd_3284713 < baseStart_3284713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284760 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_3284760 : Nat := 118140960795 + 3284760 * 2 ^ 59
def prefixEnd_3284760 : Nat := 4983230072969 + 3 ^ 40 * 3284760 * 2
def baseEnd_3284760 : Nat := 1124440476441782396729113

theorem tailTrace_3284760 : CollatzResearch.WordTrace tailWord_3284760 prefixEnd_3284760 1124440476441782396729113 := by
  unfold tailWord_3284760
  simp only [CollatzResearch.WordTrace]
  refine ⟨59902519789941493595113867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79870026386588658126818489 59902519789941493595113867)
  ·
    refine ⟨89853779684912240392670801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59902519789941493595113867 89853779684912240392670801)
    ·
      refine ⟨67390334763684180294503101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89853779684912240392670801 67390334763684180294503101)
      ·
        refine ⟨25271375536381567610438663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67390334763684180294503101 25271375536381567610438663)
        ·
          refine ⟨37907063304572351415657995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25271375536381567610438663 37907063304572351415657995)
          ·
            refine ⟨56860594956858527123486993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37907063304572351415657995 56860594956858527123486993)
            ·
              refine ⟨42645446217643895342615245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56860594956858527123486993 42645446217643895342615245)
              ·
                refine ⟨15992042331616460753480717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42645446217643895342615245 15992042331616460753480717)
                ·
                  refine ⟨5997015874356172782555269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15992042331616460753480717 5997015874356172782555269)
                  ·
                    refine ⟨1124440476441782396729113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997015874356172782555269 1124440476441782396729113)
                    ·
                      rfl

theorem cell22_3284760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_3284760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284760 prefixEnd_3284760 := by exact prefixLift 3284760
  have htrace : WordTrace (prefixWord ++ tailWord_3284760) baseStart_3284760 baseEnd_3284760 := by
    simpa [prefixWord, tailWord_3284760, baseEnd_3284760] using wordTrace_append hprefix tailTrace_3284760
  have hstable : (prefixWord ++ tailWord_3284760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284760).length < 2 ^ (prefixWord ++ tailWord_3284760).sum := by decide
  have hdescent : baseEnd_3284760 < baseStart_3284760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284792 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 6]
def baseStart_3284792 : Nat := 118140960795 + 3284792 * 2 ^ 59
def prefixEnd_3284792 : Nat := 4983230072969 + 3 ^ 40 * 3284792 * 2
def baseEnd_3284792 : Nat := 374817143565248326643005

theorem tailTrace_3284792 : CollatzResearch.WordTrace tailWord_3284792 prefixEnd_3284792 374817143565248326643005 := by
  unfold tailWord_3284792
  simp only [CollatzResearch.WordTrace]
  refine ⟨59903103357883528327696315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79870804477178037770261753 59903103357883528327696315)
  ·
    refine ⟨89854655036825292491544473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59903103357883528327696315 89854655036825292491544473)
    ·
      refine ⟨67390991277618969368658355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89854655036825292491544473 67390991277618969368658355)
      ·
        refine ⟨101086486916428454052987533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67390991277618969368658355 101086486916428454052987533)
        ·
          refine ⟨37907432593660670269870325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101086486916428454052987533 37907432593660670269870325)
          ·
            refine ⟨3553821805655687837800343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37907432593660670269870325 3553821805655687837800343)
            ·
              refine ⟨5330732708483531756700515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553821805655687837800343 5330732708483531756700515)
              ·
                refine ⟨7996099062725297635050773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330732708483531756700515 7996099062725297635050773)
                ·
                  refine ⟨374817143565248326643005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7996099062725297635050773 374817143565248326643005)
                  ·
                    rfl

theorem cell22_3284792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_3284792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284792 prefixEnd_3284792 := by exact prefixLift 3284792
  have htrace : WordTrace (prefixWord ++ tailWord_3284792) baseStart_3284792 baseEnd_3284792 := by
    simpa [prefixWord, tailWord_3284792, baseEnd_3284792] using wordTrace_append hprefix tailTrace_3284792
  have hstable : (prefixWord ++ tailWord_3284792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284792).length < 2 ^ (prefixWord ++ tailWord_3284792).sum := by decide
  have hdescent : baseEnd_3284792 < baseStart_3284792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284805 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_3284805 : Nat := 118140960795 + 3284805 * 2 ^ 59
def prefixEnd_3284805 : Nat := 4983230072969 + 3 ^ 40 * 3284805 * 2
def baseEnd_3284805 : Nat := 1124455880861417279353975

theorem tailTrace_3284805 : CollatzResearch.WordTrace tailWord_3284805 prefixEnd_3284805 1124455880861417279353975 := by
  unfold tailWord_3284805
  simp only [CollatzResearch.WordTrace]
  refine ⟨119806680864719959875615869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79871120576479973250410579 119806680864719959875615869)
  ·
    refine ⟨44927505324269984953355951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119806680864719959875615869 44927505324269984953355951)
    ·
      refine ⟨67391257986404977430033927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44927505324269984953355951 67391257986404977430033927)
      ·
        refine ⟨101086886979607466145050891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67391257986404977430033927 101086886979607466145050891)
        ·
          refine ⟨151630330469411199217576337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101086886979607466145050891 151630330469411199217576337)
          ·
            refine ⟨113722747852058399413182253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151630330469411199217576337 113722747852058399413182253)
            ·
              refine ⟨42646030444521899779943345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113722747852058399413182253 42646030444521899779943345)
              ·
                refine ⟨31984522833391424834957509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42646030444521899779943345 31984522833391424834957509)
                ·
                  refine ⟨5997098031260892156554533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31984522833391424834957509 5997098031260892156554533)
                  ·
                    refine ⟨1124455880861417279353975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997098031260892156554533 1124455880861417279353975)
                    ·
                      rfl

theorem cell22_3284805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_3284805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284805 prefixEnd_3284805 := by exact prefixLift 3284805
  have htrace : WordTrace (prefixWord ++ tailWord_3284805) baseStart_3284805 baseEnd_3284805 := by
    simpa [prefixWord, tailWord_3284805, baseEnd_3284805] using wordTrace_append hprefix tailTrace_3284805
  have hstable : (prefixWord ++ tailWord_3284805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284805).length < 2 ^ (prefixWord ++ tailWord_3284805).sum := by decide
  have hdescent : baseEnd_3284805 < baseStart_3284805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284880 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_3284880 : Nat := 118140960795 + 3284880 * 2 ^ 59
def prefixEnd_3284880 : Nat := 4983230072969 + 3 ^ 40 * 3284880 * 2
def baseEnd_3284880 : Nat := 1124481554894142083728745

theorem tailTrace_3284880 : CollatzResearch.WordTrace tailWord_3284880 prefixEnd_3284880 1124481554894142083728745 := by
  unfold tailWord_3284880
  simp only [CollatzResearch.WordTrace]
  refine ⟨59904708169724123842298047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79872944226298831789730729 59904708169724123842298047)
  ·
    refine ⟨89857062254586185763447071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59904708169724123842298047 89857062254586185763447071)
    ·
      refine ⟨134785593381879278645170607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89857062254586185763447071 134785593381879278645170607)
      ·
        refine ⟨202178390072818917967755911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134785593381879278645170607 202178390072818917967755911)
        ·
          refine ⟨303267585109228376951633867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202178390072818917967755911 303267585109228376951633867)
          ·
            refine ⟨454901377663842565427450801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303267585109228376951633867 454901377663842565427450801)
            ·
              refine ⟨341176033247881924070588101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454901377663842565427450801 341176033247881924070588101)
              ·
                refine ⟨63970506233977860763235269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341176033247881924070588101 63970506233977860763235269)
                ·
                  refine ⟨11994469918870848893106613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63970506233977860763235269 11994469918870848893106613)
                  ·
                    refine ⟨1124481554894142083728745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11994469918870848893106613 1124481554894142083728745)
                    ·
                      rfl

theorem cell22_3284880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_3284880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284880 prefixEnd_3284880 := by exact prefixLift 3284880
  have htrace : WordTrace (prefixWord ++ tailWord_3284880) baseStart_3284880 baseEnd_3284880 := by
    simpa [prefixWord, tailWord_3284880, baseEnd_3284880] using wordTrace_append hprefix tailTrace_3284880
  have hstable : (prefixWord ++ tailWord_3284880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284880).length < 2 ^ (prefixWord ++ tailWord_3284880).sum := by decide
  have hdescent : baseEnd_3284880 < baseStart_3284880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284942 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3284942 : Nat := 118140960795 + 3284942 * 2 ^ 59
def prefixEnd_3284942 : Nat := 4983230072969 + 3 ^ 40 * 3284942 * 2
def baseEnd_3284942 : Nat := 1124502778761194588678555

theorem tailTrace_3284942 : CollatzResearch.WordTrace tailWord_3284942 prefixEnd_3284942 1124502778761194588678555 := by
  unfold tailWord_3284942
  simp only [CollatzResearch.WordTrace]
  refine ⟨14976459708152954034169135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79874451776815754848902053 14976459708152954034169135)
  ·
    refine ⟨22464689562229431051253703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14976459708152954034169135 22464689562229431051253703)
    ·
      refine ⟨33697034343344146576880555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22464689562229431051253703 33697034343344146576880555)
      ·
        refine ⟨50545551515016219865320833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33697034343344146576880555 50545551515016219865320833)
        ·
          refine ⟨37909163636262164898990625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50545551515016219865320833 37909163636262164898990625)
          ·
            refine ⟨28431872727196623674242969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37909163636262164898990625 28431872727196623674242969)
            ·
              refine ⟨21323904545397467755682227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28431872727196623674242969 21323904545397467755682227)
              ·
                refine ⟨31985856818096201633523341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21323904545397467755682227 31985856818096201633523341)
                ·
                  refine ⟨11994696306786075612571253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31985856818096201633523341 11994696306786075612571253)
                  ·
                    refine ⟨1124502778761194588678555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11994696306786075612571253 1124502778761194588678555)
                    ·
                      rfl

theorem cell22_3284942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3284942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284942 prefixEnd_3284942 := by exact prefixLift 3284942
  have htrace : WordTrace (prefixWord ++ tailWord_3284942) baseStart_3284942 baseEnd_3284942 := by
    simpa [prefixWord, tailWord_3284942, baseEnd_3284942] using wordTrace_append hprefix tailTrace_3284942
  have hstable : (prefixWord ++ tailWord_3284942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284942).length < 2 ^ (prefixWord ++ tailWord_3284942).sum := by decide
  have hdescent : baseEnd_3284942 < baseStart_3284942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284944 : List Nat := [2, 1, 1, 1, 1, 2, 7, 3, 4]
def baseStart_3284944 : Nat := 118140960795 + 3284944 * 2 ^ 59
def prefixEnd_3284944 : Nat := 4983230072969 + 3 ^ 40 * 3284944 * 2
def baseEnd_3284944 : Nat := 374834487800689083376183

theorem tailTrace_3284944 : CollatzResearch.WordTrace tailWord_3284944 prefixEnd_3284944 374834487800689083376183 := by
  unfold tailWord_3284944
  simp only [CollatzResearch.WordTrace]
  refine ⟨59905875305608193307462943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79874500407477591076617257 59905875305608193307462943)
  ·
    refine ⟨89858812958412289961194415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59905875305608193307462943 89858812958412289961194415)
    ·
      refine ⟨134788219437618434941791623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89858812958412289961194415 134788219437618434941791623)
      ·
        refine ⟨202182329156427652412687435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134788219437618434941791623 202182329156427652412687435)
        ·
          refine ⟨303273493734641478619031153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202182329156427652412687435 303273493734641478619031153)
          ·
            refine ⟨227455120300981108964273365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303273493734641478619031153 227455120300981108964273365)
            ·
              refine ⟨5330979382054244741350157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 227455120300981108964273365 5330979382054244741350157)
              ·
                refine ⟨1999117268270341778006309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5330979382054244741350157 1999117268270341778006309)
                ·
                  refine ⟨374834487800689083376183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999117268270341778006309 374834487800689083376183)
                  ·
                    rfl

theorem cell22_3284944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_3284944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284944 prefixEnd_3284944 := by exact prefixLift 3284944
  have htrace : WordTrace (prefixWord ++ tailWord_3284944) baseStart_3284944 baseEnd_3284944 := by
    simpa [prefixWord, tailWord_3284944, baseEnd_3284944] using wordTrace_append hprefix tailTrace_3284944
  have hstable : (prefixWord ++ tailWord_3284944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284944).length < 2 ^ (prefixWord ++ tailWord_3284944).sum := by decide
  have hdescent : baseEnd_3284944 < baseStart_3284944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284959 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 4, 3]
def baseStart_3284959 : Nat := 118140960795 + 3284959 * 2 ^ 59
def prefixEnd_3284959 : Nat := 4983230072969 + 3 ^ 40 * 3284959 * 2
def baseEnd_3284959 : Nat := 1124508598208612211003503

theorem tailTrace_3284959 : CollatzResearch.WordTrace tailWord_3284959 prefixEnd_3284959 1124508598208612211003503 := by
  unfold tailWord_3284959
  simp only [CollatzResearch.WordTrace]
  refine ⟨119812297706162044176721931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79874865137441362784481287 119812297706162044176721931)
  ·
    refine ⟨179718446559243066265082897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119812297706162044176721931 179718446559243066265082897)
    ·
      refine ⟨134788834919432299698812173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179718446559243066265082897 134788834919432299698812173)
      ·
        refine ⟨50545813094787112387054565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134788834919432299698812173 50545813094787112387054565)
        ·
          refine ⟨9477339955272583572572731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50545813094787112387054565 9477339955272583572572731)
          ·
            refine ⟨14216009932908875358859097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9477339955272583572572731 14216009932908875358859097)
            ·
              refine ⟨10662007449681656519144323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14216009932908875358859097 10662007449681656519144323)
              ·
                refine ⟨15993011174522484778716485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10662007449681656519144323 15993011174522484778716485)
                ·
                  refine ⟨2998689595222965896009341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15993011174522484778716485 2998689595222965896009341)
                  ·
                    refine ⟨1124508598208612211003503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998689595222965896009341 1124508598208612211003503)
                    ·
                      rfl

theorem cell22_3284959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_3284959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284959 prefixEnd_3284959 := by exact prefixLift 3284959
  have htrace : WordTrace (prefixWord ++ tailWord_3284959) baseStart_3284959 baseEnd_3284959 := by
    simpa [prefixWord, tailWord_3284959, baseEnd_3284959] using wordTrace_append hprefix tailTrace_3284959
  have hstable : (prefixWord ++ tailWord_3284959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284959).length < 2 ^ (prefixWord ++ tailWord_3284959).sum := by decide
  have hdescent : baseEnd_3284959 < baseStart_3284959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3284976 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 2, 3]
def baseStart_3284976 : Nat := 118140960795 + 3284976 * 2 ^ 59
def prefixEnd_3284976 : Nat := 4983230072969 + 3 ^ 40 * 3284976 * 2
def baseEnd_3284976 : Nat := 1124514417656029833328451

theorem tailTrace_3284976 : CollatzResearch.WordTrace tailWord_3284976 prefixEnd_3284976 1124514417656029833328451 := by
  unfold tailWord_3284976
  simp only [CollatzResearch.WordTrace]
  refine ⟨59906458873550228040045391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79875278498066970720060521 59906458873550228040045391)
  ·
    refine ⟨89859688310325342060068087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59906458873550228040045391 89859688310325342060068087)
    ·
      refine ⟨134789532465488013090102131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89859688310325342060068087 134789532465488013090102131)
      ·
        refine ⟨202184298698232019635153197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134789532465488013090102131 202184298698232019635153197)
        ·
          refine ⟨75819112011837007363182449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202184298698232019635153197 75819112011837007363182449)
          ·
            refine ⟨56864334008877755522386837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75819112011837007363182449 56864334008877755522386837)
            ·
              refine ⟨2665515656666144790111883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56864334008877755522386837 2665515656666144790111883)
              ·
                refine ⟨3998273484999217185167825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665515656666144790111883 3998273484999217185167825)
                ·
                  refine ⟨2998705113749412888875869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998273484999217185167825 2998705113749412888875869)
                  ·
                    refine ⟨1124514417656029833328451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998705113749412888875869 1124514417656029833328451)
                    ·
                      rfl

theorem cell22_3284976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_3284976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3284976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3284976 prefixEnd_3284976 := by exact prefixLift 3284976
  have htrace : WordTrace (prefixWord ++ tailWord_3284976) baseStart_3284976 baseEnd_3284976 := by
    simpa [prefixWord, tailWord_3284976, baseEnd_3284976] using wordTrace_append hprefix tailTrace_3284976
  have hstable : (prefixWord ++ tailWord_3284976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3284976).length < 2 ^ (prefixWord ++ tailWord_3284976).sum := by decide
  have hdescent : baseEnd_3284976 < baseStart_3284976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3284976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285012 : List Nat := [2, 4, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3285012 : Nat := 118140960795 + 3285012 * 2 ^ 59
def prefixEnd_3285012 : Nat := 4983230072969 + 3 ^ 40 * 3285012 * 2
def baseEnd_3285012 : Nat := 374842247063912579809447

theorem tailTrace_3285012 : CollatzResearch.WordTrace tailWord_3285012 prefixEnd_3285012 374842247063912579809447 := by
  unfold tailWord_3285012
  simp only [CollatzResearch.WordTrace]
  refine ⟨59907115387485017114200645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79876153849980022818934193 59907115387485017114200645)
  ·
    refine ⟨11232584135153440708912621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59907115387485017114200645 11232584135153440708912621)
    ·
      refine ⟨4212219050682540265842233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11232584135153440708912621 4212219050682540265842233)
      ·
        refine ⟨3159164288011905199381675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4212219050682540265842233 3159164288011905199381675)
        ·
          refine ⟨4738746432017857799072513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159164288011905199381675 4738746432017857799072513)
          ·
            refine ⟨3554059824013393349304385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4738746432017857799072513 3554059824013393349304385)
            ·
              refine ⟨2665544868010045011978289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554059824013393349304385 2665544868010045011978289)
              ·
                refine ⟨1999158651007533758983717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665544868010045011978289 1999158651007533758983717)
                ·
                  refine ⟨374842247063912579809447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999158651007533758983717 374842247063912579809447)
                  ·
                    rfl

theorem cell22_3285012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3285012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285012 prefixEnd_3285012 := by exact prefixLift 3285012
  have htrace : WordTrace (prefixWord ++ tailWord_3285012) baseStart_3285012 baseEnd_3285012 := by
    simpa [prefixWord, tailWord_3285012, baseEnd_3285012] using wordTrace_append hprefix tailTrace_3285012
  have hstable : (prefixWord ++ tailWord_3285012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285012).length < 2 ^ (prefixWord ++ tailWord_3285012).sum := by decide
  have hdescent : baseEnd_3285012 < baseStart_3285012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285098 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3285098 : Nat := 118140960795 + 3285098 * 2 ^ 59
def prefixEnd_3285098 : Nat := 4983230072969 + 3 ^ 40 * 3285098 * 2
def baseEnd_3285098 : Nat := 1124556180749262181778077

theorem tailTrace_3285098 : CollatzResearch.WordTrace tailWord_3285098 prefixEnd_3285098 1124556180749262181778077 := by
  unfold tailWord_3285098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29954341863164617729007987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79878244968438980610687965 29954341863164617729007987)
  ·
    refine ⟨44931512794746926593511981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29954341863164617729007987 44931512794746926593511981)
    ·
      refine ⟨16849317298030097472566993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44931512794746926593511981 16849317298030097472566993)
      ·
        refine ⟨12636987973522573104425245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16849317298030097472566993 12636987973522573104425245)
        ·
          refine ⟨4738870490070964914159467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12636987973522573104425245 4738870490070964914159467)
          ·
            refine ⟨7108305735106447371239201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4738870490070964914159467 7108305735106447371239201)
            ·
              refine ⟨5331229301329835528429401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7108305735106447371239201 5331229301329835528429401)
              ·
                refine ⟨3998421975997376646322051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5331229301329835528429401 3998421975997376646322051)
                ·
                  refine ⟨5997632963996064969483077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998421975997376646322051 5997632963996064969483077)
                  ·
                    refine ⟨1124556180749262181778077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997632963996064969483077 1124556180749262181778077)
                    ·
                      rfl

theorem cell22_3285098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3285098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285098 prefixEnd_3285098 := by exact prefixLift 3285098
  have htrace : WordTrace (prefixWord ++ tailWord_3285098) baseStart_3285098 baseEnd_3285098 := by
    simpa [prefixWord, tailWord_3285098, baseEnd_3285098] using wordTrace_append hprefix tailTrace_3285098
  have hstable : (prefixWord ++ tailWord_3285098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285098).length < 2 ^ (prefixWord ++ tailWord_3285098).sum := by decide
  have hdescent : baseEnd_3285098 < baseStart_3285098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285113 : List Nat := [1, 2, 1, 3, 4, 3, 1, 3, 4]
def baseStart_3285113 : Nat := 118140960795 + 3285113 * 2 ^ 59
def prefixEnd_3285113 : Nat := 4983230072969 + 3 ^ 40 * 3285113 * 2
def baseEnd_3285113 : Nat := 374853771851935714217677

theorem tailTrace_3285113 : CollatzResearch.WordTrace tailWord_3285113 prefixEnd_3285113 374853771851935714217677 := by
  unfold tailWord_3285113
  simp only [CollatzResearch.WordTrace]
  refine ⟨119817914547604128477827993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79878609698402752318551995 119817914547604128477827993)
  ·
    refine ⟨89863435910703096358370995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119817914547604128477827993 89863435910703096358370995)
    ·
      refine ⟨134795153866054644537556493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89863435910703096358370995 134795153866054644537556493)
      ·
        refine ⟨50548182699770491701583685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134795153866054644537556493 50548182699770491701583685)
        ·
          refine ⟨9477784256206967194046941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50548182699770491701583685 9477784256206967194046941)
          ·
            refine ⟨3554169096077612697767603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9477784256206967194046941 3554169096077612697767603)
            ·
              refine ⟨5331253644116419046651405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554169096077612697767603 5331253644116419046651405)
              ·
                refine ⟨1999220116543657142494277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5331253644116419046651405 1999220116543657142494277)
                ·
                  refine ⟨374853771851935714217677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999220116543657142494277 374853771851935714217677)
                  ·
                    rfl

theorem cell22_3285113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_3285113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285113 prefixEnd_3285113 := by exact prefixLift 3285113
  have htrace : WordTrace (prefixWord ++ tailWord_3285113) baseStart_3285113 baseEnd_3285113 := by
    simpa [prefixWord, tailWord_3285113, baseEnd_3285113] using wordTrace_append hprefix tailTrace_3285113
  have hstable : (prefixWord ++ tailWord_3285113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285113).length < 2 ^ (prefixWord ++ tailWord_3285113).sum := by decide
  have hdescent : baseEnd_3285113 < baseStart_3285113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285199 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 5, 4]
def baseStart_3285199 : Nat := 118140960795 + 3285199 * 2 ^ 59
def prefixEnd_3285199 : Nat := 4983230072969 + 3 ^ 40 * 3285199 * 2
def baseEnd_3285199 : Nat := 1124590755113331585002767

theorem tailTrace_3285199 : CollatzResearch.WordTrace tailWord_3285199 prefixEnd_3285199 1124590755113331585002767 := by
  unfold tailWord_3285199
  simp only [CollatzResearch.WordTrace]
  refine ⟨119821051225292565165458651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79880700816861710110305767 119821051225292565165458651)
  ·
    refine ⟨179731576837938847748187977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119821051225292565165458651 179731576837938847748187977)
    ·
      refine ⟨134798682628454135811140983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179731576837938847748187977 134798682628454135811140983)
      ·
        refine ⟨202198023942681203716711475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134798682628454135811140983 202198023942681203716711475)
        ·
          refine ⟨303297035914021805575067213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202198023942681203716711475 303297035914021805575067213)
          ·
            refine ⟨113736388467758177090650205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303297035914021805575067213 113736388467758177090650205)
            ·
              refine ⟨42651145675409316408993827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113736388467758177090650205 42651145675409316408993827)
              ·
                refine ⟨63976718513113974613490741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42651145675409316408993827 63976718513113974613490741)
                ·
                  refine ⟨5997817360604435120014757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63976718513113974613490741 5997817360604435120014757)
                  ·
                    refine ⟨1124590755113331585002767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997817360604435120014757 1124590755113331585002767)
                    ·
                      rfl

theorem cell22_3285199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_3285199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285199 prefixEnd_3285199 := by exact prefixLift 3285199
  have htrace : WordTrace (prefixWord ++ tailWord_3285199) baseStart_3285199 baseEnd_3285199 := by
    simpa [prefixWord, tailWord_3285199, baseEnd_3285199] using wordTrace_append hprefix tailTrace_3285199
  have hstable : (prefixWord ++ tailWord_3285199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285199).length < 2 ^ (prefixWord ++ tailWord_3285199).sum := by decide
  have hdescent : baseEnd_3285199 < baseStart_3285199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285216 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_3285216 : Nat := 118140960795 + 3285216 * 2 ^ 59
def prefixEnd_3285216 : Nat := 4983230072969 + 3 ^ 40 * 3285216 * 2
def baseEnd_3285216 : Nat := 1124596574560749207327715

theorem tailTrace_3285216 : CollatzResearch.WordTrace tailWord_3285216 prefixEnd_3285216 1124596574560749207327715 := by
  unfold tailWord_3285216
  simp only [CollatzResearch.WordTrace]
  refine ⟨59910835633115488534413751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79881114177487318045885001 59910835633115488534413751)
  ·
    refine ⟨89866253449673232801620627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59910835633115488534413751 89866253449673232801620627)
    ·
      refine ⟨134799380174509849202430941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89866253449673232801620627 134799380174509849202430941)
      ·
        refine ⟨50549767565441193450911603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134799380174509849202430941 50549767565441193450911603)
        ·
          refine ⟨75824651348161790176367405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50549767565441193450911603 75824651348161790176367405)
          ·
            refine ⟨28434244255560671316137777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75824651348161790176367405 28434244255560671316137777)
            ·
              refine ⟨21325683191670503487103333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28434244255560671316137777 21325683191670503487103333)
              ·
                refine ⟨3998565598438219403831875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21325683191670503487103333 3998565598438219403831875)
                ·
                  refine ⟨5997848397657329105747813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998565598438219403831875 5997848397657329105747813)
                  ·
                    refine ⟨1124596574560749207327715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997848397657329105747813 1124596574560749207327715)
                    ·
                      rfl

theorem cell22_3285216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_3285216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285216 prefixEnd_3285216 := by exact prefixLift 3285216
  have htrace : WordTrace (prefixWord ++ tailWord_3285216) baseStart_3285216 baseEnd_3285216 := by
    simpa [prefixWord, tailWord_3285216, baseEnd_3285216] using wordTrace_append hprefix tailTrace_3285216
  have hstable : (prefixWord ++ tailWord_3285216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285216).length < 2 ^ (prefixWord ++ tailWord_3285216).sum := by decide
  have hdescent : baseEnd_3285216 < baseStart_3285216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285233 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 1, 4]
def baseStart_3285233 : Nat := 118140960795 + 3285233 * 2 ^ 59
def prefixEnd_3285233 : Nat := 4983230072969 + 3 ^ 40 * 3285233 * 2
def baseEnd_3285233 : Nat := 1124602394008166829652663

theorem tailTrace_3285233 : CollatzResearch.WordTrace tailWord_3285233 prefixEnd_3285233 1124602394008166829652663 := by
  unfold tailWord_3285233
  simp only [CollatzResearch.WordTrace]
  refine ⟨119822291307169388972196353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79881527538112925981464235 119822291307169388972196353)
  ·
    refine ⟨89866718480377041729147265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119822291307169388972196353 89866718480377041729147265)
    ·
      refine ⟨67400038860282781296860449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89866718480377041729147265 67400038860282781296860449)
      ·
        refine ⟨50550029145212085972645337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67400038860282781296860449 50550029145212085972645337)
        ·
          refine ⟨37912521858909064479484003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50550029145212085972645337 37912521858909064479484003)
          ·
            refine ⟨56868782788363596719226005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37912521858909064479484003 56868782788363596719226005)
            ·
              refine ⟨2665724193204543596213719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56868782788363596719226005 2665724193204543596213719)
              ·
                refine ⟨3998586289806815394320579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665724193204543596213719 3998586289806815394320579)
                ·
                  refine ⟨5997879434710223091480869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998586289806815394320579 5997879434710223091480869)
                  ·
                    refine ⟨1124602394008166829652663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997879434710223091480869 1124602394008166829652663)
                    ·
                      rfl

theorem cell22_3285233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_3285233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285233 prefixEnd_3285233 := by exact prefixLift 3285233
  have htrace : WordTrace (prefixWord ++ tailWord_3285233) baseStart_3285233 baseEnd_3285233 := by
    simpa [prefixWord, tailWord_3285233, baseEnd_3285233] using wordTrace_append hprefix tailTrace_3285233
  have hstable : (prefixWord ++ tailWord_3285233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285233).length < 2 ^ (prefixWord ++ tailWord_3285233).sum := by decide
  have hdescent : baseEnd_3285233 < baseStart_3285233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285259 : List Nat := [1, 1, 1, 1, 5, 2, 2, 9]
def baseStart_3285259 : Nat := 118140960795 + 3285259 * 2 ^ 59
def prefixEnd_3285259 : Nat := 4983230072969 + 3 ^ 40 * 3285259 * 2
def baseEnd_3285259 : Nat := 124956810482167936500287

theorem tailTrace_3285259 : CollatzResearch.WordTrace tailWord_3285259 prefixEnd_3285259 124956810482167936500287 := by
  unfold tailWord_3285259
  simp only [CollatzResearch.WordTrace]
  refine ⟨119823239605075195412642831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79882159736716796941761887 119823239605075195412642831)
  ·
    refine ⟨179734859407612793118964247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119823239605075195412642831 179734859407612793118964247)
    ·
      refine ⟨269602289111419189678446371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179734859407612793118964247 269602289111419189678446371)
      ·
        refine ⟨404403433667128784517669557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269602289111419189678446371 404403433667128784517669557)
        ·
          refine ⟨37912821906293323548531521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404403433667128784517669557 37912821906293323548531521)
          ·
            refine ⟨28434616429719992661398641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37912821906293323548531521 28434616429719992661398641)
            ·
              refine ⟨21325962322289994496048981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28434616429719992661398641 21325962322289994496048981)
              ·
                refine ⟨124956810482167936500287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21325962322289994496048981 124956810482167936500287)
                ·
                  rfl

theorem cell22_3285259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 9].length) (baseStart_3285259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285259 prefixEnd_3285259 := by exact prefixLift 3285259
  have htrace : WordTrace (prefixWord ++ tailWord_3285259) baseStart_3285259 baseEnd_3285259 := by
    simpa [prefixWord, tailWord_3285259, baseEnd_3285259] using wordTrace_append hprefix tailTrace_3285259
  have hstable : (prefixWord ++ tailWord_3285259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285259).length < 2 ^ (prefixWord ++ tailWord_3285259).sum := by decide
  have hdescent : baseEnd_3285259 < baseStart_3285259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285400 : List Nat := [2, 1, 2, 5, 1, 1, 1, 5, 4]
def baseStart_3285400 : Nat := 118140960795 + 3285400 * 2 ^ 59
def prefixEnd_3285400 : Nat := 4983230072969 + 3 ^ 40 * 3285400 * 2
def baseEnd_3285400 : Nat := 374886520507011353575717

theorem tailTrace_3285400 : CollatzResearch.WordTrace tailWord_3285400 prefixEnd_3285400 374886520507011353575717 := by
  unfold tailWord_3285400
  simp only [CollatzResearch.WordTrace]
  refine ⟨59914191148782188246762827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79885588198376250995683769 59914191148782188246762827)
  ·
    refine ⟨89871286723173282370144241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59914191148782188246762827 89871286723173282370144241)
    ·
      refine ⟨67403465042379961777608181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89871286723173282370144241 67403465042379961777608181)
      ·
        refine ⟨6319074847723121416650767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67403465042379961777608181 6319074847723121416650767)
        ·
          refine ⟨9478612271584682124976151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6319074847723121416650767 9478612271584682124976151)
          ·
            refine ⟨14217918407377023187464227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9478612271584682124976151 14217918407377023187464227)
            ·
              refine ⟨21326877611065534781196341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14217918407377023187464227 21326877611065534781196341)
              ·
                refine ⟨1999394776037393885737157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21326877611065534781196341 1999394776037393885737157)
                ·
                  refine ⟨374886520507011353575717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999394776037393885737157 374886520507011353575717)
                  ·
                    rfl

theorem cell22_3285400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_3285400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285400 prefixEnd_3285400 := by exact prefixLift 3285400
  have htrace : WordTrace (prefixWord ++ tailWord_3285400) baseStart_3285400 baseEnd_3285400 := by
    simpa [prefixWord, tailWord_3285400, baseEnd_3285400] using wordTrace_append hprefix tailTrace_3285400
  have hstable : (prefixWord ++ tailWord_3285400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285400).length < 2 ^ (prefixWord ++ tailWord_3285400).sum := by decide
  have hdescent : baseEnd_3285400 < baseStart_3285400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285402 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_3285402 : Nat := 118140960795 + 3285402 * 2 ^ 59
def prefixEnd_3285402 : Nat := 4983230072969 + 3 ^ 40 * 3285402 * 2
def baseEnd_3285402 : Nat := 1124660246161906722177145

theorem tailTrace_3285402 : CollatzResearch.WordTrace tailWord_3285402 prefixEnd_3285402 1124660246161906722177145 := by
  unfold tailWord_3285402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29957113810889282708774615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79885636829038087223398973 29957113810889282708774615)
  ·
    refine ⟨44935670716333924063161923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29957113810889282708774615 44935670716333924063161923)
    ·
      refine ⟨67403506074500886094742885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44935670716333924063161923 67403506074500886094742885)
      ·
        refine ⟨12638157388968916142764291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67403506074500886094742885 12638157388968916142764291)
        ·
          refine ⟨18957236083453374214146437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12638157388968916142764291 18957236083453374214146437)
          ·
            refine ⟨3554481765647507665152457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18957236083453374214146437 3554481765647507665152457)
            ·
              refine ⟨2665861324235630748864343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554481765647507665152457 2665861324235630748864343)
              ·
                refine ⟨3998791986353446123296515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665861324235630748864343 3998791986353446123296515)
                ·
                  refine ⟨5998187979530169184944773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998791986353446123296515 5998187979530169184944773)
                  ·
                    refine ⟨1124660246161906722177145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5998187979530169184944773 1124660246161906722177145)
                    ·
                      rfl

theorem cell22_3285402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_3285402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285402 prefixEnd_3285402 := by exact prefixLift 3285402
  have htrace : WordTrace (prefixWord ++ tailWord_3285402) baseStart_3285402 baseEnd_3285402 := by
    simpa [prefixWord, tailWord_3285402, baseEnd_3285402] using wordTrace_append hprefix tailTrace_3285402
  have hstable : (prefixWord ++ tailWord_3285402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285402).length < 2 ^ (prefixWord ++ tailWord_3285402).sum := by decide
  have hdescent : baseEnd_3285402 < baseStart_3285402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285411 : List Nat := [1, 1, 1, 4, 1, 5, 9]
def baseStart_3285411 : Nat := 118140960795 + 3285411 * 2 ^ 59
def prefixEnd_3285411 : Nat := 4983230072969 + 3 ^ 40 * 3285411 * 2
def baseEnd_3285411 : Nat := 41654197297993840692671

theorem tailTrace_3285411 : CollatzResearch.WordTrace tailWord_3285411 prefixEnd_3285411 41654197297993840692671 := by
  unfold tailWord_3285411
  simp only [CollatzResearch.WordTrace]
  refine ⟨119828783500524525372176087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79885855667016350248117391 119828783500524525372176087)
  ·
    refine ⟨179743175250786788058264131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119828783500524525372176087 179743175250786788058264131)
    ·
      refine ⟨269614762876180182087396197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179743175250786788058264131 269614762876180182087396197)
      ·
        refine ⟨50552768039283784141386787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269614762876180182087396197 50552768039283784141386787)
        ·
          refine ⟨75829152058925676212080181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50552768039283784141386787 75829152058925676212080181)
          ·
            refine ⟨7108983005524282144882517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75829152058925676212080181 7108983005524282144882517)
            ·
              refine ⟨41654197297993840692671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7108983005524282144882517 41654197297993840692671)
              ·
                rfl

theorem cell22_3285411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 9].length) (baseStart_3285411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285411 prefixEnd_3285411 := by exact prefixLift 3285411
  have htrace : WordTrace (prefixWord ++ tailWord_3285411) baseStart_3285411 baseEnd_3285411 := by
    simpa [prefixWord, tailWord_3285411, baseEnd_3285411] using wordTrace_append hprefix tailTrace_3285411
  have hstable : (prefixWord ++ tailWord_3285411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285411).length < 2 ^ (prefixWord ++ tailWord_3285411).sum := by decide
  have hdescent : baseEnd_3285411 < baseStart_3285411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285415 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3285415 : Nat := 118140960795 + 3285415 * 2 ^ 59
def prefixEnd_3285415 : Nat := 4983230072969 + 3 ^ 40 * 3285415 * 2
def baseEnd_3285415 : Nat := 1124664696327579021602105

theorem tailTrace_3285415 : CollatzResearch.WordTrace tailWord_3285415 prefixEnd_3285415 1124664696327579021602105 := by
  unfold tailWord_3285415
  simp only [CollatzResearch.WordTrace]
  refine ⟨119828929392510034055321699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79885952928340022703547799 119828929392510034055321699)
  ·
    refine ⟨179743394088765051082982549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119828929392510034055321699 179743394088765051082982549)
    ·
      refine ⟨8425471597910861769514807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179743394088765051082982549 8425471597910861769514807)
      ·
        refine ⟨12638207396866292654272211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8425471597910861769514807 12638207396866292654272211)
        ·
          refine ⟨18957311095299438981408317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12638207396866292654272211 18957311095299438981408317)
          ·
            refine ⟨7108991660737289618028119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18957311095299438981408317 7108991660737289618028119)
            ·
              refine ⟨10663487491105934427042179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108991660737289618028119 10663487491105934427042179)
              ·
                refine ⟨15995231236658901640563269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10663487491105934427042179 15995231236658901640563269)
                ·
                  refine ⟨2999105856873544057605613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15995231236658901640563269 2999105856873544057605613)
                  ·
                    refine ⟨1124664696327579021602105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999105856873544057605613 1124664696327579021602105)
                    ·
                      rfl

theorem cell22_3285415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3285415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285415 prefixEnd_3285415 := by exact prefixLift 3285415
  have htrace : WordTrace (prefixWord ++ tailWord_3285415) baseStart_3285415 baseEnd_3285415 := by
    simpa [prefixWord, tailWord_3285415, baseEnd_3285415] using wordTrace_append hprefix tailTrace_3285415
  have hstable : (prefixWord ++ tailWord_3285415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285415).length < 2 ^ (prefixWord ++ tailWord_3285415).sum := by decide
  have hdescent : baseEnd_3285415 < baseStart_3285415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285473 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 5]
def baseStart_3285473 : Nat := 118140960795 + 3285473 * 2 ^ 59
def prefixEnd_3285473 : Nat := 4983230072969 + 3 ^ 40 * 3285473 * 2
def baseEnd_3285473 : Nat := 374894850304295401217309

theorem tailTrace_3285473 : CollatzResearch.WordTrace tailWord_3285473 prefixEnd_3285473 374894850304295401217309 := by
  unfold tailWord_3285473
  simp only [CollatzResearch.WordTrace]
  refine ⟨119831044826299909960933073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79887363217533273307288715 119831044826299909960933073)
  ·
    refine ⟨89873283619724932470699805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119831044826299909960933073 89873283619724932470699805)
    ·
      refine ⟨33702481357396849676512427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89873283619724932470699805 33702481357396849676512427)
      ·
        refine ⟨50553722036095274514768641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33702481357396849676512427 50553722036095274514768641)
        ·
          refine ⟨37915291527071455886076481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50553722036095274514768641 37915291527071455886076481)
          ·
            refine ⟨28436468645303591914557361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37915291527071455886076481 28436468645303591914557361)
            ·
              refine ⟨21327351483977693935918021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28436468645303591914557361 21327351483977693935918021)
              ·
                refine ⟨3998878403245817612984629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21327351483977693935918021 3998878403245817612984629)
                ·
                  refine ⟨374894850304295401217309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3998878403245817612984629 374894850304295401217309)
                  ·
                    rfl

theorem cell22_3285473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_3285473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285473 prefixEnd_3285473 := by exact prefixLift 3285473
  have htrace : WordTrace (prefixWord ++ tailWord_3285473) baseStart_3285473 baseEnd_3285473 := by
    simpa [prefixWord, tailWord_3285473, baseEnd_3285473] using wordTrace_append hprefix tailTrace_3285473
  have hstable : (prefixWord ++ tailWord_3285473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285473).length < 2 ^ (prefixWord ++ tailWord_3285473).sum := by decide
  have hdescent : baseEnd_3285473 < baseStart_3285473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285503 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 3, 4]
def baseStart_3285503 : Nat := 118140960795 + 3285503 * 2 ^ 59
def prefixEnd_3285503 : Nat := 4983230072969 + 3 ^ 40 * 3285503 * 2
def baseEnd_3285503 : Nat := 1124694820525976125401835

theorem tailTrace_3285503 : CollatzResearch.WordTrace tailWord_3285503 prefixEnd_3285503 1124694820525976125401835 := by
  unfold tailWord_3285503
  simp only [CollatzResearch.WordTrace]
  refine ⟨119832139016191225084525163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79888092677460816723016775 119832139016191225084525163)
  ·
    refine ⟨179748208524286837626787745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119832139016191225084525163 179748208524286837626787745)
    ·
      refine ⟨134811156393215128220090809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179748208524286837626787745 134811156393215128220090809)
      ·
        refine ⟨101108367294911346165068107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134811156393215128220090809 101108367294911346165068107)
        ·
          refine ⟨151662550942367019247602161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101108367294911346165068107 151662550942367019247602161)
          ·
            refine ⟨113746913206775264435701621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151662550942367019247602161 113746913206775264435701621)
            ·
              refine ⟨10663773113135181040847027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113746913206775264435701621 10663773113135181040847027)
              ·
                refine ⟨15995659669702771561270541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10663773113135181040847027 15995659669702771561270541)
                ·
                  refine ⟨5998372376138539335476453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15995659669702771561270541 5998372376138539335476453)
                  ·
                    refine ⟨1124694820525976125401835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5998372376138539335476453 1124694820525976125401835)
                    ·
                      rfl

theorem cell22_3285503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_3285503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285503 prefixEnd_3285503 := by exact prefixLift 3285503
  have htrace : WordTrace (prefixWord ++ tailWord_3285503) baseStart_3285503 baseEnd_3285503 := by
    simpa [prefixWord, tailWord_3285503, baseEnd_3285503] using wordTrace_append hprefix tailTrace_3285503
  have hstable : (prefixWord ++ tailWord_3285503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285503).length < 2 ^ (prefixWord ++ tailWord_3285503).sum := by decide
  have hdescent : baseEnd_3285503 < baseStart_3285503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285548 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_3285548 : Nat := 118140960795 + 3285548 * 2 ^ 59
def prefixEnd_3285548 : Nat := 4983230072969 + 3 ^ 40 * 3285548 * 2
def baseEnd_3285548 : Nat := 1124710224945611008026697

theorem tailTrace_3285548 : CollatzResearch.WordTrace tailWord_3285548 prefixEnd_3285548 1124710224945611008026697 := by
  unfold tailWord_3285548
  simp only [CollatzResearch.WordTrace]
  refine ⟨59916890150514098884956649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79889186867352131846608865 59916890150514098884956649)
  ·
    refine ⟨44937667612885574163717487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59916890150514098884956649 44937667612885574163717487)
    ·
      refine ⟨67406501419328361245576231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44937667612885574163717487 67406501419328361245576231)
      ·
        refine ⟨101109752128992541868364347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67406501419328361245576231 101109752128992541868364347)
        ·
          refine ⟨151664628193488812802546521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101109752128992541868364347 151664628193488812802546521)
          ·
            refine ⟨113748471145116609601909891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151664628193488812802546521 113748471145116609601909891)
            ·
              refine ⟨170622706717674914402864837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113748471145116609601909891 170622706717674914402864837)
              ·
                refine ⟨31991757509564046450537157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170622706717674914402864837 31991757509564046450537157)
                ·
                  refine ⟨5998454533043258709475717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31991757509564046450537157 5998454533043258709475717)
                  ·
                    refine ⟨1124710224945611008026697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5998454533043258709475717 1124710224945611008026697)
                    ·
                      rfl

theorem cell22_3285548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_3285548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285548 prefixEnd_3285548 := by exact prefixLift 3285548
  have htrace : WordTrace (prefixWord ++ tailWord_3285548) baseStart_3285548 baseEnd_3285548 := by
    simpa [prefixWord, tailWord_3285548, baseEnd_3285548] using wordTrace_append hprefix tailTrace_3285548
  have hstable : (prefixWord ++ tailWord_3285548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285548).length < 2 ^ (prefixWord ++ tailWord_3285548).sum := by decide
  have hdescent : baseEnd_3285548 < baseStart_3285548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285565 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_3285565 : Nat := 118140960795 + 3285565 * 2 ^ 59
def prefixEnd_3285565 : Nat := 4983230072969 + 3 ^ 40 * 3285565 * 2
def baseEnd_3285565 : Nat := 1124716044393028630351645

theorem tailTrace_3285565 : CollatzResearch.WordTrace tailWord_3285565 prefixEnd_3285565 1124716044393028630351645 := by
  unfold tailWord_3285565
  simp only [CollatzResearch.WordTrace]
  refine ⟨119834400341966609673282149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79889600227977739782188099 119834400341966609673282149)
  ·
    refine ⟨22468950064118739313740403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119834400341966609673282149 22468950064118739313740403)
    ·
      refine ⟨33703425096178108970610605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22468950064118739313740403 33703425096178108970610605)
      ·
        refine ⟨12638784411066790863978977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33703425096178108970610605 12638784411066790863978977)
        ·
          refine ⟨9479088308300093147984233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12638784411066790863978977 9479088308300093147984233)
          ·
            refine ⟨7109316231225069860988175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9479088308300093147984233 7109316231225069860988175)
            ·
              refine ⟨10663974346837604791482263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109316231225069860988175 10663974346837604791482263)
              ·
                refine ⟨15995961520256407187223395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10663974346837604791482263 15995961520256407187223395)
                ·
                  refine ⟨23993942280384610780835093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15995961520256407187223395 23993942280384610780835093)
                  ·
                    refine ⟨1124716044393028630351645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23993942280384610780835093 1124716044393028630351645)
                    ·
                      rfl

theorem cell22_3285565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_3285565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285565 prefixEnd_3285565 := by exact prefixLift 3285565
  have htrace : WordTrace (prefixWord ++ tailWord_3285565) baseStart_3285565 baseEnd_3285565 := by
    simpa [prefixWord, tailWord_3285565, baseEnd_3285565] using wordTrace_append hprefix tailTrace_3285565
  have hstable : (prefixWord ++ tailWord_3285565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285565).length < 2 ^ (prefixWord ++ tailWord_3285565).sum := by decide
  have hdescent : baseEnd_3285565 < baseStart_3285565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285623 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 1, 7]
def baseStart_3285623 : Nat := 118140960795 + 3285623 * 2 ^ 59
def prefixEnd_3285623 : Nat := 4983230072969 + 3 ^ 40 * 3285623 * 2
def baseEnd_3285623 : Nat := 1124735898978335812401467

theorem tailTrace_3285623 : CollatzResearch.WordTrace tailWord_3285623 prefixEnd_3285623 1124735898978335812401467 := by
  unfold tailWord_3285623
  simp only [CollatzResearch.WordTrace]
  refine ⟨119836515775756485578893523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79891010517170990385929015 119836515775756485578893523)
  ·
    refine ⟨179754773663634728368340285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119836515775756485578893523 179754773663634728368340285)
    ·
      refine ⟨67408040123863023138127607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179754773663634728368340285 67408040123863023138127607)
      ·
        refine ⟨101112060185794534707191411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67408040123863023138127607 101112060185794534707191411)
        ·
          refine ⟨151668090278691802060787117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101112060185794534707191411 151668090278691802060787117)
          ·
            refine ⟨56875533854509425772795169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151668090278691802060787117 56875533854509425772795169)
            ·
              refine ⟨42656650390882069329596377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56875533854509425772795169 42656650390882069329596377)
              ·
                refine ⟨31992487793161551997197283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42656650390882069329596377 31992487793161551997197283)
                ·
                  refine ⟨47988731689742327995795925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31992487793161551997197283 47988731689742327995795925)
                  ·
                    refine ⟨1124735898978335812401467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47988731689742327995795925 1124735898978335812401467)
                    ·
                      rfl

theorem cell22_3285623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_3285623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285623 prefixEnd_3285623 := by exact prefixLift 3285623
  have htrace : WordTrace (prefixWord ++ tailWord_3285623) baseStart_3285623 baseEnd_3285623 := by
    simpa [prefixWord, tailWord_3285623, baseEnd_3285623] using wordTrace_append hprefix tailTrace_3285623
  have hstable : (prefixWord ++ tailWord_3285623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285623).length < 2 ^ (prefixWord ++ tailWord_3285623).sum := by decide
  have hdescent : baseEnd_3285623 < baseStart_3285623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285646 : List Nat := [4, 1, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3285646 : Nat := 118140960795 + 3285646 * 2 ^ 59
def prefixEnd_3285646 : Nat := 4983230072969 + 3 ^ 40 * 3285646 * 2
def baseEnd_3285646 : Nat := 1124743772348371419076397

theorem tailTrace_3285646 : CollatzResearch.WordTrace tailWord_3285646 prefixEnd_3285646 1124743772348371419076397 := by
  unfold tailWord_3285646
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979669331834145063372599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79891569769782107004653861 14979669331834145063372599)
  ·
    refine ⟨22469503997751217595058899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14979669331834145063372599 22469503997751217595058899)
    ·
      refine ⟨33704255996626826392588349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22469503997751217595058899 33704255996626826392588349)
      ·
        refine ⟨12639095998735059897220631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33704255996626826392588349 12639095998735059897220631)
        ·
          refine ⟨18958643998102589845830947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12639095998735059897220631 18958643998102589845830947)
          ·
            refine ⟨28437965997153884768746421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18958643998102589845830947 28437965997153884768746421)
            ·
              refine ⟨2666059312233176697069977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28437965997153884768746421 2666059312233176697069977)
              ·
                refine ⟨1999544484174882522802483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666059312233176697069977 1999544484174882522802483)
                ·
                  refine ⟨2999316726262323784203725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999544484174882522802483 2999316726262323784203725)
                  ·
                    refine ⟨1124743772348371419076397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999316726262323784203725 1124743772348371419076397)
                    ·
                      rfl

theorem cell22_3285646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3285646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285646 prefixEnd_3285646 := by exact prefixLift 3285646
  have htrace : WordTrace (prefixWord ++ tailWord_3285646) baseStart_3285646 baseEnd_3285646 := by
    simpa [prefixWord, tailWord_3285646, baseEnd_3285646] using wordTrace_append hprefix tailTrace_3285646
  have hstable : (prefixWord ++ tailWord_3285646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285646).length < 2 ^ (prefixWord ++ tailWord_3285646).sum := by decide
  have hdescent : baseEnd_3285646 < baseStart_3285646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285655 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 3, 4]
def baseStart_3285655 : Nat := 118140960795 + 3285655 * 2 ^ 59
def prefixEnd_3285655 : Nat := 4983230072969 + 3 ^ 40 * 3285655 * 2
def baseEnd_3285655 : Nat := 1124746853232298395601369

theorem tailTrace_3285655 : CollatzResearch.WordTrace tailWord_3285655 prefixEnd_3285655 1124746853232298395601369 := by
  unfold tailWord_3285655
  simp only [CollatzResearch.WordTrace]
  refine ⟨119837682911640555044058419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79891788607760370029372279 119837682911640555044058419)
  ·
    refine ⟨179756524367460832566087629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119837682911640555044058419 179756524367460832566087629)
    ·
      refine ⟨67408696637797812212282861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179756524367460832566087629 67408696637797812212282861)
      ·
        refine ⟨25278261239174179579606073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67408696637797812212282861 25278261239174179579606073)
        ·
          refine ⟨18958695929380634684704555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25278261239174179579606073 18958695929380634684704555)
          ·
            refine ⟨28438043894070952027056833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18958695929380634684704555 28438043894070952027056833)
            ·
              refine ⟨21328532920553214020292625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28438043894070952027056833 21328532920553214020292625)
              ·
                refine ⟨15996399690414910515219469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21328532920553214020292625 15996399690414910515219469)
                ·
                  refine ⟨5998649883905591443207301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15996399690414910515219469 5998649883905591443207301)
                  ·
                    refine ⟨1124746853232298395601369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5998649883905591443207301 1124746853232298395601369)
                    ·
                      rfl

theorem cell22_3285655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_3285655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285655 prefixEnd_3285655 := by exact prefixLift 3285655
  have htrace : WordTrace (prefixWord ++ tailWord_3285655) baseStart_3285655 baseEnd_3285655 := by
    simpa [prefixWord, tailWord_3285655, baseEnd_3285655] using wordTrace_append hprefix tailTrace_3285655
  have hstable : (prefixWord ++ tailWord_3285655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285655).length < 2 ^ (prefixWord ++ tailWord_3285655).sum := by decide
  have hdescent : baseEnd_3285655 < baseStart_3285655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285697 : List Nat := [1, 2, 6, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3285697 : Nat := 118140960795 + 3285697 * 2 ^ 59
def prefixEnd_3285697 : Nat := 4983230072969 + 3 ^ 40 * 3285697 * 2
def baseEnd_3285697 : Nat := 1124761230690624286051241

theorem tailTrace_3285697 : CollatzResearch.WordTrace tailWord_3285697 prefixEnd_3285697 1124761230690624286051241 := by
  unfold tailWord_3285697
  simp only [CollatzResearch.WordTrace]
  refine ⟨119839214777488396217087345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79892809851658930811391563 119839214777488396217087345)
  ·
    refine ⟨89879411083116297162815509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119839214777488396217087345 89879411083116297162815509)
    ·
      refine ⟨4213097394521076429506977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89879411083116297162815509 4213097394521076429506977)
      ·
        refine ⟨3159823045890807322130233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4213097394521076429506977 3159823045890807322130233)
        ·
          refine ⟨2369867284418105491597675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3159823045890807322130233 2369867284418105491597675)
          ·
            refine ⟨3554800926627158237396513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369867284418105491597675 3554800926627158237396513)
            ·
              refine ⟨2666100694970368678047385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554800926627158237396513 2666100694970368678047385)
              ·
                refine ⟨1999575521227776508535539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666100694970368678047385 1999575521227776508535539)
                ·
                  refine ⟨2999363281841664762803309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999575521227776508535539 2999363281841664762803309)
                  ·
                    refine ⟨1124761230690624286051241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999363281841664762803309 1124761230690624286051241)
                    ·
                      rfl

theorem cell22_3285697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3285697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285697 prefixEnd_3285697 := by exact prefixLift 3285697
  have htrace : WordTrace (prefixWord ++ tailWord_3285697) baseStart_3285697 baseEnd_3285697 := by
    simpa [prefixWord, tailWord_3285697, baseEnd_3285697] using wordTrace_append hprefix tailTrace_3285697
  have hstable : (prefixWord ++ tailWord_3285697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285697).length < 2 ^ (prefixWord ++ tailWord_3285697).sum := by decide
  have hdescent : baseEnd_3285697 < baseStart_3285697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285704 : List Nat := [2, 1, 3, 1, 2, 3, 4, 2, 4]
def baseStart_3285704 : Nat := 118140960795 + 3285704 * 2 ^ 59
def prefixEnd_3285704 : Nat := 4983230072969 + 3 ^ 40 * 3285704 * 2
def baseEnd_3285704 : Nat := 374921208977892867042073

theorem tailTrace_3285704 : CollatzResearch.WordTrace tailWord_3285704 prefixEnd_3285704 374921208977892867042073 := by
  unfold tailWord_3285704
  simp only [CollatzResearch.WordTrace]
  refine ⟨59919735044231518206296083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79892980058975357608394777 59919735044231518206296083)
  ·
    refine ⟨89879602566347277309444125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59919735044231518206296083 89879602566347277309444125)
    ·
      refine ⟨33704850962380228991041547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89879602566347277309444125 33704850962380228991041547)
      ·
        refine ⟨50557276443570343486562321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33704850962380228991041547 50557276443570343486562321)
        ·
          refine ⟨37917957332677757614921741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50557276443570343486562321 37917957332677757614921741)
          ·
            refine ⟨14219233999754159105595653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37917957332677757614921741 14219233999754159105595653)
            ·
              refine ⟨2666106374953904832299185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14219233999754159105595653 2666106374953904832299185)
              ·
                refine ⟨1999579781215428624224389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666106374953904832299185 1999579781215428624224389)
                ·
                  refine ⟨374921208977892867042073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999579781215428624224389 374921208977892867042073)
                  ·
                    rfl

theorem cell22_3285704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_3285704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285704 prefixEnd_3285704 := by exact prefixLift 3285704
  have htrace : WordTrace (prefixWord ++ tailWord_3285704) baseStart_3285704 baseEnd_3285704 := by
    simpa [prefixWord, tailWord_3285704, baseEnd_3285704] using wordTrace_append hprefix tailTrace_3285704
  have hstable : (prefixWord ++ tailWord_3285704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285704).length < 2 ^ (prefixWord ++ tailWord_3285704).sum := by decide
  have hdescent : baseEnd_3285704 < baseStart_3285704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285732 : List Nat := [2, 3, 1, 1, 1, 5, 3, 6]
def baseStart_3285732 : Nat := 118140960795 + 3285732 * 2 ^ 59
def prefixEnd_3285732 : Nat := 4983230072969 + 3 ^ 40 * 3285732 * 2
def baseEnd_3285732 : Nat := 124974801322877317936237

theorem tailTrace_3285732 : CollatzResearch.WordTrace tailWord_3285732 prefixEnd_3285732 124974801322877317936237 := by
  unfold tailWord_3285732
  simp only [CollatzResearch.WordTrace]
  refine ⟨59920245666180798597305725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79893660888241064796407633 59920245666180798597305725)
  ·
    refine ⟨22470092124817799473989647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59920245666180798597305725 22470092124817799473989647)
    ·
      refine ⟨33705138187226699210984471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22470092124817799473989647 33705138187226699210984471)
      ·
        refine ⟨50557707280840048816476707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33705138187226699210984471 50557707280840048816476707)
        ·
          refine ⟨75836560921260073224715061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50557707280840048816476707 75836560921260073224715061)
          ·
            refine ⟨7109677586368131864817037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75836560921260073224715061 7109677586368131864817037)
            ·
              refine ⟨2666129094888049449306389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7109677586368131864817037 2666129094888049449306389)
              ·
                refine ⟨124974801322877317936237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2666129094888049449306389 124974801322877317936237)
                ·
                  rfl

theorem cell22_3285732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 6].length) (baseStart_3285732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285732 prefixEnd_3285732 := by exact prefixLift 3285732
  have htrace : WordTrace (prefixWord ++ tailWord_3285732) baseStart_3285732 baseEnd_3285732 := by
    simpa [prefixWord, tailWord_3285732, baseEnd_3285732] using wordTrace_append hprefix tailTrace_3285732
  have hstable : (prefixWord ++ tailWord_3285732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285732).length < 2 ^ (prefixWord ++ tailWord_3285732).sum := by decide
  have hdescent : baseEnd_3285732 < baseStart_3285732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285764 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_3285764 : Nat := 118140960795 + 3285764 * 2 ^ 59
def prefixEnd_3285764 : Nat := 4983230072969 + 3 ^ 40 * 3285764 * 2
def baseEnd_3285764 : Nat := 1124784166159858444626035

theorem tailTrace_3285764 : CollatzResearch.WordTrace tailWord_3285764 prefixEnd_3285764 1124784166159858444626035 := by
  unfold tailWord_3285764
  simp only [CollatzResearch.WordTrace]
  refine ⟨59920829234122833329888173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79894438978830444439850897 59920829234122833329888173)
  ·
    refine ⟨22470310962796062498708065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59920829234122833329888173 22470310962796062498708065)
    ·
      refine ⟨16852733222097046874031049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22470310962796062498708065 16852733222097046874031049)
      ·
        refine ⟨12639549916572785155523287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16852733222097046874031049 12639549916572785155523287)
        ·
          refine ⟨18959324874859177733284931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12639549916572785155523287 18959324874859177733284931)
          ·
            refine ⟨28438987312288766599927397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18959324874859177733284931 28438987312288766599927397)
            ·
              refine ⟨5332310121054143737486387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28438987312288766599927397 5332310121054143737486387)
              ·
                refine ⟨7998465181581215606229581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5332310121054143737486387 7998465181581215606229581)
                ·
                  refine ⟨2999424443092955852336093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7998465181581215606229581 2999424443092955852336093)
                  ·
                    refine ⟨1124784166159858444626035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999424443092955852336093 1124784166159858444626035)
                    ·
                      rfl

theorem cell22_3285764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_3285764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285764 prefixEnd_3285764 := by exact prefixLift 3285764
  have htrace : WordTrace (prefixWord ++ tailWord_3285764) baseStart_3285764 baseEnd_3285764 := by
    simpa [prefixWord, tailWord_3285764, baseEnd_3285764] using wordTrace_append hprefix tailTrace_3285764
  have hstable : (prefixWord ++ tailWord_3285764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285764).length < 2 ^ (prefixWord ++ tailWord_3285764).sum := by decide
  have hdescent : baseEnd_3285764 < baseStart_3285764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285775 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 2, 5]
def baseStart_3285775 : Nat := 118140960795 + 3285775 * 2 ^ 59
def prefixEnd_3285775 : Nat := 4983230072969 + 3 ^ 40 * 3285775 * 2
def baseEnd_3285775 : Nat := 1124787931684658082601001

theorem tailTrace_3285775 : CollatzResearch.WordTrace tailWord_3285775 prefixEnd_3285775 1124787931684658082601001 := by
  unfold tailWord_3285775
  simp only [CollatzResearch.WordTrace]
  refine ⟨119842059671205815538426779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79894706447470543692284519 119842059671205815538426779)
  ·
    refine ⟨179763089506808723307640169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119842059671205815538426779 179763089506808723307640169)
    ·
      refine ⟨134822317130106542480730127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179763089506808723307640169 134822317130106542480730127)
      ·
        refine ⟨202233475695159813721095191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134822317130106542480730127 202233475695159813721095191)
        ·
          refine ⟨303350213542739720581642787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202233475695159813721095191 303350213542739720581642787)
          ·
            refine ⟨455025320314109580872464181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303350213542739720581642787 455025320314109580872464181)
            ·
              refine ⟨42658623779447773206793517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 455025320314109580872464181 42658623779447773206793517)
              ·
                refine ⟨15996983917292914952547569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42658623779447773206793517 15996983917292914952547569)
                ·
                  refine ⟨11997737937969686214410677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15996983917292914952547569 11997737937969686214410677)
                  ·
                    refine ⟨1124787931684658082601001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11997737937969686214410677 1124787931684658082601001)
                    ·
                      rfl

theorem cell22_3285775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_3285775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285775 prefixEnd_3285775 := by exact prefixLift 3285775
  have htrace : WordTrace (prefixWord ++ tailWord_3285775) baseStart_3285775 baseEnd_3285775 := by
    simpa [prefixWord, tailWord_3285775, baseEnd_3285775] using wordTrace_append hprefix tailTrace_3285775
  have hstable : (prefixWord ++ tailWord_3285775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285775).length < 2 ^ (prefixWord ++ tailWord_3285775).sum := by decide
  have hdescent : baseEnd_3285775 < baseStart_3285775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285841 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 1, 4]
def baseStart_3285841 : Nat := 118140960795 + 3285841 * 2 ^ 59
def prefixEnd_3285841 : Nat := 4983230072969 + 3 ^ 40 * 3285841 * 2
def baseEnd_3285841 : Nat := 1124810524833455910450799

theorem tailTrace_3285841 : CollatzResearch.WordTrace tailWord_3285841 prefixEnd_3285841 1124810524833455910450799 := by
  unfold tailWord_3285841
  simp only [CollatzResearch.WordTrace]
  refine ⟨119844466888966708810329377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79896311259311139206886251 119844466888966708810329377)
  ·
    refine ⟨89883350166725031607747033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119844466888966708810329377 89883350166725031607747033)
    ·
      refine ⟨67412512625043773705810275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89883350166725031607747033 67412512625043773705810275)
      ·
        refine ⟨101118768937565660558715413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67412512625043773705810275 101118768937565660558715413)
        ·
          refine ⟨4739942293948390338689785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101118768937565660558715413 4739942293948390338689785)
          ·
            refine ⟨3554956720461292754017339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4739942293948390338689785 3554956720461292754017339)
            ·
              refine ⟨5332435080691939131026009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554956720461292754017339 5332435080691939131026009)
              ·
                refine ⟨3999326310518954348269507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5332435080691939131026009 3999326310518954348269507)
                ·
                  refine ⟨5998989465778431522404261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999326310518954348269507 5998989465778431522404261)
                  ·
                    refine ⟨1124810524833455910450799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5998989465778431522404261 1124810524833455910450799)
                    ·
                      rfl

theorem cell22_3285841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_3285841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285841 prefixEnd_3285841 := by exact prefixLift 3285841
  have htrace : WordTrace (prefixWord ++ tailWord_3285841) baseStart_3285841 baseEnd_3285841 := by
    simpa [prefixWord, tailWord_3285841, baseEnd_3285841] using wordTrace_append hprefix tailTrace_3285841
  have hstable : (prefixWord ++ tailWord_3285841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285841).length < 2 ^ (prefixWord ++ tailWord_3285841).sum := by decide
  have hdescent : baseEnd_3285841 < baseStart_3285841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285858 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3285858 : Nat := 118140960795 + 3285858 * 2 ^ 59
def prefixEnd_3285858 : Nat := 4983230072969 + 3 ^ 40 * 3285858 * 2
def baseEnd_3285858 : Nat := 1124816344280873532775747

theorem tailTrace_3285858 : CollatzResearch.WordTrace tailWord_3285858 prefixEnd_3285858 1124816344280873532775747 := by
  unfold tailWord_3285858
  simp only [CollatzResearch.WordTrace]
  refine ⟨29961271732476280178424557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79896724619936747142465485 29961271732476280178424557)
  ·
    refine ⟨11235476899678605066909209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29961271732476280178424557 11235476899678605066909209)
    ·
      refine ⟨8426607674758953800181907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11235476899678605066909209 8426607674758953800181907)
      ·
        refine ⟨12639911512138430700272861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426607674758953800181907 12639911512138430700272861)
        ·
          refine ⟨4739966817051911512602323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12639911512138430700272861 4739966817051911512602323)
          ·
            refine ⟨7109950225577867268903485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739966817051911512602323 7109950225577867268903485)
            ·
              refine ⟨2666231334591700225838807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7109950225577867268903485 2666231334591700225838807)
              ·
                refine ⟨3999347001887550338758211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666231334591700225838807 3999347001887550338758211)
                ·
                  refine ⟨5999020502831325508137317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999347001887550338758211 5999020502831325508137317)
                  ·
                    refine ⟨1124816344280873532775747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5999020502831325508137317 1124816344280873532775747)
                    ·
                      rfl

theorem cell22_3285858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3285858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285858 prefixEnd_3285858 := by exact prefixLift 3285858
  have htrace : WordTrace (prefixWord ++ tailWord_3285858) baseStart_3285858 baseEnd_3285858 := by
    simpa [prefixWord, tailWord_3285858, baseEnd_3285858] using wordTrace_append hprefix tailTrace_3285858
  have hstable : (prefixWord ++ tailWord_3285858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285858).length < 2 ^ (prefixWord ++ tailWord_3285858).sum := by decide
  have hdescent : baseEnd_3285858 < baseStart_3285858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285959 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3285959 : Nat := 118140960795 + 3285959 * 2 ^ 59
def prefixEnd_3285959 : Nat := 4983230072969 + 3 ^ 40 * 3285959 * 2
def baseEnd_3285959 : Nat := 1124850918644942936000437

theorem tailTrace_3285959 : CollatzResearch.WordTrace tailWord_3285959 prefixEnd_3285959 1124850918644942936000437 := by
  unfold tailWord_3285959
  simp only [CollatzResearch.WordTrace]
  refine ⟨119848770702539214963124931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79899180468359476642083287 119848770702539214963124931)
  ·
    refine ⟨179773156053808822444687397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119848770702539214963124931 179773156053808822444687397)
    ·
      refine ⟨33707466760089154208378887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179773156053808822444687397 33707466760089154208378887)
      ·
        refine ⟨50561200140133731312568331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33707466760089154208378887 50561200140133731312568331)
        ·
          refine ⟨75841800210200596968852497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50561200140133731312568331 75841800210200596968852497)
          ·
            refine ⟨56881350157650447726639373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75841800210200596968852497 56881350157650447726639373)
            ·
              refine ⟨21330506309118917897489765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56881350157650447726639373 21330506309118917897489765)
              ·
                refine ⟨3999469932959797105779331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21330506309118917897489765 3999469932959797105779331)
                ·
                  refine ⟨5999204899439695658668997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999469932959797105779331 5999204899439695658668997)
                  ·
                    refine ⟨1124850918644942936000437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5999204899439695658668997 1124850918644942936000437)
                    ·
                      rfl

theorem cell22_3285959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3285959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285959 prefixEnd_3285959 := by exact prefixLift 3285959
  have htrace : WordTrace (prefixWord ++ tailWord_3285959) baseStart_3285959 baseEnd_3285959 := by
    simpa [prefixWord, tailWord_3285959, baseEnd_3285959] using wordTrace_append hprefix tailTrace_3285959
  have hstable : (prefixWord ++ tailWord_3285959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285959).length < 2 ^ (prefixWord ++ tailWord_3285959).sum := by decide
  have hdescent : baseEnd_3285959 < baseStart_3285959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3285991 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 6]
def baseStart_3285991 : Nat := 118140960795 + 3285991 * 2 ^ 59
def prefixEnd_3285991 : Nat := 4983230072969 + 3 ^ 40 * 3285991 * 2
def baseEnd_3285991 : Nat := 374953957632968506400113

theorem tailTrace_3285991 : CollatzResearch.WordTrace tailWord_3285991 prefixEnd_3285991 374953957632968506400113 := by
  unfold tailWord_3285991
  simp only [CollatzResearch.WordTrace]
  refine ⟨119849937838423284428289827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79899958558948856285526551 119849937838423284428289827)
  ·
    refine ⟨179774906757634926642434741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119849937838423284428289827 179774906757634926642434741)
    ·
      refine ⟨16853897508528274372728257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179774906757634926642434741 16853897508528274372728257)
      ·
        refine ⟨12640423131396205779546193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16853897508528274372728257 12640423131396205779546193)
        ·
          refine ⟨9480317348547154334659645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12640423131396205779546193 9480317348547154334659645)
          ·
            refine ⟨3555119005705182875497367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9480317348547154334659645 3555119005705182875497367)
            ·
              refine ⟨5332678508557774313246051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555119005705182875497367 5332678508557774313246051)
              ·
                refine ⟨7999017762836661469869077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5332678508557774313246051 7999017762836661469869077)
                ·
                  refine ⟨374953957632968506400113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7999017762836661469869077 374953957632968506400113)
                  ·
                    rfl

theorem cell22_3285991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 6].length) (baseStart_3285991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3285991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3285991 prefixEnd_3285991 := by exact prefixLift 3285991
  have htrace : WordTrace (prefixWord ++ tailWord_3285991) baseStart_3285991 baseEnd_3285991 := by
    simpa [prefixWord, tailWord_3285991, baseEnd_3285991] using wordTrace_append hprefix tailTrace_3285991
  have hstable : (prefixWord ++ tailWord_3285991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3285991).length < 2 ^ (prefixWord ++ tailWord_3285991).sum := by decide
  have hdescent : baseEnd_3285991 < baseStart_3285991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3285991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286032 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_3286032 : Nat := 118140960795 + 3286032 * 2 ^ 59
def prefixEnd_3286032 : Nat := 4983230072969 + 3 ^ 40 * 3286032 * 2
def baseEnd_3286032 : Nat := 1124875908036795078925213

theorem tailTrace_3286032 : CollatzResearch.WordTrace tailWord_3286032 prefixEnd_3286032 1124875908036795078925213 := by
  unfold tailWord_3286032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59925716615637374215266175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79900955487516498953688233 59925716615637374215266175)
  ·
    refine ⟨89888574923456061322899263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59925716615637374215266175 89888574923456061322899263)
    ·
      refine ⟨134832862385184091984348895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89888574923456061322899263 134832862385184091984348895)
      ·
        refine ⟨202249293577776137976523343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134832862385184091984348895 202249293577776137976523343)
        ·
          refine ⟨303373940366664206964785015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202249293577776137976523343 303373940366664206964785015)
          ·
            refine ⟨455060910549996310447177523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303373940366664206964785015 455060910549996310447177523)
            ·
              refine ⟨682591365824994465670766285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455060910549996310447177523 682591365824994465670766285)
              ·
                refine ⟨255971762184372924626537357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 682591365824994465670766285 255971762184372924626537357)
                ·
                  refine ⟨95989410819139846734951509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255971762184372924626537357 95989410819139846734951509)
                  ·
                    refine ⟨1124875908036795078925213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95989410819139846734951509 1124875908036795078925213)
                    ·
                      rfl

theorem cell22_3286032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_3286032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286032 prefixEnd_3286032 := by exact prefixLift 3286032
  have htrace : WordTrace (prefixWord ++ tailWord_3286032) baseStart_3286032 baseEnd_3286032 := by
    simpa [prefixWord, tailWord_3286032, baseEnd_3286032] using wordTrace_append hprefix tailTrace_3286032
  have hstable : (prefixWord ++ tailWord_3286032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286032).length < 2 ^ (prefixWord ++ tailWord_3286032).sum := by decide
  have hdescent : baseEnd_3286032 < baseStart_3286032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286049 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3286049 : Nat := 118140960795 + 3286049 * 2 ^ 59
def prefixEnd_3286049 : Nat := 4983230072969 + 3 ^ 40 * 3286049 * 2
def baseEnd_3286049 : Nat := 1124881727484212701250161

theorem tailTrace_3286049 : CollatzResearch.WordTrace tailWord_3286049 prefixEnd_3286049 1124881727484212701250161 := by
  unfold tailWord_3286049
  simp only [CollatzResearch.WordTrace]
  refine ⟨119852053272213160333901201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79901368848142106889267467 119852053272213160333901201)
  ·
    refine ⟨89889039954159870250425901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119852053272213160333901201 89889039954159870250425901)
    ·
      refine ⟨33708389982809951343909713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89889039954159870250425901 33708389982809951343909713)
      ·
        refine ⟨25281292487107463507932285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33708389982809951343909713 25281292487107463507932285)
        ·
          refine ⟨9480484682665298815474607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25281292487107463507932285 9480484682665298815474607)
          ·
            refine ⟨14220727023997948223211911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480484682665298815474607 14220727023997948223211911)
            ·
              refine ⟨21331090535996922334817867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14220727023997948223211911 21331090535996922334817867)
              ·
                refine ⟨31996635803995383502226801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21331090535996922334817867 31996635803995383502226801)
                ·
                  refine ⟨23997476852996537626670101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31996635803995383502226801 23997476852996537626670101)
                  ·
                    refine ⟨1124881727484212701250161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23997476852996537626670101 1124881727484212701250161)
                    ·
                      rfl

theorem cell22_3286049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3286049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286049 prefixEnd_3286049 := by exact prefixLift 3286049
  have htrace : WordTrace (prefixWord ++ tailWord_3286049) baseStart_3286049 baseEnd_3286049 := by
    simpa [prefixWord, tailWord_3286049, baseEnd_3286049] using wordTrace_append hprefix tailTrace_3286049
  have hstable : (prefixWord ++ tailWord_3286049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286049).length < 2 ^ (prefixWord ++ tailWord_3286049).sum := by decide
  have hdescent : baseEnd_3286049 < baseStart_3286049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286064 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 5]
def baseStart_3286064 : Nat := 118140960795 + 3286064 * 2 ^ 59
def prefixEnd_3286064 : Nat := 4983230072969 + 3 ^ 40 * 3286064 * 2
def baseEnd_3286064 : Nat := 374962287430252554041705

theorem tailTrace_3286064 : CollatzResearch.WordTrace tailWord_3286064 prefixEnd_3286064 374962287430252554041705 := by
  unfold tailWord_3286064
  simp only [CollatzResearch.WordTrace]
  refine ⟨59926300183579408947848623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79901733578105878597131497 59926300183579408947848623)
  ·
    refine ⟨89889450275369113421772935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59926300183579408947848623 89889450275369113421772935)
    ·
      refine ⟨134834175413053670132659403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89889450275369113421772935 134834175413053670132659403)
      ·
        refine ⟨202251263119580505198989105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134834175413053670132659403 202251263119580505198989105)
        ·
          refine ⟨151688447339685378899241829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202251263119580505198989105 151688447339685378899241829)
          ·
            refine ⟨28441583876191008543607843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151688447339685378899241829 28441583876191008543607843)
            ·
              refine ⟨42662375814286512815411765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28441583876191008543607843 42662375814286512815411765)
              ·
                refine ⟨3999597732589360576444853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42662375814286512815411765 3999597732589360576444853)
                ·
                  refine ⟨374962287430252554041705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3999597732589360576444853 374962287430252554041705)
                  ·
                    rfl

theorem cell22_3286064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_3286064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286064 prefixEnd_3286064 := by exact prefixLift 3286064
  have htrace : WordTrace (prefixWord ++ tailWord_3286064) baseStart_3286064 baseEnd_3286064 := by
    simpa [prefixWord, tailWord_3286064, baseEnd_3286064] using wordTrace_append hprefix tailTrace_3286064
  have hstable : (prefixWord ++ tailWord_3286064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286064).length < 2 ^ (prefixWord ++ tailWord_3286064).sum := by decide
  have hdescent : baseEnd_3286064 < baseStart_3286064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286068 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3286068 : Nat := 118140960795 + 3286068 * 2 ^ 59
def prefixEnd_3286068 : Nat := 4983230072969 + 3 ^ 40 * 3286068 * 2
def baseEnd_3286068 : Nat := 1124888231572502985025103

theorem tailTrace_3286068 : CollatzResearch.WordTrace tailWord_3286068 prefixEnd_3286068 1124888231572502985025103 := by
  unfold tailWord_3286068
  simp only [CollatzResearch.WordTrace]
  refine ⟨59926373129572163289421429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79901830839429551052561905 59926373129572163289421429)
  ·
    refine ⟨5618097480897390308383259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59926373129572163289421429 5618097480897390308383259)
    ·
      refine ⟨8427146221346085462574889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618097480897390308383259 8427146221346085462574889)
      ·
        refine ⟨6320359666009564096931167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8427146221346085462574889 6320359666009564096931167)
        ·
          refine ⟨9480539499014346145396751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6320359666009564096931167 9480539499014346145396751)
          ·
            refine ⟨14220809248521519218095127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480539499014346145396751 14220809248521519218095127)
            ·
              refine ⟨21331213872782278827142691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14220809248521519218095127 21331213872782278827142691)
              ·
                refine ⟨31996820809173418240714037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21331213872782278827142691 31996820809173418240714037)
                ·
                  refine ⟨2999701950860007960066941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31996820809173418240714037 2999701950860007960066941)
                  ·
                    refine ⟨1124888231572502985025103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999701950860007960066941 1124888231572502985025103)
                    ·
                      rfl

theorem cell22_3286068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3286068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286068 prefixEnd_3286068 := by exact prefixLift 3286068
  have htrace : WordTrace (prefixWord ++ tailWord_3286068) baseStart_3286068 baseEnd_3286068 := by
    simpa [prefixWord, tailWord_3286068, baseEnd_3286068] using wordTrace_append hprefix tailTrace_3286068
  have hstable : (prefixWord ++ tailWord_3286068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286068).length < 2 ^ (prefixWord ++ tailWord_3286068).sum := by decide
  have hdescent : baseEnd_3286068 < baseStart_3286068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286098 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_3286098 : Nat := 118140960795 + 3286098 * 2 ^ 59
def prefixEnd_3286098 : Nat := 4983230072969 + 3 ^ 40 * 3286098 * 2
def baseEnd_3286098 : Nat := 374966167061864302258337

theorem tailTrace_3286098 : CollatzResearch.WordTrace tailWord_3286098 prefixEnd_3286098 374966167061864302258337 := by
  unfold tailWord_3286098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29963460112258910425608737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79902560299357094468289965 29963460112258910425608737)
  ·
    refine ⟨22472595084194182819206553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29963460112258910425608737 22472595084194182819206553)
    ·
      refine ⟨16854446313145637114404915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22472595084194182819206553 16854446313145637114404915)
      ·
        refine ⟨25281669469718455671607373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16854446313145637114404915 25281669469718455671607373)
        ·
          refine ⟨9480626051144420876852765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25281669469718455671607373 9480626051144420876852765)
          ·
            refine ⟨3555234769179157828819787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9480626051144420876852765 3555234769179157828819787)
            ·
              refine ⟨5332852153768736743229681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555234769179157828819787 5332852153768736743229681)
              ·
                refine ⟨3999639115326552557422261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5332852153768736743229681 3999639115326552557422261)
                ·
                  refine ⟨374966167061864302258337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3999639115326552557422261 374966167061864302258337)
                  ·
                    rfl

theorem cell22_3286098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_3286098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286098 prefixEnd_3286098 := by exact prefixLift 3286098
  have htrace : WordTrace (prefixWord ++ tailWord_3286098) baseStart_3286098 baseEnd_3286098 := by
    simpa [prefixWord, tailWord_3286098, baseEnd_3286098] using wordTrace_append hprefix tailTrace_3286098
  have hstable : (prefixWord ++ tailWord_3286098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286098).length < 2 ^ (prefixWord ++ tailWord_3286098).sum := by decide
  have hdescent : baseEnd_3286098 < baseStart_3286098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286102 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3286102 : Nat := 118140960795 + 3286102 * 2 ^ 59
def prefixEnd_3286102 : Nat := 4983230072969 + 3 ^ 40 * 3286102 * 2
def baseEnd_3286102 : Nat := 1124899870467338229674999

theorem tailTrace_3286102 : CollatzResearch.WordTrace tailWord_3286102 prefixEnd_3286102 1124899870467338229674999 := by
  unfold tailWord_3286102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490874146313821899098785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79902657560680766923720373 7490874146313821899098785)
  ·
    refine ⟨5618155609735366424324089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7490874146313821899098785 5618155609735366424324089)
    ·
      refine ⟨4213616707301524818243067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5618155609735366424324089 4213616707301524818243067)
      ·
        refine ⟨6320425060952287227364601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4213616707301524818243067 6320425060952287227364601)
        ·
          refine ⟨4740318795714215420523451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6320425060952287227364601 4740318795714215420523451)
          ·
            refine ⟨7110478193571323130785177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740318795714215420523451 7110478193571323130785177)
            ·
              refine ⟨5332858645178492348088883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7110478193571323130785177 5332858645178492348088883)
              ·
                refine ⟨7999287967767738522133325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5332858645178492348088883 7999287967767738522133325)
                ·
                  refine ⟨2999732987912901945799997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7999287967767738522133325 2999732987912901945799997)
                  ·
                    refine ⟨1124899870467338229674999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999732987912901945799997 1124899870467338229674999)
                    ·
                      rfl

theorem cell22_3286102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3286102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286102 prefixEnd_3286102 := by exact prefixLift 3286102
  have htrace : WordTrace (prefixWord ++ tailWord_3286102) baseStart_3286102 baseEnd_3286102 := by
    simpa [prefixWord, tailWord_3286102, baseEnd_3286102] using wordTrace_append hprefix tailTrace_3286102
  have hstable : (prefixWord ++ tailWord_3286102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286102).length < 2 ^ (prefixWord ++ tailWord_3286102).sum := by decide
  have hdescent : baseEnd_3286102 < baseStart_3286102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286126 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_3286126 : Nat := 118140960795 + 3286126 * 2 ^ 59
def prefixEnd_3286126 : Nat := 4983230072969 + 3 ^ 40 * 3286126 * 2
def baseEnd_3286126 : Nat := 374969362052603389024975

theorem tailTrace_3286126 : CollatzResearch.WordTrace tailWord_3286126 prefixEnd_3286126 374969362052603389024975 := by
  unfold tailWord_3286126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14981857711616775310556779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79903241128622801656302821 14981857711616775310556779)
  ·
    refine ⟨22472786567425162965835169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14981857711616775310556779 22472786567425162965835169)
    ·
      refine ⟨16854589925568872224376377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22472786567425162965835169 16854589925568872224376377)
      ·
        refine ⟨12640942444176654168282283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16854589925568872224376377 12640942444176654168282283)
        ·
          refine ⟨18961413666264981252423425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12640942444176654168282283 18961413666264981252423425)
          ·
            refine ⟨14221060249698735939317569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18961413666264981252423425 14221060249698735939317569)
            ·
              refine ⟨10665795187274051954488177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14221060249698735939317569 10665795187274051954488177)
              ·
                refine ⟨7999346390455538965866133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10665795187274051954488177 7999346390455538965866133)
                ·
                  refine ⟨374969362052603389024975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7999346390455538965866133 374969362052603389024975)
                  ·
                    rfl

theorem cell22_3286126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_3286126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286126 prefixEnd_3286126 := by exact prefixLift 3286126
  have htrace : WordTrace (prefixWord ++ tailWord_3286126) baseStart_3286126 baseEnd_3286126 := by
    simpa [prefixWord, tailWord_3286126, baseEnd_3286126] using wordTrace_append hprefix tailTrace_3286126
  have hstable : (prefixWord ++ tailWord_3286126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286126).length < 2 ^ (prefixWord ++ tailWord_3286126).sum := by decide
  have hdescent : baseEnd_3286126 < baseStart_3286126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286139 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 6, 4]
def baseStart_3286139 : Nat := 118140960795 + 3286139 * 2 ^ 59
def prefixEnd_3286139 : Nat := 4983230072969 + 3 ^ 40 * 3286139 * 2
def baseEnd_3286139 : Nat := 1124912536323482466499885

theorem tailTrace_3286139 : CollatzResearch.WordTrace tailWord_3286139 prefixEnd_3286139 1124912536323482466499885 := by
  unfold tailWord_3286139
  simp only [CollatzResearch.WordTrace]
  refine ⟨119855335841887105704677471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79903557227924737136451647 119855335841887105704677471)
  ·
    refine ⟨179783003762830658557016207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119855335841887105704677471 179783003762830658557016207)
    ·
      refine ⟨269674505644245987835524311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179783003762830658557016207 269674505644245987835524311)
      ·
        refine ⟨404511758466368981753286467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269674505644245987835524311 404511758466368981753286467)
        ·
          refine ⟨606767637699553472629929701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404511758466368981753286467 606767637699553472629929701)
          ·
            refine ⟨113768932068666276118111819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 606767637699553472629929701 113768932068666276118111819)
            ·
              refine ⟨170653398102999414177167729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113768932068666276118111819 170653398102999414177167729)
              ·
                refine ⟨127990048577249560632875797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170653398102999414177167729 127990048577249560632875797)
                ·
                  refine ⟨5999533527058573154666053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127990048577249560632875797 5999533527058573154666053)
                  ·
                    refine ⟨1124912536323482466499885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5999533527058573154666053 1124912536323482466499885)
                    ·
                      rfl

theorem cell22_3286139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_3286139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286139 prefixEnd_3286139 := by exact prefixLift 3286139
  have htrace : WordTrace (prefixWord ++ tailWord_3286139) baseStart_3286139 baseEnd_3286139 := by
    simpa [prefixWord, tailWord_3286139, baseEnd_3286139] using wordTrace_append hprefix tailTrace_3286139
  have hstable : (prefixWord ++ tailWord_3286139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286139).length < 2 ^ (prefixWord ++ tailWord_3286139).sum := by decide
  have hdescent : baseEnd_3286139 < baseStart_3286139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286141 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_3286141 : Nat := 118140960795 + 3286141 * 2 ^ 59
def prefixEnd_3286141 : Nat := 4983230072969 + 3 ^ 40 * 3286141 * 2
def baseEnd_3286141 : Nat := 1124913220964355127949879

theorem tailTrace_3286141 : CollatzResearch.WordTrace tailWord_3286141 prefixEnd_3286141 1124913220964355127949879 := by
  unfold tailWord_3286141
  simp only [CollatzResearch.WordTrace]
  refine ⟨119855408787879860046250277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79903605858586573364166851 119855408787879860046250277)
  ·
    refine ⟨22472889147727473758671927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119855408787879860046250277 22472889147727473758671927)
    ·
      refine ⟨33709333721591210638007891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22472889147727473758671927 33709333721591210638007891)
      ·
        refine ⟨50564000582386815957011837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33709333721591210638007891 50564000582386815957011837)
        ·
          refine ⟨18961500218395055983879439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50564000582386815957011837 18961500218395055983879439)
          ·
            refine ⟨28442250327592583975819159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18961500218395055983879439 28442250327592583975819159)
            ·
              refine ⟨42663375491388875963728739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28442250327592583975819159 42663375491388875963728739)
              ·
                refine ⟨63995063237083313945593109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42663375491388875963728739 63995063237083313945593109)
                ·
                  refine ⟨2999768589238280341199677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63995063237083313945593109 2999768589238280341199677)
                  ·
                    refine ⟨1124913220964355127949879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999768589238280341199677 1124913220964355127949879)
                    ·
                      rfl

theorem cell22_3286141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_3286141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286141 prefixEnd_3286141 := by exact prefixLift 3286141
  have htrace : WordTrace (prefixWord ++ tailWord_3286141) baseStart_3286141 baseEnd_3286141 := by
    simpa [prefixWord, tailWord_3286141, baseEnd_3286141] using wordTrace_append hprefix tailTrace_3286141
  have hstable : (prefixWord ++ tailWord_3286141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286141).length < 2 ^ (prefixWord ++ tailWord_3286141).sum := by decide
  have hdescent : baseEnd_3286141 < baseStart_3286141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286158 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_3286158 : Nat := 118140960795 + 3286158 * 2 ^ 59
def prefixEnd_3286158 : Nat := 4983230072969 + 3 ^ 40 * 3286158 * 2
def baseEnd_3286158 : Nat := 1124919040411772750274827

theorem tailTrace_3286158 : CollatzResearch.WordTrace tailWord_3286158 prefixEnd_3286158 1124919040411772750274827 := by
  unfold tailWord_3286158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14982003603602283993702391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79904019219212181299746085 14982003603602283993702391)
  ·
    refine ⟨22473005405403425990553587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14982003603602283993702391 22473005405403425990553587)
    ·
      refine ⟨33709508108105138985830381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22473005405403425990553587 33709508108105138985830381)
      ·
        refine ⟨12641065540539427119686393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33709508108105138985830381 12641065540539427119686393)
        ·
          refine ⟨9480799155404570339764795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12641065540539427119686393 9480799155404570339764795)
          ·
            refine ⟨14221198733106855509647193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480799155404570339764795 14221198733106855509647193)
            ·
              refine ⟨10665899049830141632235395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14221198733106855509647193 10665899049830141632235395)
              ·
                refine ⟨15998848574745212448353093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10665899049830141632235395 15998848574745212448353093)
                ·
                  refine ⟨2999784107764727334066205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15998848574745212448353093 2999784107764727334066205)
                  ·
                    refine ⟨1124919040411772750274827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999784107764727334066205 1124919040411772750274827)
                    ·
                      rfl

theorem cell22_3286158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_3286158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286158 prefixEnd_3286158 := by exact prefixLift 3286158
  have htrace : WordTrace (prefixWord ++ tailWord_3286158) baseStart_3286158 baseEnd_3286158 := by
    simpa [prefixWord, tailWord_3286158, baseEnd_3286158] using wordTrace_append hprefix tailTrace_3286158
  have hstable : (prefixWord ++ tailWord_3286158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286158).length < 2 ^ (prefixWord ++ tailWord_3286158).sum := by decide
  have hdescent : baseEnd_3286158 < baseStart_3286158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286175 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 2, 3]
def baseStart_3286175 : Nat := 118140960795 + 3286175 * 2 ^ 59
def prefixEnd_3286175 : Nat := 4983230072969 + 3 ^ 40 * 3286175 * 2
def baseEnd_3286175 : Nat := 1124924859859190372599775

theorem tailTrace_3286175 : CollatzResearch.WordTrace tailWord_3286175 prefixEnd_3286175 1124924859859190372599775 := by
  unfold tailWord_3286175
  simp only [CollatzResearch.WordTrace]
  refine ⟨119856648869756683852987979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79904432579837789235325319 119856648869756683852987979)
  ·
    refine ⟨179784973304635025779481969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119856648869756683852987979 179784973304635025779481969)
    ·
      refine ⟨134838729978476269334611477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179784973304635025779481969 134838729978476269334611477)
      ·
        refine ⟨6320565467741075125059913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134838729978476269334611477 6320565467741075125059913)
        ·
          refine ⟨4740424100805806343794935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6320565467741075125059913 4740424100805806343794935)
          ·
            refine ⟨7110636151208709515692403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740424100805806343794935 7110636151208709515692403)
            ·
              refine ⟨10665954226813064273538605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110636151208709515692403 10665954226813064273538605)
              ·
                refine ⟨3999732835054899102576977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10665954226813064273538605 3999732835054899102576977)
                ·
                  refine ⟨2999799626291174326932733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999732835054899102576977 2999799626291174326932733)
                  ·
                    refine ⟨1124924859859190372599775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999799626291174326932733 1124924859859190372599775)
                    ·
                      rfl

theorem cell22_3286175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_3286175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286175 prefixEnd_3286175 := by exact prefixLift 3286175
  have htrace : WordTrace (prefixWord ++ tailWord_3286175) baseStart_3286175 baseEnd_3286175 := by
    simpa [prefixWord, tailWord_3286175, baseEnd_3286175] using wordTrace_append hprefix tailTrace_3286175
  have hstable : (prefixWord ++ tailWord_3286175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286175).length < 2 ^ (prefixWord ++ tailWord_3286175).sum := by decide
  have hdescent : baseEnd_3286175 < baseStart_3286175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286216 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 5]
def baseStart_3286216 : Nat := 118140960795 + 3286216 * 2 ^ 59
def prefixEnd_3286216 : Nat := 4983230072969 + 3 ^ 40 * 3286216 * 2
def baseEnd_3286216 : Nat := 374979631665693310774883

theorem tailTrace_3286216 : CollatzResearch.WordTrace tailWord_3286216 prefixEnd_3286216 374979631665693310774883 := by
  unfold tailWord_3286216
  simp only [CollatzResearch.WordTrace]
  refine ⟨59929072131304073927615251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79905429508405431903487001 59929072131304073927615251)
  ·
    refine ⟨89893608196956110891422877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59929072131304073927615251 89893608196956110891422877)
    ·
      refine ⟨33710103073858541584283579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89893608196956110891422877 33710103073858541584283579)
      ·
        refine ⟨50565154610787812376425369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33710103073858541584283579 50565154610787812376425369)
        ·
          refine ⟨37923865958090859282319027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50565154610787812376425369 37923865958090859282319027)
          ·
            refine ⟨56885798937136288923478541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37923865958090859282319027 56885798937136288923478541)
            ·
              refine ⟨21332174601426108346304453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56885798937136288923478541 21332174601426108346304453)
              ·
                refine ⟨3999782737767395314932085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21332174601426108346304453 3999782737767395314932085)
                ·
                  refine ⟨374979631665693310774883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3999782737767395314932085 374979631665693310774883)
                  ·
                    rfl

theorem cell22_3286216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_3286216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286216 prefixEnd_3286216 := by exact prefixLift 3286216
  have htrace : WordTrace (prefixWord ++ tailWord_3286216) baseStart_3286216 baseEnd_3286216 := by
    simpa [prefixWord, tailWord_3286216, baseEnd_3286216] using wordTrace_append hprefix tailTrace_3286216
  have hstable : (prefixWord ++ tailWord_3286216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286216).length < 2 ^ (prefixWord ++ tailWord_3286216).sum := by decide
  have hdescent : baseEnd_3286216 < baseStart_3286216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286308 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_3286308 : Nat := 118140960795 + 3286308 * 2 ^ 59
def prefixEnd_3286308 : Nat := 4983230072969 + 3 ^ 40 * 3286308 * 2
def baseEnd_3286308 : Nat := 1124970388477222359024367

theorem tailTrace_3286308 : CollatzResearch.WordTrace tailWord_3286308 prefixEnd_3286308 1124970388477222359024367 := by
  unfold tailWord_3286308
  simp only [CollatzResearch.WordTrace]
  refine ⟨59930749889137423783789789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79907666518849898378386385 59930749889137423783789789)
  ·
    refine ⟨22474031208426533918921171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59930749889137423783789789 22474031208426533918921171)
    ·
      refine ⟨33711046812639800878381757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22474031208426533918921171 33711046812639800878381757)
      ·
        refine ⟨12641642554739925329393159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33711046812639800878381757 12641642554739925329393159)
        ·
          refine ⟨18962463832109887994089739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12641642554739925329393159 18962463832109887994089739)
          ·
            refine ⟨28443695748164831991134609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18962463832109887994089739 28443695748164831991134609)
            ·
              refine ⟨21332771811123623993350957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28443695748164831991134609 21332771811123623993350957)
              ·
                refine ⟨7999789429171358997506609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21332771811123623993350957 7999789429171358997506609)
                ·
                  refine ⟨5999842071878519248129957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7999789429171358997506609 5999842071878519248129957)
                  ·
                    refine ⟨1124970388477222359024367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5999842071878519248129957 1124970388477222359024367)
                    ·
                      rfl

theorem cell22_3286308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_3286308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286308 prefixEnd_3286308 := by exact prefixLift 3286308
  have htrace : WordTrace (prefixWord ++ tailWord_3286308) baseStart_3286308 baseEnd_3286308 := by
    simpa [prefixWord, tailWord_3286308, baseEnd_3286308] using wordTrace_append hprefix tailTrace_3286308
  have hstable : (prefixWord ++ tailWord_3286308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286308).length < 2 ^ (prefixWord ++ tailWord_3286308).sum := by decide
  have hdescent : baseEnd_3286308 < baseStart_3286308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286312 : List Nat := [2, 1, 5, 1, 2, 3, 1, 3, 4]
def baseStart_3286312 : Nat := 118140960795 + 3286312 * 2 ^ 59
def prefixEnd_3286312 : Nat := 4983230072969 + 3 ^ 40 * 3286312 * 2
def baseEnd_3286312 : Nat := 374990585919655893974785

theorem tailTrace_3286312 : CollatzResearch.WordTrace tailWord_3286312 prefixEnd_3286312 374990585919655893974785 := by
  unfold tailWord_3286312
  simp only [CollatzResearch.WordTrace]
  refine ⟨59930822835130178125362595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79907763780173570833816793 59930822835130178125362595)
  ·
    refine ⟨89896234252695267188043893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59930822835130178125362595 89896234252695267188043893)
    ·
      refine ⟨8427771961190181298879115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89896234252695267188043893 8427771961190181298879115)
      ·
        refine ⟨12641657941785271948318673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8427771961190181298879115 12641657941785271948318673)
        ·
          refine ⟨9481243456338953961239005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12641657941785271948318673 9481243456338953961239005)
          ·
            refine ⟨3555466296127107735464627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9481243456338953961239005 3555466296127107735464627)
            ·
              refine ⟨5333199444190661603196941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555466296127107735464627 5333199444190661603196941)
              ·
                refine ⟨1999949791571498101198853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5333199444190661603196941 1999949791571498101198853)
                ·
                  refine ⟨374990585919655893974785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999949791571498101198853 374990585919655893974785)
                  ·
                    rfl

theorem cell22_3286312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_3286312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286312 prefixEnd_3286312 := by exact prefixLift 3286312
  have htrace : WordTrace (prefixWord ++ tailWord_3286312) baseStart_3286312 baseEnd_3286312 := by
    simpa [prefixWord, tailWord_3286312, baseEnd_3286312] using wordTrace_append hprefix tailTrace_3286312
  have hstable : (prefixWord ++ tailWord_3286312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286312).length < 2 ^ (prefixWord ++ tailWord_3286312).sum := by decide
  have hdescent : baseEnd_3286312 < baseStart_3286312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286336 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_3286336 : Nat := 118140960795 + 3286336 * 2 ^ 59
def prefixEnd_3286336 : Nat := 4983230072969 + 3 ^ 40 * 3286336 * 2
def baseEnd_3286336 : Nat := 1124979973449439619324281

theorem tailTrace_3286336 : CollatzResearch.WordTrace tailWord_3286336 prefixEnd_3286336 1124979973449439619324281 := by
  unfold tailWord_3286336
  simp only [CollatzResearch.WordTrace]
  refine ⟨59931260511086704174799431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79908347348115605566399241 59931260511086704174799431)
  ·
    refine ⟨89896890766630056262199147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59931260511086704174799431 89896890766630056262199147)
    ·
      refine ⟨134845336149945084393298721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89896890766630056262199147 134845336149945084393298721)
      ·
        refine ⟨101134002112458813294974041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134845336149945084393298721 101134002112458813294974041)
        ·
          refine ⟨75850501584344109971230531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101134002112458813294974041 75850501584344109971230531)
          ·
            refine ⟨113775752376516164956845797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75850501584344109971230531 113775752376516164956845797)
            ·
              refine ⟨21332953570596780929408587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113775752376516164956845797 21332953570596780929408587)
              ·
                refine ⟨31999430355895171394112881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21332953570596780929408587 31999430355895171394112881)
                ·
                  refine ⟨23999572766921378545584661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31999430355895171394112881 23999572766921378545584661)
                  ·
                    refine ⟨1124979973449439619324281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23999572766921378545584661 1124979973449439619324281)
                    ·
                      rfl

theorem cell22_3286336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_3286336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286336 prefixEnd_3286336 := by exact prefixLift 3286336
  have htrace : WordTrace (prefixWord ++ tailWord_3286336) baseStart_3286336 baseEnd_3286336 := by
    simpa [prefixWord, tailWord_3286336, baseEnd_3286336] using wordTrace_append hprefix tailTrace_3286336
  have hstable : (prefixWord ++ tailWord_3286336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286336).length < 2 ^ (prefixWord ++ tailWord_3286336).sum := by decide
  have hdescent : baseEnd_3286336 < baseStart_3286336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286340 : List Nat := [2, 3, 4, 1, 1, 2, 2, 7]
def baseStart_3286340 : Nat := 118140960795 + 3286340 * 2 ^ 59
def prefixEnd_3286340 : Nat := 4983230072969 + 3 ^ 40 * 3286340 * 2
def baseEnd_3286340 : Nat := 124997926970131660247141

theorem tailTrace_3286340 : CollatzResearch.WordTrace tailWord_3286340 prefixEnd_3286340 124997926970131660247141 := by
  unfold tailWord_3286340
  simp only [CollatzResearch.WordTrace]
  refine ⟨59931333457079458516372237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79908444609439278021829649 59931333457079458516372237)
  ·
    refine ⟨22474250046404796943639589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59931333457079458516372237 22474250046404796943639589)
    ·
      refine ⟨4213921883700899426932423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22474250046404796943639589 4213921883700899426932423)
      ·
        refine ⟨6320882825551349140398635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4213921883700899426932423 6320882825551349140398635)
        ·
          refine ⟨9481324238327023710597953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6320882825551349140398635 9481324238327023710597953)
          ·
            refine ⟨7110993178745267782948465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9481324238327023710597953 7110993178745267782948465)
            ·
              refine ⟨5333244884058950837211349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7110993178745267782948465 5333244884058950837211349)
              ·
                refine ⟨124997926970131660247141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5333244884058950837211349 124997926970131660247141)
                ·
                  rfl

theorem cell22_3286340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 7].length) (baseStart_3286340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286340 prefixEnd_3286340 := by exact prefixLift 3286340
  have htrace : WordTrace (prefixWord ++ tailWord_3286340) baseStart_3286340 baseEnd_3286340 := by
    simpa [prefixWord, tailWord_3286340, baseEnd_3286340] using wordTrace_append hprefix tailTrace_3286340
  have hstable : (prefixWord ++ tailWord_3286340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286340).length < 2 ^ (prefixWord ++ tailWord_3286340).sum := by decide
  have hdescent : baseEnd_3286340 < baseStart_3286340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286389 : List Nat := [1, 3, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3286389 : Nat := 118140960795 + 3286389 * 2 ^ 59
def prefixEnd_3286389 : Nat := 4983230072969 + 3 ^ 40 * 3286389 * 2
def baseEnd_3286389 : Nat := 1124998116432565147749119

theorem tailTrace_3286389 : CollatzResearch.WordTrace tailWord_3286389 prefixEnd_3286389 1124998116432565147749119 := by
  unfold tailWord_3286389
  simp only [CollatzResearch.WordTrace]
  refine ⟨119864454090981398401278221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79909636060654265600852147 119864454090981398401278221)
  ·
    refine ⟨44949170284118024400479333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119864454090981398401278221 44949170284118024400479333)
    ·
      refine ⟨8427969428272129575089875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44949170284118024400479333 8427969428272129575089875)
      ·
        refine ⟨12641954142408194362634813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8427969428272129575089875 12641954142408194362634813)
        ·
          refine ⟨4740732803403072885988055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12641954142408194362634813 4740732803403072885988055)
          ·
            refine ⟨7111099205104609328982083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740732803403072885988055 7111099205104609328982083)
            ·
              refine ⟨10666648807656913993473125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111099205104609328982083 10666648807656913993473125)
              ·
                refine ⟨1999996651435671373776211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10666648807656913993473125 1999996651435671373776211)
                ·
                  refine ⟨2999994977153507060664317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999996651435671373776211 2999994977153507060664317)
                  ·
                    refine ⟨1124998116432565147749119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999994977153507060664317 1124998116432565147749119)
                    ·
                      rfl

theorem cell22_3286389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3286389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286389 prefixEnd_3286389 := by exact prefixLift 3286389
  have htrace : WordTrace (prefixWord ++ tailWord_3286389) baseStart_3286389 baseEnd_3286389 := by
    simpa [prefixWord, tailWord_3286389, baseEnd_3286389] using wordTrace_append hprefix tailTrace_3286389
  have hstable : (prefixWord ++ tailWord_3286389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286389).length < 2 ^ (prefixWord ++ tailWord_3286389).sum := by decide
  have hdescent : baseEnd_3286389 < baseStart_3286389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286402 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3286402 : Nat := 118140960795 + 3286402 * 2 ^ 59
def prefixEnd_3286402 : Nat := 4983230072969 + 3 ^ 40 * 3286402 * 2
def baseEnd_3286402 : Nat := 375000855532745815724693

theorem tailTrace_3286402 : CollatzResearch.WordTrace tailWord_3286402 prefixEnd_3286402 375000855532745815724693 := by
  unfold tailWord_3286402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29966232059983575405375365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79909952159956201081000973 29966232059983575405375365)
  ·
    refine ⟨5618668511246920388507881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29966232059983575405375365 5618668511246920388507881)
    ·
      refine ⟨4214001383435190291380911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5618668511246920388507881 4214001383435190291380911)
      ·
        refine ⟨6321002075152785437071367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214001383435190291380911 6321002075152785437071367)
        ·
          refine ⟨9481503112729178155607051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6321002075152785437071367 9481503112729178155607051)
          ·
            refine ⟨14222254669093767233410577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9481503112729178155607051 14222254669093767233410577)
            ·
              refine ⟨10666691001820325425057933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222254669093767233410577 10666691001820325425057933)
              ·
                refine ⟨4000009125682622034396725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10666691001820325425057933 4000009125682622034396725)
                ·
                  refine ⟨375000855532745815724693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000009125682622034396725 375000855532745815724693)
                  ·
                    rfl

theorem cell22_3286402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3286402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286402 prefixEnd_3286402 := by exact prefixLift 3286402
  have htrace : WordTrace (prefixWord ++ tailWord_3286402) baseStart_3286402 baseEnd_3286402 := by
    simpa [prefixWord, tailWord_3286402, baseEnd_3286402] using wordTrace_append hprefix tailTrace_3286402
  have hstable : (prefixWord ++ tailWord_3286402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286402).length < 2 ^ (prefixWord ++ tailWord_3286402).sum := by decide
  have hdescent : baseEnd_3286402 < baseStart_3286402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286520 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 5]
def baseStart_3286520 : Nat := 118140960795 + 3286520 * 2 ^ 59
def prefixEnd_3286520 : Nat := 4983230072969 + 3 ^ 40 * 3286520 * 2
def baseEnd_3286520 : Nat := 375014320136574824241239

theorem tailTrace_3286520 : CollatzResearch.WordTrace tailWord_3286520 prefixEnd_3286520 375014320136574824241239 := by
  unfold tailWord_3286520
  simp only [CollatzResearch.WordTrace]
  refine ⟨59934616026753403887148507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79912821369004538516198009 59934616026753403887148507)
  ·
    refine ⟨89901924040130105830722761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59934616026753403887148507 89901924040130105830722761)
    ·
      refine ⟨67426443030097579373042071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89901924040130105830722761 67426443030097579373042071)
      ·
        refine ⟨101139664545146369059563107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67426443030097579373042071 101139664545146369059563107)
        ·
          refine ⟨151709496817719553589344661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101139664545146369059563107 151709496817719553589344661)
          ·
            refine ⟨7111382663330604074500531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151709496817719553589344661 7111382663330604074500531)
            ·
              refine ⟨10667073994995906111750797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111382663330604074500531 10667073994995906111750797)
              ·
                refine ⟨4000152748123464791906549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10667073994995906111750797 4000152748123464791906549)
                ·
                  refine ⟨375014320136574824241239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000152748123464791906549 375014320136574824241239)
                  ·
                    rfl

theorem cell22_3286520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_3286520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286520 prefixEnd_3286520 := by exact prefixLift 3286520
  have htrace : WordTrace (prefixWord ++ tailWord_3286520) baseStart_3286520 baseEnd_3286520 := by
    simpa [prefixWord, tailWord_3286520, baseEnd_3286520] using wordTrace_append hprefix tailTrace_3286520
  have hstable : (prefixWord ++ tailWord_3286520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286520).length < 2 ^ (prefixWord ++ tailWord_3286520).sum := by decide
  have hdescent : baseEnd_3286520 < baseStart_3286520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286599 : List Nat := [1, 1, 4, 1, 5, 1, 2, 3, 4]
def baseStart_3286599 : Nat := 118140960795 + 3286599 * 2 ^ 59
def prefixEnd_3286599 : Nat := 4983230072969 + 3 ^ 40 * 3286599 * 2
def baseEnd_3286599 : Nat := 375023334574731533332825

theorem tailTrace_3286599 : CollatzResearch.WordTrace tailWord_3286599 prefixEnd_3286599 375023334574731533332825 := by
  unfold tailWord_3286599
  simp only [CollatzResearch.WordTrace]
  refine ⟨119872113420220604266422851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79914742280147069510948567 119872113420220604266422851)
  ·
    refine ⟨179808170130330906399634277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119872113420220604266422851 179808170130330906399634277)
    ·
      refine ⟨33714031899437044949931427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179808170130330906399634277 33714031899437044949931427)
      ·
        refine ⟨50571047849155567424897141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33714031899437044949931427 50571047849155567424897141)
        ·
          refine ⟨4741035735858334446084107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50571047849155567424897141 4741035735858334446084107)
          ·
            refine ⟨7111553603787501669126161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741035735858334446084107 7111553603787501669126161)
            ·
              refine ⟨5333665202840626251844621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7111553603787501669126161 5333665202840626251844621)
              ·
                refine ⟨2000124451065234844441733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5333665202840626251844621 2000124451065234844441733)
                ·
                  refine ⟨375023334574731533332825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000124451065234844441733 375023334574731533332825)
                  ·
                    rfl

theorem cell22_3286599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 4].length) (baseStart_3286599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286599 prefixEnd_3286599 := by exact prefixLift 3286599
  have htrace : WordTrace (prefixWord ++ tailWord_3286599) baseStart_3286599 baseEnd_3286599 := by
    simpa [prefixWord, tailWord_3286599, baseEnd_3286599] using wordTrace_append hprefix tailTrace_3286599
  have hstable : (prefixWord ++ tailWord_3286599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286599).length < 2 ^ (prefixWord ++ tailWord_3286599).sum := by decide
  have hdescent : baseEnd_3286599 < baseStart_3286599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286610 : List Nat := [3, 2, 2, 1, 2, 3, 9]
def baseStart_3286610 : Nat := 118140960795 + 3286610 * 2 ^ 59
def prefixEnd_3286610 : Nat := 4983230072969 + 3 ^ 40 * 3286610 * 2
def baseEnd_3286610 : Nat := 41669398861073860665683

theorem tailTrace_3286610 : CollatzResearch.WordTrace tailWord_3286610 prefixEnd_3286610 41669398861073860665683 := by
  unfold tailWord_3286610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29968128655795188286268321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79915009748787168763382189 29968128655795188286268321)
  ·
    refine ⟨22476096491846391214701241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29968128655795188286268321 22476096491846391214701241)
    ·
      refine ⟨16857072368884793411025931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22476096491846391214701241 16857072368884793411025931)
      ·
        refine ⟨25285608553327190116538897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16857072368884793411025931 25285608553327190116538897)
        ·
          refine ⟨18964206414995392587404173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25285608553327190116538897 18964206414995392587404173)
          ·
            refine ⟨7111577405623272220276565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18964206414995392587404173 7111577405623272220276565)
            ·
              refine ⟨41669398861073860665683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7111577405623272220276565 41669398861073860665683)
              ·
                rfl

theorem cell22_3286610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 9].length) (baseStart_3286610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286610 prefixEnd_3286610 := by exact prefixLift 3286610
  have htrace : WordTrace (prefixWord ++ tailWord_3286610) baseStart_3286610 baseEnd_3286610 := by
    simpa [prefixWord, tailWord_3286610, baseEnd_3286610] using wordTrace_append hprefix tailTrace_3286610
  have hstable : (prefixWord ++ tailWord_3286610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286610).length < 2 ^ (prefixWord ++ tailWord_3286610).sum := by decide
  have hdescent : baseEnd_3286610 < baseStart_3286610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286685 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3286685 : Nat := 118140960795 + 3286685 * 2 ^ 59
def prefixEnd_3286685 : Nat := 4983230072969 + 3 ^ 40 * 3286685 * 2
def baseEnd_3286685 : Nat := 1125099443281719042348211

theorem tailTrace_3286685 : CollatzResearch.WordTrace tailWord_3286685 prefixEnd_3286685 1125099443281719042348211 := by
  unfold tailWord_3286685
  simp only [CollatzResearch.WordTrace]
  refine ⟨119875250097909040954053509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79916833398606027302702339 119875250097909040954053509)
  ·
    refine ⟨22476609393357945178885033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119875250097909040954053509 22476609393357945178885033)
    ·
      refine ⟨16857457045018458884163775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22476609393357945178885033 16857457045018458884163775)
      ·
        refine ⟨25286185567527688326245663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16857457045018458884163775 25286185567527688326245663)
        ·
          refine ⟨37929278351291532489368495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25286185567527688326245663 37929278351291532489368495)
          ·
            refine ⟨56893917526937298734052743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37929278351291532489368495 56893917526937298734052743)
            ·
              refine ⟨85340876290405948101079115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56893917526937298734052743 85340876290405948101079115)
              ·
                refine ⟨128011314435608922151618673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85340876290405948101079115 128011314435608922151618673)
                ·
                  refine ⟨96008485826706691613714005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128011314435608922151618673 96008485826706691613714005)
                  ·
                    refine ⟨1125099443281719042348211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96008485826706691613714005 1125099443281719042348211)
                    ·
                      rfl

theorem cell22_3286685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3286685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286685 prefixEnd_3286685 := by exact prefixLift 3286685
  have htrace : WordTrace (prefixWord ++ tailWord_3286685) baseStart_3286685 baseEnd_3286685 := by
    simpa [prefixWord, tailWord_3286685, baseEnd_3286685] using wordTrace_append hprefix tailTrace_3286685
  have hstable : (prefixWord ++ tailWord_3286685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286685).length < 2 ^ (prefixWord ++ tailWord_3286685).sum := by decide
  have hdescent : baseEnd_3286685 < baseStart_3286685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286689 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 5]
def baseStart_3286689 : Nat := 118140960795 + 3286689 * 2 ^ 59
def prefixEnd_3286689 : Nat := 4983230072969 + 3 ^ 40 * 3286689 * 2
def baseEnd_3286689 : Nat := 375033604187821455082733

theorem tailTrace_3286689 : CollatzResearch.WordTrace tailWord_3286689 prefixEnd_3286689 375033604187821455082733 := by
  unfold tailWord_3286689
  simp only [CollatzResearch.WordTrace]
  refine ⟨119875395989894549637199121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79916930659929699758132747 119875395989894549637199121)
  ·
    refine ⟨89906546992420912227899341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119875395989894549637199121 89906546992420912227899341)
    ·
      refine ⟨33714955122157842085462253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89906546992420912227899341 33714955122157842085462253)
      ·
        refine ⟨12643108170809190782048345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33714955122157842085462253 12643108170809190782048345)
        ·
          refine ⟨9482331128106893086536259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12643108170809190782048345 9482331128106893086536259)
          ·
            refine ⟨14223496692160339629804389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9482331128106893086536259 14223496692160339629804389)
            ·
              refine ⟨2666905629780063680588323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14223496692160339629804389 2666905629780063680588323)
              ·
                refine ⟨4000358444670095520882485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666905629780063680588323 4000358444670095520882485)
                ·
                  refine ⟨375033604187821455082733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000358444670095520882485 375033604187821455082733)
                  ·
                    rfl

theorem cell22_3286689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_3286689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286689 prefixEnd_3286689 := by exact prefixLift 3286689
  have htrace : WordTrace (prefixWord ++ tailWord_3286689) baseStart_3286689 baseEnd_3286689 := by
    simpa [prefixWord, tailWord_3286689, baseEnd_3286689] using wordTrace_append hprefix tailTrace_3286689
  have hstable : (prefixWord ++ tailWord_3286689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286689).length < 2 ^ (prefixWord ++ tailWord_3286689).sum := by decide
  have hdescent : baseEnd_3286689 < baseStart_3286689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286719 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 1, 4]
def baseStart_3286719 : Nat := 118140960795 + 3286719 * 2 ^ 59
def prefixEnd_3286719 : Nat := 4983230072969 + 3 ^ 40 * 3286719 * 2
def baseEnd_3286719 : Nat := 1125111082176554286998107

theorem tailTrace_3286719 : CollatzResearch.WordTrace tailWord_3286719 prefixEnd_3286719 1125111082176554286998107 := by
  unfold tailWord_3286719
  simp only [CollatzResearch.WordTrace]
  refine ⟨119876490179785864760791211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79917660119857243173860807 119876490179785864760791211)
  ·
    refine ⟨179814735269678797141186817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119876490179785864760791211 179814735269678797141186817)
    ·
      refine ⟨134861051452259097855890113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179814735269678797141186817 134861051452259097855890113)
      ·
        refine ⟨101145788589194323391917585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134861051452259097855890113 101145788589194323391917585)
        ·
          refine ⟨75859341441895742543938189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101145788589194323391917585 75859341441895742543938189)
          ·
            refine ⟨28447253040710903453976821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75859341441895742543938189 28447253040710903453976821)
            ·
              refine ⟨2666929972566647198810327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28447253040710903453976821 2666929972566647198810327)
              ·
                refine ⟨4000394958849970798215491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666929972566647198810327 4000394958849970798215491)
                ·
                  refine ⟨6000592438274956197323237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000394958849970798215491 6000592438274956197323237)
                  ·
                    refine ⟨1125111082176554286998107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6000592438274956197323237 1125111082176554286998107)
                    ·
                      rfl

theorem cell22_3286719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_3286719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286719 prefixEnd_3286719 := by exact prefixLift 3286719
  have htrace : WordTrace (prefixWord ++ tailWord_3286719) baseStart_3286719 baseEnd_3286719 := by
    simpa [prefixWord, tailWord_3286719, baseEnd_3286719] using wordTrace_append hprefix tailTrace_3286719
  have hstable : (prefixWord ++ tailWord_3286719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286719).length < 2 ^ (prefixWord ++ tailWord_3286719).sum := by decide
  have hdescent : baseEnd_3286719 < baseStart_3286719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286734 : List Nat := [4, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_3286734 : Nat := 118140960795 + 3286734 * 2 ^ 59
def prefixEnd_3286734 : Nat := 4983230072969 + 3 ^ 40 * 3286734 * 2
def baseEnd_3286734 : Nat := 375038738994366415957687

theorem tailTrace_3286734 : CollatzResearch.WordTrace tailWord_3286734 prefixEnd_3286734 375038738994366415957687 := by
  unfold tailWord_3286734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984629659341440290323407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79918024849821014881724837 14984629659341440290323407)
  ·
    refine ⟨22476944489012160435485111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14984629659341440290323407 22476944489012160435485111)
    ·
      refine ⟨33715416733518240653227667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22476944489012160435485111 33715416733518240653227667)
      ·
        refine ⟨50573125100277360979841501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33715416733518240653227667 50573125100277360979841501)
        ·
          refine ⟨18964921912604010367440563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50573125100277360979841501 18964921912604010367440563)
          ·
            refine ⟨28447382868906015551160845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18964921912604010367440563 28447382868906015551160845)
            ·
              refine ⟨10667768575839755831685317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28447382868906015551160845 10667768575839755831685317)
              ·
                refine ⟨2000206607969954218440997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10667768575839755831685317 2000206607969954218440997)
                ·
                  refine ⟨375038738994366415957687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000206607969954218440997 375038738994366415957687)
                  ·
                    rfl

theorem cell22_3286734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_3286734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286734 prefixEnd_3286734 := by exact prefixLift 3286734
  have htrace : WordTrace (prefixWord ++ tailWord_3286734) baseStart_3286734 baseEnd_3286734 := by
    simpa [prefixWord, tailWord_3286734, baseEnd_3286734] using wordTrace_append hprefix tailTrace_3286734
  have hstable : (prefixWord ++ tailWord_3286734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286734).length < 2 ^ (prefixWord ++ tailWord_3286734).sum := by decide
  have hdescent : baseEnd_3286734 < baseStart_3286734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286794 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_3286794 : Nat := 118140960795 + 3286794 * 2 ^ 59
def prefixEnd_3286794 : Nat := 4983230072969 + 3 ^ 40 * 3286794 * 2
def baseEnd_3286794 : Nat := 1125136756209279091372877

theorem tailTrace_3286794 : CollatzResearch.WordTrace tailWord_3286794 prefixEnd_3286794 1125136756209279091372877 := by
  unfold tailWord_3286794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29969806413628538142442859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79919483769676101713180957 29969806413628538142442859)
  ·
    refine ⟨44954709620442807213664289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29969806413628538142442859 44954709620442807213664289)
    ·
      refine ⟨33716032215332105410248217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44954709620442807213664289 33716032215332105410248217)
      ·
        refine ⟨25287024161499079057686163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33716032215332105410248217 25287024161499079057686163)
        ·
          refine ⟨37930536242248618586529245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25287024161499079057686163 37930536242248618586529245)
          ·
            refine ⟨14223951090843231969948467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37930536242248618586529245 14223951090843231969948467)
            ·
              refine ⟨21335926636264847954922701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14223951090843231969948467 21335926636264847954922701)
              ·
                refine ⟨8000972488599317983096013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21335926636264847954922701 8000972488599317983096013)
                ·
                  refine ⟨3000364683224744243661005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8000972488599317983096013 3000364683224744243661005)
                  ·
                    refine ⟨1125136756209279091372877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000364683224744243661005 1125136756209279091372877)
                    ·
                      rfl

theorem cell22_3286794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_3286794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286794 prefixEnd_3286794 := by exact prefixLift 3286794
  have htrace : WordTrace (prefixWord ++ tailWord_3286794) baseStart_3286794 baseEnd_3286794 := by
    simpa [prefixWord, tailWord_3286794, baseEnd_3286794] using wordTrace_append hprefix tailTrace_3286794
  have hstable : (prefixWord ++ tailWord_3286794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286794).length < 2 ^ (prefixWord ++ tailWord_3286794).sum := by decide
  have hdescent : baseEnd_3286794 < baseStart_3286794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286828 : List Nat := [2, 2, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_3286828 : Nat := 118140960795 + 3286828 * 2 ^ 59
def prefixEnd_3286828 : Nat := 4983230072969 + 3 ^ 40 * 3286828 * 2
def baseEnd_3286828 : Nat := 1125148395104114336022773

theorem tailTrace_3286828 : CollatzResearch.WordTrace tailWord_3286828 prefixEnd_3286828 1125148395104114336022773 := by
  unfold tailWord_3286828
  simp only [CollatzResearch.WordTrace]
  refine ⟨59940232868195488188254569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79920310490927317584339425 59940232868195488188254569)
  ·
    refine ⟨44955174651146616141190927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59940232868195488188254569 44955174651146616141190927)
    ·
      refine ⟨67432761976719924211786391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44955174651146616141190927 67432761976719924211786391)
      ·
        refine ⟨101149142965079886317679587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67432761976719924211786391 101149142965079886317679587)
        ·
          refine ⟨151723714447619829476519381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101149142965079886317679587 151723714447619829476519381)
          ·
            refine ⟨3556024557366089753355923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 151723714447619829476519381 3556024557366089753355923)
            ·
              refine ⟨5334036836049134630033885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556024557366089753355923 5334036836049134630033885)
              ·
                refine ⟨2000263813518425486262707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5334036836049134630033885 2000263813518425486262707)
                ·
                  refine ⟨3000395720277638229394061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000263813518425486262707 3000395720277638229394061)
                  ·
                    refine ⟨1125148395104114336022773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000395720277638229394061 1125148395104114336022773)
                    ·
                      rfl

theorem cell22_3286828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_3286828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286828 prefixEnd_3286828 := by exact prefixLift 3286828
  have htrace : WordTrace (prefixWord ++ tailWord_3286828) baseStart_3286828 baseEnd_3286828 := by
    simpa [prefixWord, tailWord_3286828, baseEnd_3286828] using wordTrace_append hprefix tailTrace_3286828
  have hstable : (prefixWord ++ tailWord_3286828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286828).length < 2 ^ (prefixWord ++ tailWord_3286828).sum := by decide
  have hdescent : baseEnd_3286828 < baseStart_3286828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286845 : List Nat := [1, 4, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_3286845 : Nat := 118140960795 + 3286845 * 2 ^ 59
def prefixEnd_3286845 : Nat := 4983230072969 + 3 ^ 40 * 3286845 * 2
def baseEnd_3286845 : Nat := 1125154214551531958347721

theorem tailTrace_3286845 : CollatzResearch.WordTrace tailWord_3286845 prefixEnd_3286845 1125154214551531958347721 := by
  unfold tailWord_3286845
  simp only [CollatzResearch.WordTrace]
  refine ⟨119881085777329388279877989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79920723851552925519918659 119881085777329388279877989)
  ·
    refine ⟨22477703583249260302477123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119881085777329388279877989 22477703583249260302477123)
    ·
      refine ⟨33716555374873890453715685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22477703583249260302477123 33716555374873890453715685)
      ·
        refine ⟨6321854132788854460071691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33716555374873890453715685 6321854132788854460071691)
        ·
          refine ⟨9482781199183281690107537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6321854132788854460071691 9482781199183281690107537)
          ·
            refine ⟨7112085899387461267580653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9482781199183281690107537 7112085899387461267580653)
            ·
              refine ⟨2667032212270297975342745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7112085899387461267580653 2667032212270297975342745)
              ·
                refine ⟨2000274159202723481507059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667032212270297975342745 2000274159202723481507059)
                ·
                  refine ⟨3000411238804085222260589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000274159202723481507059 3000411238804085222260589)
                  ·
                    refine ⟨1125154214551531958347721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000411238804085222260589 1125154214551531958347721)
                    ·
                      rfl

theorem cell22_3286845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_3286845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286845 prefixEnd_3286845 := by exact prefixLift 3286845
  have htrace : WordTrace (prefixWord ++ tailWord_3286845) baseStart_3286845 baseEnd_3286845 := by
    simpa [prefixWord, tailWord_3286845, baseEnd_3286845] using wordTrace_append hprefix tailTrace_3286845
  have hstable : (prefixWord ++ tailWord_3286845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286845).length < 2 ^ (prefixWord ++ tailWord_3286845).sum := by decide
  have hdescent : baseEnd_3286845 < baseStart_3286845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286929 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 5, 3]
def baseStart_3286929 : Nat := 118140960795 + 3286929 * 2 ^ 59
def prefixEnd_3286929 : Nat := 4983230072969 + 3 ^ 40 * 3286929 * 2
def baseEnd_3286929 : Nat := 1125182969468183739247463

theorem tailTrace_3286929 : CollatzResearch.WordTrace tailWord_3286929 prefixEnd_3286929 1125182969468183739247463 := by
  unfold tailWord_3286929
  simp only [CollatzResearch.WordTrace]
  refine ⟨119884149509025070625935841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79922766339350047083957227 119884149509025070625935841)
  ·
    refine ⟨89913112131768802969451881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119884149509025070625935841 89913112131768802969451881)
    ·
      refine ⟨67434834098826602227088911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89913112131768802969451881 67434834098826602227088911)
      ·
        refine ⟨101152251148239903340633367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67434834098826602227088911 101152251148239903340633367)
        ·
          refine ⟨151728376722359855010950051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101152251148239903340633367 151728376722359855010950051)
          ·
            refine ⟨227592565083539782516425077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151728376722359855010950051 227592565083539782516425077)
            ·
              refine ⟨21336802976581854610914851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227592565083539782516425077 21336802976581854610914851)
              ·
                refine ⟨32005204464872781916372277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21336802976581854610914851 32005204464872781916372277)
                ·
                  refine ⟨3000487918581823304659901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32005204464872781916372277 3000487918581823304659901)
                  ·
                    refine ⟨1125182969468183739247463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000487918581823304659901 1125182969468183739247463)
                    ·
                      rfl

theorem cell22_3286929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_3286929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286929 prefixEnd_3286929 := by exact prefixLift 3286929
  have htrace : WordTrace (prefixWord ++ tailWord_3286929) baseStart_3286929 baseEnd_3286929 := by
    simpa [prefixWord, tailWord_3286929, baseEnd_3286929] using wordTrace_append hprefix tailTrace_3286929
  have hstable : (prefixWord ++ tailWord_3286929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286929).length < 2 ^ (prefixWord ++ tailWord_3286929).sum := by decide
  have hdescent : baseEnd_3286929 < baseStart_3286929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286952 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3286952 : Nat := 118140960795 + 3286952 * 2 ^ 59
def prefixEnd_3286952 : Nat := 4983230072969 + 3 ^ 40 * 3286952 * 2
def baseEnd_3286952 : Nat := 1125190842838219345922393

theorem tailTrace_3286952 : CollatzResearch.WordTrace tailWord_3286952 prefixEnd_3286952 1125190842838219345922393 := by
  unfold tailWord_3286952
  simp only [CollatzResearch.WordTrace]
  refine ⟨59942494193970872777011555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79923325591961163702682073 59942494193970872777011555)
  ·
    refine ⟨89913741290956309165517333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59942494193970872777011555 89913741290956309165517333)
    ·
      refine ⟨4214706623013576992133625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89913741290956309165517333 4214706623013576992133625)
      ·
        refine ⟨3161029967260182744100219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4214706623013576992133625 3161029967260182744100219)
        ·
          refine ⟨4741544950890274116150329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161029967260182744100219 4741544950890274116150329)
          ·
            refine ⟨3556158713167705587112747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4741544950890274116150329 3556158713167705587112747)
            ·
              refine ⟨5334238069751558380669121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556158713167705587112747 5334238069751558380669121)
              ·
                refine ⟨4000678552313668785501841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5334238069751558380669121 4000678552313668785501841)
                ·
                  refine ⟨3000508914235251589126381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4000678552313668785501841 3000508914235251589126381)
                  ·
                    refine ⟨1125190842838219345922393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000508914235251589126381 1125190842838219345922393)
                    ·
                      rfl

theorem cell22_3286952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3286952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286952 prefixEnd_3286952 := by exact prefixLift 3286952
  have htrace : WordTrace (prefixWord ++ tailWord_3286952) baseStart_3286952 baseEnd_3286952 := by
    simpa [prefixWord, tailWord_3286952, baseEnd_3286952] using wordTrace_append hprefix tailTrace_3286952
  have hstable : (prefixWord ++ tailWord_3286952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286952).length < 2 ^ (prefixWord ++ tailWord_3286952).sum := by decide
  have hdescent : baseEnd_3286952 < baseStart_3286952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286976 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 5]
def baseStart_3286976 : Nat := 118140960795 + 3286976 * 2 ^ 59
def prefixEnd_3286976 : Nat := 4983230072969 + 3 ^ 40 * 3286976 * 2
def baseEnd_3286976 : Nat := 375066352842897094440773

theorem tailTrace_3286976 : CollatzResearch.WordTrace tailWord_3286976 prefixEnd_3286976 375066352842897094440773 := by
  unfold tailWord_3286976
  simp only [CollatzResearch.WordTrace]
  refine ⟨59942931869927398826448391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79923909159903198435264521 59942931869927398826448391)
  ·
    refine ⟨89914397804891098239672587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59942931869927398826448391 89914397804891098239672587)
    ·
      refine ⟨134871596707336647359508881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89914397804891098239672587 134871596707336647359508881)
      ·
        refine ⟨101153697530502485519631661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134871596707336647359508881 101153697530502485519631661)
        ·
          refine ⟨37932636573938432069861873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101153697530502485519631661 37932636573938432069861873)
          ·
            refine ⟨28449477430453824052396405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37932636573938432069861873 28449477430453824052396405)
            ·
              refine ⟨2667138509105046004912163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28449477430453824052396405 2667138509105046004912163)
              ·
                refine ⟨4000707763657569007368245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667138509105046004912163 4000707763657569007368245)
                ·
                  refine ⟨375066352842897094440773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000707763657569007368245 375066352842897094440773)
                  ·
                    rfl

theorem cell22_3286976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_3286976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3286976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3286976 prefixEnd_3286976 := by exact prefixLift 3286976
  have htrace : WordTrace (prefixWord ++ tailWord_3286976) baseStart_3286976 baseEnd_3286976 := by
    simpa [prefixWord, tailWord_3286976, baseEnd_3286976] using wordTrace_append hprefix tailTrace_3286976
  have hstable : (prefixWord ++ tailWord_3286976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286976).length < 2 ^ (prefixWord ++ tailWord_3286976).sum := by decide
  have hdescent : baseEnd_3286976 < baseStart_3286976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287051 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 2, 4]
def baseStart_3287051 : Nat := 118140960795 + 3287051 * 2 ^ 59
def prefixEnd_3287051 : Nat := 4983230072969 + 3 ^ 40 * 3287051 * 2
def baseEnd_3287051 : Nat := 1125224732561416087697089

theorem tailTrace_3287051 : CollatzResearch.WordTrace tailWord_3287051 prefixEnd_3287051 1125224732561416087697089 := by
  unfold tailWord_3287051
  simp only [CollatzResearch.WordTrace]
  refine ⟨119888599214583085461877007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79925732809722056974584671 119888599214583085461877007)
  ·
    refine ⟨179832898821874628192815511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119888599214583085461877007 179832898821874628192815511)
    ·
      refine ⟨269749348232811942289223267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179832898821874628192815511 269749348232811942289223267)
      ·
        refine ⟨404624022349217913433834901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269749348232811942289223267 404624022349217913433834901)
        ·
          refine ⟨18966751047619589692211011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 404624022349217913433834901 18966751047619589692211011)
          ·
            refine ⟨28450126571429384538316517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18966751047619589692211011 28450126571429384538316517)
            ·
              refine ⟨5334398732143009600934347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28450126571429384538316517 5334398732143009600934347)
              ·
                refine ⟨8001598098214514401401521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334398732143009600934347 8001598098214514401401521)
                ·
                  refine ⟨6001198573660885801051141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8001598098214514401401521 6001198573660885801051141)
                  ·
                    refine ⟨1125224732561416087697089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6001198573660885801051141 1125224732561416087697089)
                    ·
                      rfl

theorem cell22_3287051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4].length) (baseStart_3287051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287051 prefixEnd_3287051 := by exact prefixLift 3287051
  have htrace : WordTrace (prefixWord ++ tailWord_3287051) baseStart_3287051 baseEnd_3287051 := by
    simpa [prefixWord, tailWord_3287051, baseEnd_3287051] using wordTrace_append hprefix tailTrace_3287051
  have hstable : (prefixWord ++ tailWord_3287051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287051).length < 2 ^ (prefixWord ++ tailWord_3287051).sum := by decide
  have hdescent : baseEnd_3287051 < baseStart_3287051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287102 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_3287102 : Nat := 118140960795 + 3287102 * 2 ^ 59
def prefixEnd_3287102 : Nat := 4983230072969 + 3 ^ 40 * 3287102 * 2
def baseEnd_3287102 : Nat := 1125242190903668954671933

theorem tailTrace_3287102 : CollatzResearch.WordTrace tailWord_3287102 prefixEnd_3287102 1125242190903668954671933 := by
  unfold tailWord_3287102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986307417174790146497945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79926972891598880781322373 14986307417174790146497945)
  ·
    refine ⟨11239730562881092609873459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14986307417174790146497945 11239730562881092609873459)
    ·
      refine ⟨16859595844321638914810189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11239730562881092609873459 16859595844321638914810189)
      ·
        refine ⟨6322348441620614593053821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16859595844321638914810189 6322348441620614593053821)
        ·
          refine ⟨2370880665607730472395183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6322348441620614593053821 2370880665607730472395183)
          ·
            refine ⟨3556320998411595708592775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370880665607730472395183 3556320998411595708592775)
            ·
              refine ⟨5334481497617393562889163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556320998411595708592775 5334481497617393562889163)
              ·
                refine ⟨8001722246426090344333745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334481497617393562889163 8001722246426090344333745)
                ·
                  refine ⟨6001291684819567758250309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8001722246426090344333745 6001291684819567758250309)
                  ·
                    refine ⟨1125242190903668954671933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6001291684819567758250309 1125242190903668954671933)
                    ·
                      rfl

theorem cell22_3287102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_3287102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287102 prefixEnd_3287102 := by exact prefixLift 3287102
  have htrace : WordTrace (prefixWord ++ tailWord_3287102) baseStart_3287102 baseEnd_3287102 := by
    simpa [prefixWord, tailWord_3287102, baseEnd_3287102] using wordTrace_append hprefix tailTrace_3287102
  have hstable : (prefixWord ++ tailWord_3287102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287102).length < 2 ^ (prefixWord ++ tailWord_3287102).sum := by decide
  have hdescent : baseEnd_3287102 < baseStart_3287102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287109 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3287109 : Nat := 118140960795 + 3287109 * 2 ^ 59
def prefixEnd_3287109 : Nat := 4983230072969 + 3 ^ 40 * 3287109 * 2
def baseEnd_3287109 : Nat := 1125244587146723269746911

theorem tailTrace_3287109 : CollatzResearch.WordTrace tailWord_3287109 prefixEnd_3287109 1125244587146723269746911 := by
  unfold tailWord_3287109
  simp only [CollatzResearch.WordTrace]
  refine ⟨119890714648372961367488381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79927143098915307578325587 119890714648372961367488381)
  ·
    refine ⟨44959017993139860512808143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119890714648372961367488381 44959017993139860512808143)
    ·
      refine ⟨67438526989709790769212215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44959017993139860512808143 67438526989709790769212215)
      ·
        refine ⟨101157790484564686153818323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67438526989709790769212215 101157790484564686153818323)
        ·
          refine ⟨151736685726847029230727485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101157790484564686153818323 151736685726847029230727485)
          ·
            refine ⟨56901257147567635961522807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151736685726847029230727485 56901257147567635961522807)
            ·
              refine ⟨85351885721351453942284211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56901257147567635961522807 85351885721351453942284211)
              ·
                refine ⟨128027828582027180913426317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85351885721351453942284211 128027828582027180913426317)
                ·
                  refine ⟨48010435718260192842534869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128027828582027180913426317 48010435718260192842534869)
                  ·
                    refine ⟨1125244587146723269746911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48010435718260192842534869 1125244587146723269746911)
                    ·
                      rfl

theorem cell22_3287109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3287109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287109 prefixEnd_3287109 := by exact prefixLift 3287109
  have htrace : WordTrace (prefixWord ++ tailWord_3287109) baseStart_3287109 baseEnd_3287109 := by
    simpa [prefixWord, tailWord_3287109, baseEnd_3287109] using wordTrace_append hprefix tailTrace_3287109
  have hstable : (prefixWord ++ tailWord_3287109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287109).length < 2 ^ (prefixWord ++ tailWord_3287109).sum := by decide
  have hdescent : baseEnd_3287109 < baseStart_3287109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287128 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 5]
def baseStart_3287128 : Nat := 118140960795 + 3287128 * 2 ^ 59
def prefixEnd_3287128 : Nat := 4983230072969 + 3 ^ 40 * 3287128 * 2
def baseEnd_3287128 : Nat := 375083697078337851173951

theorem tailTrace_3287128 : CollatzResearch.WordTrace tailWord_3287128 prefixEnd_3287128 375083697078337851173951 := by
  unfold tailWord_3287128
  simp only [CollatzResearch.WordTrace]
  refine ⟨59945703817652063806215019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79927605090202751741620025 59945703817652063806215019)
  ·
    refine ⟨89918555726478095709322529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59945703817652063806215019 89918555726478095709322529)
    ·
      refine ⟨67438916794858571781991897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89918555726478095709322529 67438916794858571781991897)
      ·
        refine ⟨50579187596143928836493923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67438916794858571781991897 50579187596143928836493923)
        ·
          refine ⟨75868781394215893254740885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50579187596143928836493923 75868781394215893254740885)
          ·
            refine ⟨3556349127853869996315979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75868781394215893254740885 3556349127853869996315979)
            ·
              refine ⟨5334523691780804994473969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556349127853869996315979 5334523691780804994473969)
              ·
                refine ⟨4000892768835603745855477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5334523691780804994473969 4000892768835603745855477)
                ·
                  refine ⟨375083697078337851173951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000892768835603745855477 375083697078337851173951)
                  ·
                    rfl

theorem cell22_3287128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_3287128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287128 prefixEnd_3287128 := by exact prefixLift 3287128
  have htrace : WordTrace (prefixWord ++ tailWord_3287128) baseStart_3287128 baseEnd_3287128 := by
    simpa [prefixWord, tailWord_3287128, baseEnd_3287128] using wordTrace_append hprefix tailTrace_3287128
  have hstable : (prefixWord ++ tailWord_3287128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287128).length < 2 ^ (prefixWord ++ tailWord_3287128).sum := by decide
  have hdescent : baseEnd_3287128 < baseStart_3287128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287201 : List Nat := [1, 2, 3, 3, 1, 2, 1, 9]
def baseStart_3287201 : Nat := 118140960795 + 3287201 * 2 ^ 59
def prefixEnd_3287201 : Nat := 4983230072969 + 3 ^ 40 * 3287201 * 2
def baseEnd_3287201 : Nat := 125030675625207299605181

theorem tailTrace_3287201 : CollatzResearch.WordTrace tailWord_3287201 prefixEnd_3287201 125030675625207299605181 := by
  unfold tailWord_3287201
  simp only [CollatzResearch.WordTrace]
  refine ⟨119894070164039661079837457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79929380109359774053224971 119894070164039661079837457)
  ·
    refine ⟨89920552623029745809878093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119894070164039661079837457 89920552623029745809878093)
    ·
      refine ⟨33720207233636154678704285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89920552623029745809878093 33720207233636154678704285)
      ·
        refine ⟨12645077712613558004514107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33720207233636154678704285 12645077712613558004514107)
        ·
          refine ⟨18967616568920337006771161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12645077712613558004514107 18967616568920337006771161)
          ·
            refine ⟨14225712426690252755078371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18967616568920337006771161 14225712426690252755078371)
            ·
              refine ⟨21338568640035379132617557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14225712426690252755078371 21338568640035379132617557)
              ·
                refine ⟨125030675625207299605181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21338568640035379132617557 125030675625207299605181)
                ·
                  rfl

theorem cell22_3287201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 9].length) (baseStart_3287201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287201 prefixEnd_3287201 := by exact prefixLift 3287201
  have htrace : WordTrace (prefixWord ++ tailWord_3287201) baseStart_3287201 baseEnd_3287201 := by
    simpa [prefixWord, tailWord_3287201, baseEnd_3287201] using wordTrace_append hprefix tailTrace_3287201
  have hstable : (prefixWord ++ tailWord_3287201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287201).length < 2 ^ (prefixWord ++ tailWord_3287201).sum := by decide
  have hdescent : baseEnd_3287201 < baseStart_3287201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287267 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 3, 3]
def baseStart_3287267 : Nat := 118140960795 + 3287267 * 2 ^ 59
def prefixEnd_3287267 : Nat := 4983230072969 + 3 ^ 40 * 3287267 * 2
def baseEnd_3287267 : Nat := 1125298673775663524296427

theorem tailTrace_3287267 : CollatzResearch.WordTrace tailWord_3287267 prefixEnd_3287267 1125298673775663524296427 := by
  unfold tailWord_3287267
  simp only [CollatzResearch.WordTrace]
  refine ⟨119896477381800554351740055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79930984921200369567826703 119896477381800554351740055)
  ·
    refine ⟨179844716072700831527610083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119896477381800554351740055 179844716072700831527610083)
    ·
      refine ⟨269767074109051247291415125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179844716072700831527610083 269767074109051247291415125)
      ·
        refine ⟨3161332899715444304196271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 269767074109051247291415125 3161332899715444304196271)
        ·
          refine ⟨4741999349573166456294407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161332899715444304196271 4741999349573166456294407)
          ·
            refine ⟨7112999024359749684441611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741999349573166456294407 7112999024359749684441611)
            ·
              refine ⟨10669498536539624526662417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112999024359749684441611 10669498536539624526662417)
              ·
                refine ⟨8002123902404718394996813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10669498536539624526662417 8002123902404718394996813)
                ·
                  refine ⟨3000796463401769398123805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8002123902404718394996813 3000796463401769398123805)
                  ·
                    refine ⟨1125298673775663524296427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000796463401769398123805 1125298673775663524296427)
                    ·
                      rfl

theorem cell22_3287267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 3].length) (baseStart_3287267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287267 prefixEnd_3287267 := by exact prefixLift 3287267
  have htrace : WordTrace (prefixWord ++ tailWord_3287267) baseStart_3287267 baseEnd_3287267 := by
    simpa [prefixWord, tailWord_3287267, baseEnd_3287267] using wordTrace_append hprefix tailTrace_3287267
  have hstable : (prefixWord ++ tailWord_3287267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287267).length < 2 ^ (prefixWord ++ tailWord_3287267).sum := by decide
  have hdescent : baseEnd_3287267 < baseStart_3287267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287308 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 6]
def baseStart_3287308 : Nat := 118140960795 + 3287308 * 2 ^ 59
def prefixEnd_3287308 : Nat := 4983230072969 + 3 ^ 40 * 3287308 * 2
def baseEnd_3287308 : Nat := 375104236304517694673767

theorem tailTrace_3287308 : CollatzResearch.WordTrace tailWord_3287308 prefixEnd_3287308 375104236304517694673767 := by
  unfold tailWord_3287308
  simp only [CollatzResearch.WordTrace]
  refine ⟨59948986387326009176991289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79931981849768012235988385 59948986387326009176991289)
  ·
    refine ⟨44961739790494506882743467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59948986387326009176991289 44961739790494506882743467)
    ·
      refine ⟨67442609685741760324115201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44961739790494506882743467 67442609685741760324115201)
      ·
        refine ⟨50581957264306320243086401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67442609685741760324115201 50581957264306320243086401)
        ·
          refine ⟨37936467948229740182314801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50581957264306320243086401 37936467948229740182314801)
          ·
            refine ⟨28452350961172305136736101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37936467948229740182314801 28452350961172305136736101)
            ·
              refine ⟨5334815805219807213138019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28452350961172305136736101 5334815805219807213138019)
              ·
                refine ⟨8002223707829710819707029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334815805219807213138019 8002223707829710819707029)
                ·
                  refine ⟨375104236304517694673767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8002223707829710819707029 375104236304517694673767)
                  ·
                    rfl

theorem cell22_3287308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_3287308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287308 prefixEnd_3287308 := by exact prefixLift 3287308
  have htrace : WordTrace (prefixWord ++ tailWord_3287308) baseStart_3287308 baseEnd_3287308 := by
    simpa [prefixWord, tailWord_3287308, baseEnd_3287308] using wordTrace_append hprefix tailTrace_3287308
  have hstable : (prefixWord ++ tailWord_3287308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287308).length < 2 ^ (prefixWord ++ tailWord_3287308).sum := by decide
  have hdescent : baseEnd_3287308 < baseStart_3287308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287323 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 1, 5]
def baseStart_3287323 : Nat := 118140960795 + 3287323 * 2 ^ 59
def prefixEnd_3287323 : Nat := 4983230072969 + 3 ^ 40 * 3287323 * 2
def baseEnd_3287323 : Nat := 1125317843720098044896255

theorem tailTrace_3287323 : CollatzResearch.WordTrace tailWord_3287323 prefixEnd_3287323 1125317843720098044896255 := by
  unfold tailWord_3287323
  simp only [CollatzResearch.WordTrace]
  refine ⟨119898519869597675915778623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79932346579731783943852415 119898519869597675915778623)
  ·
    refine ⟨179847779804396513873667935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119898519869597675915778623 179847779804396513873667935)
    ·
      refine ⟨269771669706594770810501903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179847779804396513873667935 269771669706594770810501903)
      ·
        refine ⟨404657504559892156215752855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269771669706594770810501903 404657504559892156215752855)
        ·
          refine ⟨606986256839838234323629283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404657504559892156215752855 606986256839838234323629283)
          ·
            refine ⟨910479385259757351485443925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606986256839838234323629283 910479385259757351485443925)
            ·
              refine ⟨5334840148006390731360023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 910479385259757351485443925 5334840148006390731360023)
              ·
                refine ⟨8002260222009586097040035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334840148006390731360023 8002260222009586097040035)
                ·
                  refine ⟨12003390333014379145560053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002260222009586097040035 12003390333014379145560053)
                  ·
                    refine ⟨1125317843720098044896255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12003390333014379145560053 1125317843720098044896255)
                    ·
                      rfl

theorem cell22_3287323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5].length) (baseStart_3287323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287323 prefixEnd_3287323 := by exact prefixLift 3287323
  have htrace : WordTrace (prefixWord ++ tailWord_3287323) baseStart_3287323 baseEnd_3287323 := by
    simpa [prefixWord, tailWord_3287323, baseEnd_3287323] using wordTrace_append hprefix tailTrace_3287323
  have hstable : (prefixWord ++ tailWord_3287323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287323).length < 2 ^ (prefixWord ++ tailWord_3287323).sum := by decide
  have hdescent : baseEnd_3287323 < baseStart_3287323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287335 : List Nat := [1, 1, 8, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3287335 : Nat := 118140960795 + 3287335 * 2 ^ 59
def prefixEnd_3287335 : Nat := 4983230072969 + 3 ^ 40 * 3287335 * 2
def baseEnd_3287335 : Nat := 1125321951565334013596219

theorem tailTrace_3287335 : CollatzResearch.WordTrace tailWord_3287335 prefixEnd_3287335 1125321951565334013596219 := by
  unfold tailWord_3287335
  simp only [CollatzResearch.WordTrace]
  refine ⟨119898957545554201965215459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79932638363702801310143639 119898957545554201965215459)
  ·
    refine ⟨179848436318331302947823189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119898957545554201965215459 179848436318331302947823189)
    ·
      refine ⟨2107598863105444956419803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 179848436318331302947823189 2107598863105444956419803)
      ·
        refine ⟨3161398294658167434629705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107598863105444956419803 3161398294658167434629705)
        ·
          refine ⟨2371048720993625575972279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3161398294658167434629705 2371048720993625575972279)
          ·
            refine ⟨3556573081490438363958419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371048720993625575972279 3556573081490438363958419)
            ·
              refine ⟨5334859622235657545937629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556573081490438363958419 5334859622235657545937629)
              ·
                refine ⟨2000572358338371579726611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5334859622235657545937629 2000572358338371579726611)
                ·
                  refine ⟨3000858537507557369589917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000572358338371579726611 3000858537507557369589917)
                  ·
                    refine ⟨1125321951565334013596219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000858537507557369589917 1125321951565334013596219)
                    ·
                      rfl

theorem cell22_3287335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3287335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287335 prefixEnd_3287335 := by exact prefixLift 3287335
  have htrace : WordTrace (prefixWord ++ tailWord_3287335) baseStart_3287335 baseEnd_3287335 := by
    simpa [prefixWord, tailWord_3287335, baseEnd_3287335] using wordTrace_append hprefix tailTrace_3287335
  have hstable : (prefixWord ++ tailWord_3287335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287335).length < 2 ^ (prefixWord ++ tailWord_3287335).sum := by decide
  have hdescent : baseEnd_3287335 < baseStart_3287335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287353 : List Nat := [1, 2, 1, 6, 1, 1, 10]
def baseStart_3287353 : Nat := 118140960795 + 3287353 * 2 ^ 59
def prefixEnd_3287353 : Nat := 4983230072969 + 3 ^ 40 * 3287353 * 2
def baseEnd_3287353 : Nat := 41678819012340295060969

theorem tailTrace_3287353 : CollatzResearch.WordTrace tailWord_3287353 prefixEnd_3287353 41678819012340295060969 := by
  unfold tailWord_3287353
  simp only [CollatzResearch.WordTrace]
  refine ⟨119899614059488991039370713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79933076039659327359580475 119899614059488991039370713)
  ·
    refine ⟨89924710544616743279528035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119899614059488991039370713 89924710544616743279528035)
    ·
      refine ⟨134887065816925114919292053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89924710544616743279528035 134887065816925114919292053)
      ·
        refine ⟨6322831210168364761841815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134887065816925114919292053 6322831210168364761841815)
        ·
          refine ⟨9484246815252547142762723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322831210168364761841815 9484246815252547142762723)
          ·
            refine ⟨14226370222878820714144085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484246815252547142762723 14226370222878820714144085)
            ·
              refine ⟨41678819012340295060969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14226370222878820714144085 41678819012340295060969)
              ·
                rfl

theorem cell22_3287353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 10].length) (baseStart_3287353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287353 prefixEnd_3287353 := by exact prefixLift 3287353
  have htrace : WordTrace (prefixWord ++ tailWord_3287353) baseStart_3287353 baseEnd_3287353 := by
    simpa [prefixWord, tailWord_3287353, baseEnd_3287353] using wordTrace_append hprefix tailTrace_3287353
  have hstable : (prefixWord ++ tailWord_3287353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287353).length < 2 ^ (prefixWord ++ tailWord_3287353).sum := by decide
  have hdescent : baseEnd_3287353 < baseStart_3287353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287419 : List Nat := [1, 1, 1, 1, 1, 7, 4, 2, 1, 3]
def baseStart_3287419 : Nat := 118140960795 + 3287419 * 2 ^ 59
def prefixEnd_3287419 : Nat := 4983230072969 + 3 ^ 40 * 3287419 * 2
def baseEnd_3287419 : Nat := 1125350706481985794495961

theorem tailTrace_3287419 : CollatzResearch.WordTrace tailWord_3287419 prefixEnd_3287419 1125350706481985794495961 := by
  unfold tailWord_3287419
  simp only [CollatzResearch.WordTrace]
  refine ⟨119902021277249884311273311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79934680851499922874182207 119902021277249884311273311)
  ·
    refine ⟨179853031915874826466909967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119902021277249884311273311 179853031915874826466909967)
    ·
      refine ⟨269779547873812239700364951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179853031915874826466909967 269779547873812239700364951)
      ·
        refine ⟨404669321810718359550547427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269779547873812239700364951 404669321810718359550547427)
        ·
          refine ⟨607003982716077539325821141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404669321810718359550547427 607003982716077539325821141)
          ·
            refine ⟨14226655844908067327948933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 607003982716077539325821141 14226655844908067327948933)
            ·
              refine ⟨2667497970920262623990425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14226655844908067327948933 2667497970920262623990425)
              ·
                refine ⟨2000623478190196967992819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667497970920262623990425 2000623478190196967992819)
                ·
                  refine ⟨3000935217285295451989229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000623478190196967992819 3000935217285295451989229)
                  ·
                    refine ⟨1125350706481985794495961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000935217285295451989229 1125350706481985794495961)
                    ·
                      rfl

theorem cell22_3287419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 3].length) (baseStart_3287419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287419 prefixEnd_3287419 := by exact prefixLift 3287419
  have htrace : WordTrace (prefixWord ++ tailWord_3287419) baseStart_3287419 baseEnd_3287419 := by
    simpa [prefixWord, tailWord_3287419, baseEnd_3287419] using wordTrace_append hprefix tailTrace_3287419
  have hstable : (prefixWord ++ tailWord_3287419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287419).length < 2 ^ (prefixWord ++ tailWord_3287419).sum := by decide
  have hdescent : baseEnd_3287419 < baseStart_3287419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287445 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3287445 : Nat := 118140960795 + 3287445 * 2 ^ 59
def prefixEnd_3287445 : Nat := 4983230072969 + 3 ^ 40 * 3287445 * 2
def baseEnd_3287445 : Nat := 1125359606813330393345881

theorem tailTrace_3287445 : CollatzResearch.WordTrace tailWord_3287445 prefixEnd_3287445 1125359606813330393345881 := by
  unfold tailWord_3287445
  simp only [CollatzResearch.WordTrace]
  refine ⟨119902969575155690751719789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79935313050103793834479859 119902969575155690751719789)
  ·
    refine ⟨44963613590683384031894921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119902969575155690751719789 44963613590683384031894921)
    ·
      refine ⟨33722710193012538023921191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44963613590683384031894921 33722710193012538023921191)
      ·
        refine ⟨50584065289518807035881787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33722710193012538023921191 50584065289518807035881787)
        ·
          refine ⟨75876097934278210553822681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50584065289518807035881787 75876097934278210553822681)
          ·
            refine ⟨56907073450708657915367011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75876097934278210553822681 56907073450708657915367011)
            ·
              refine ⟨85360610176062986873050517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56907073450708657915367011 85360610176062986873050517)
              ·
                refine ⟨4001278602002952509674243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85360610176062986873050517 4001278602002952509674243)
                ·
                  refine ⟨6001917903004428764511365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001278602002952509674243 6001917903004428764511365)
                  ·
                    refine ⟨1125359606813330393345881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6001917903004428764511365 1125359606813330393345881)
                    ·
                      rfl

theorem cell22_3287445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3287445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287445 prefixEnd_3287445 := by exact prefixLift 3287445
  have htrace : WordTrace (prefixWord ++ tailWord_3287445) baseStart_3287445 baseEnd_3287445 := by
    simpa [prefixWord, tailWord_3287445, baseEnd_3287445] using wordTrace_append hprefix tailTrace_3287445
  have hstable : (prefixWord ++ tailWord_3287445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287445).length < 2 ^ (prefixWord ++ tailWord_3287445).sum := by decide
  have hdescent : baseEnd_3287445 < baseStart_3287445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287477 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 6]
def baseStart_3287477 : Nat := 118140960795 + 3287477 * 2 ^ 59
def prefixEnd_3287477 : Nat := 4983230072969 + 3 ^ 40 * 3287477 * 2
def baseEnd_3287477 : Nat := 375123520355764325515261

theorem tailTrace_3287477 : CollatzResearch.WordTrace tailWord_3287477 prefixEnd_3287477 375123520355764325515261 := by
  unfold tailWord_3287477
  simp only [CollatzResearch.WordTrace]
  refine ⟨119904136711039760216884685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79936091140693173477923123 119904136711039760216884685)
  ·
    refine ⟨44964051266639910081331757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119904136711039760216884685 44964051266639910081331757)
    ·
      refine ⟨16861519224989966280499409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44964051266639910081331757 16861519224989966280499409)
      ·
        refine ⟨12646139418742474710374557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16861519224989966280499409 12646139418742474710374557)
        ·
          refine ⟨4742302282028428016390459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12646139418742474710374557 4742302282028428016390459)
          ·
            refine ⟨7113453423042642024585689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4742302282028428016390459 7113453423042642024585689)
            ·
              refine ⟨5335090067281981518439267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7113453423042642024585689 5335090067281981518439267)
              ·
                refine ⟨8002635100922972277658901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335090067281981518439267 8002635100922972277658901)
                ·
                  refine ⟨375123520355764325515261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8002635100922972277658901 375123520355764325515261)
                  ·
                    rfl

theorem cell22_3287477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_3287477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287477 prefixEnd_3287477 := by exact prefixLift 3287477
  have htrace : WordTrace (prefixWord ++ tailWord_3287477) baseStart_3287477 baseEnd_3287477 := by
    simpa [prefixWord, tailWord_3287477, baseEnd_3287477] using wordTrace_append hprefix tailTrace_3287477
  have hstable : (prefixWord ++ tailWord_3287477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287477).length < 2 ^ (prefixWord ++ tailWord_3287477).sum := by decide
  have hdescent : baseEnd_3287477 < baseStart_3287477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287488 : List Nat := [2, 1, 1, 2, 3, 1, 1, 11]
def baseStart_3287488 : Nat := 118140960795 + 3287488 * 2 ^ 59
def prefixEnd_3287488 : Nat := 4983230072969 + 3 ^ 40 * 3287488 * 2
def baseEnd_3287488 : Nat := 125041591843565846057861

theorem tailTrace_3287488 : CollatzResearch.WordTrace tailWord_3287488 prefixEnd_3287488 125041591843565846057861 := by
  unfold tailWord_3287488
  simp only [CollatzResearch.WordTrace]
  refine ⟨59952268956999954547767559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79936358609333272730356745 59952268956999954547767559)
  ·
    refine ⟨89928403435499931821651339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59952268956999954547767559 89928403435499931821651339)
    ·
      refine ⟨134892605153249897732477009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89928403435499931821651339 134892605153249897732477009)
      ·
        refine ⟨101169453864937423299357757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134892605153249897732477009 101169453864937423299357757)
        ·
          refine ⟨37938545199351533737259159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101169453864937423299357757 37938545199351533737259159)
          ·
            refine ⟨56907817799027300605888739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37938545199351533737259159 56907817799027300605888739)
            ·
              refine ⟨85361726698540950908833109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56907817799027300605888739 85361726698540950908833109)
              ·
                refine ⟨125041591843565846057861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 85361726698540950908833109 125041591843565846057861)
                ·
                  rfl

theorem cell22_3287488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_3287488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287488 prefixEnd_3287488 := by exact prefixLift 3287488
  have htrace : WordTrace (prefixWord ++ tailWord_3287488) baseStart_3287488 baseEnd_3287488 := by
    simpa [prefixWord, tailWord_3287488, baseEnd_3287488] using wordTrace_append hprefix tailTrace_3287488
  have hstable : (prefixWord ++ tailWord_3287488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287488).length < 2 ^ (prefixWord ++ tailWord_3287488).sum := by decide
  have hdescent : baseEnd_3287488 < baseStart_3287488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287503 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 9]
def baseStart_3287503 : Nat := 118140960795 + 3287503 * 2 ^ 59
def prefixEnd_3287503 : Nat := 4983230072969 + 3 ^ 40 * 3287503 * 2
def baseEnd_3287503 : Nat := 1125379461398637575395703

theorem tailTrace_3287503 : CollatzResearch.WordTrace tailWord_3287503 prefixEnd_3287503 1125379461398637575395703 := by
  unfold tailWord_3287503
  simp only [CollatzResearch.WordTrace]
  refine ⟨119905085008945566657331163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79936723339297044438220775 119905085008945566657331163)
  ·
    refine ⟨179857627513418349985996745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119905085008945566657331163 179857627513418349985996745)
    ·
      refine ⟨134893220635063762489497559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179857627513418349985996745 134893220635063762489497559)
      ·
        refine ⟨202339830952595643734246339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134893220635063762489497559 202339830952595643734246339)
        ·
          refine ⟨303509746428893465601369509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202339830952595643734246339 303509746428893465601369509)
          ·
            refine ⟨56908077455417524800256783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303509746428893465601369509 56908077455417524800256783)
            ·
              refine ⟨85362116183126287200385175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56908077455417524800256783 85362116183126287200385175)
              ·
                refine ⟨128043174274689430800577763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85362116183126287200385175 128043174274689430800577763)
                ·
                  refine ⟨192064761412034146200866645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128043174274689430800577763 192064761412034146200866645)
                  ·
                    refine ⟨1125379461398637575395703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192064761412034146200866645 1125379461398637575395703)
                    ·
                      rfl

theorem cell22_3287503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_3287503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287503 prefixEnd_3287503 := by exact prefixLift 3287503
  have htrace : WordTrace (prefixWord ++ tailWord_3287503) baseStart_3287503 baseEnd_3287503 := by
    simpa [prefixWord, tailWord_3287503, baseEnd_3287503] using wordTrace_append hprefix tailTrace_3287503
  have hstable : (prefixWord ++ tailWord_3287503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287503).length < 2 ^ (prefixWord ++ tailWord_3287503).sum := by decide
  have hdescent : baseEnd_3287503 < baseStart_3287503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287558 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3287558 : Nat := 118140960795 + 3287558 * 2 ^ 59
def prefixEnd_3287558 : Nat := 4983230072969 + 3 ^ 40 * 3287558 * 2
def baseEnd_3287558 : Nat := 1125398289022635765270535

theorem tailTrace_3287558 : CollatzResearch.WordTrace tailWord_3287558 prefixEnd_3287558 1125398289022635765270535 := by
  unfold tailWord_3287558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747096594492072220330729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79938060682497540700388885 3747096594492072220330729)
  ·
    refine ⟨2810322445869054165248047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3747096594492072220330729 2810322445869054165248047)
    ·
      refine ⟨4215483668803581247872071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810322445869054165248047 4215483668803581247872071)
      ·
        refine ⟨6323225503205371871808107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215483668803581247872071 6323225503205371871808107)
        ·
          refine ⟨9484838254808057807712161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323225503205371871808107 9484838254808057807712161)
          ·
            refine ⟨7113628691106043355784121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9484838254808057807712161 7113628691106043355784121)
            ·
              refine ⟨5335221518329532516838091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7113628691106043355784121 5335221518329532516838091)
              ·
                refine ⟨8002832277494298775257137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335221518329532516838091 8002832277494298775257137)
                ·
                  refine ⟨6002124208120724081442853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8002832277494298775257137 6002124208120724081442853)
                  ·
                    refine ⟨1125398289022635765270535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002124208120724081442853 1125398289022635765270535)
                    ·
                      rfl

theorem cell22_3287558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3287558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287558 prefixEnd_3287558 := by exact prefixLift 3287558
  have htrace : WordTrace (prefixWord ++ tailWord_3287558) baseStart_3287558 baseEnd_3287558 := by
    simpa [prefixWord, tailWord_3287558, baseEnd_3287558] using wordTrace_append hprefix tailTrace_3287558
  have hstable : (prefixWord ++ tailWord_3287558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287558).length < 2 ^ (prefixWord ++ tailWord_3287558).sum := by decide
  have hdescent : baseEnd_3287558 < baseStart_3287558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287584 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 5]
def baseStart_3287584 : Nat := 118140960795 + 3287584 * 2 ^ 59
def prefixEnd_3287584 : Nat := 4983230072969 + 3 ^ 40 * 3287584 * 2
def baseEnd_3287584 : Nat := 375135729784660121373485

theorem tailTrace_3287584 : CollatzResearch.WordTrace tailWord_3287584 prefixEnd_3287584 375135729784660121373485 := by
  unfold tailWord_3287584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59954019660826058745514903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79938692881101411660686537 59954019660826058745514903)
  ·
    refine ⟨89931029491239088118272355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59954019660826058745514903 89931029491239088118272355)
    ·
      refine ⟨134896544236858632177408533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89931029491239088118272355 134896544236858632177408533)
      ·
        refine ⟨6323275511102748383316025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134896544236858632177408533 6323275511102748383316025)
        ·
          refine ⟨4742456633327061287487019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6323275511102748383316025 4742456633327061287487019)
          ·
            refine ⟨7113684949990591931230529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4742456633327061287487019 7113684949990591931230529)
            ·
              refine ⟨5335263712492943948422897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7113684949990591931230529 5335263712492943948422897)
              ·
                refine ⟨4001447784369707961317173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335263712492943948422897 4001447784369707961317173)
                ·
                  refine ⟨375135729784660121373485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4001447784369707961317173 375135729784660121373485)
                  ·
                    rfl

theorem cell22_3287584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_3287584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287584 prefixEnd_3287584 := by exact prefixLift 3287584
  have htrace : WordTrace (prefixWord ++ tailWord_3287584) baseStart_3287584 baseEnd_3287584 := by
    simpa [prefixWord, tailWord_3287584, baseEnd_3287584] using wordTrace_append hprefix tailTrace_3287584
  have hstable : (prefixWord ++ tailWord_3287584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287584).length < 2 ^ (prefixWord ++ tailWord_3287584).sum := by decide
  have hdescent : baseEnd_3287584 < baseStart_3287584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287588 : List Nat := [2, 3, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_3287588 : Nat := 118140960795 + 3287588 * 2 ^ 59
def prefixEnd_3287588 : Nat := 4983230072969 + 3 ^ 40 * 3287588 * 2
def baseEnd_3287588 : Nat := 1125408558635725687020443

theorem tailTrace_3287588 : CollatzResearch.WordTrace tailWord_3287588 prefixEnd_3287588 1125408558635725687020443 := by
  unfold tailWord_3287588
  simp only [CollatzResearch.WordTrace]
  refine ⟨59954092606818813087087709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79938790142425084116116945 59954092606818813087087709)
  ·
    refine ⟨22482784727557054907657891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59954092606818813087087709 22482784727557054907657891)
    ·
      refine ⟨33724177091335582361486837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22482784727557054907657891 33724177091335582361486837)
      ·
        refine ⟨3161641602312710846389391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33724177091335582361486837 3161641602312710846389391)
        ·
          refine ⟨4742462403469066269584087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161641602312710846389391 4742462403469066269584087)
          ·
            refine ⟨7113693605203599404376131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4742462403469066269584087 7113693605203599404376131)
            ·
              refine ⟨10670540407805399106564197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113693605203599404376131 10670540407805399106564197)
              ·
                refine ⟨2000726326463512332480787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10670540407805399106564197 2000726326463512332480787)
                ·
                  refine ⟨3001089489695268498721181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000726326463512332480787 3001089489695268498721181)
                  ·
                    refine ⟨1125408558635725687020443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001089489695268498721181 1125408558635725687020443)
                    ·
                      rfl

theorem cell22_3287588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_3287588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287588 prefixEnd_3287588 := by exact prefixLift 3287588
  have htrace : WordTrace (prefixWord ++ tailWord_3287588) baseStart_3287588 baseEnd_3287588 := by
    simpa [prefixWord, tailWord_3287588, baseEnd_3287588] using wordTrace_append hprefix tailTrace_3287588
  have hstable : (prefixWord ++ tailWord_3287588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287588).length < 2 ^ (prefixWord ++ tailWord_3287588).sum := by decide
  have hdescent : baseEnd_3287588 < baseStart_3287588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287612 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 6]
def baseStart_3287612 : Nat := 118140960795 + 3287612 * 2 ^ 59
def prefixEnd_3287612 : Nat := 4983230072969 + 3 ^ 40 * 3287612 * 2
def baseEnd_3287612 : Nat := 375138924775399208140123

theorem tailTrace_3287612 : CollatzResearch.WordTrace tailWord_3287612 prefixEnd_3287612 375138924775399208140123 := by
  unfold tailWord_3287612
  simp only [CollatzResearch.WordTrace]
  refine ⟨59954530282775339136524545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79939373710367118848699393 59954530282775339136524545)
  ·
    refine ⟨44965897712081504352393409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59954530282775339136524545 44965897712081504352393409)
    ·
      refine ⟨33724423284061128264295057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44965897712081504352393409 33724423284061128264295057)
      ·
        refine ⟨25293317463045846198221293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33724423284061128264295057 25293317463045846198221293)
        ·
          refine ⟨9484994048642192324332985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25293317463045846198221293 9484994048642192324332985)
          ·
            refine ⟨7113745536481644243249739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9484994048642192324332985 7113745536481644243249739)
            ·
              refine ⟨10670618304722466364874609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113745536481644243249739 10670618304722466364874609)
              ·
                refine ⟨8002963728541849773655957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10670618304722466364874609 8002963728541849773655957)
                ·
                  refine ⟨375138924775399208140123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8002963728541849773655957 375138924775399208140123)
                  ·
                    rfl

theorem cell22_3287612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_3287612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287612 prefixEnd_3287612 := by exact prefixLift 3287612
  have htrace : WordTrace (prefixWord ++ tailWord_3287612) baseStart_3287612 baseEnd_3287612 := by
    simpa [prefixWord, tailWord_3287612, baseEnd_3287612] using wordTrace_append hprefix tailTrace_3287612
  have hstable : (prefixWord ++ tailWord_3287612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287612).length < 2 ^ (prefixWord ++ tailWord_3287612).sum := by decide
  have hdescent : baseEnd_3287612 < baseStart_3287612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287779 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 1, 5]
def baseStart_3287779 : Nat := 118140960795 + 3287779 * 2 ^ 59
def prefixEnd_3287779 : Nat := 4983230072969 + 3 ^ 40 * 3287779 * 2
def baseEnd_3287779 : Nat := 1125473941839064855494857

theorem tailTrace_3287779 : CollatzResearch.WordTrace tailWord_3287779 prefixEnd_3287779 1125473941839064855494857 := by
  unfold tailWord_3287779
  simp only [CollatzResearch.WordTrace]
  refine ⟨119915151555945665794378391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79943434370630443862918927 119915151555945665794378391)
  ·
    refine ⟨179872727333918498691567587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119915151555945665794378391 179872727333918498691567587)
    ·
      refine ⟨269809091000877748037351381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179872727333918498691567587 269809091000877748037351381)
      ·
        refine ⟨6323650570333072219625423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 269809091000877748037351381 6323650570333072219625423)
        ·
          refine ⟨9485475855499608329438135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323650570333072219625423 9485475855499608329438135)
          ·
            refine ⟨14228213783249412494157203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485475855499608329438135 14228213783249412494157203)
            ·
              refine ⟨21342320674874118741235805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14228213783249412494157203 21342320674874118741235805)
              ·
                refine ⟨8003370253077794527963427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21342320674874118741235805 8003370253077794527963427)
                ·
                  refine ⟨12005055379616691791945141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8003370253077794527963427 12005055379616691791945141)
                  ·
                    refine ⟨1125473941839064855494857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12005055379616691791945141 1125473941839064855494857)
                    ·
                      rfl

theorem cell22_3287779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_3287779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287779 prefixEnd_3287779 := by exact prefixLift 3287779
  have htrace : WordTrace (prefixWord ++ tailWord_3287779) baseStart_3287779 baseEnd_3287779 := by
    simpa [prefixWord, tailWord_3287779, baseEnd_3287779] using wordTrace_append hprefix tailTrace_3287779
  have hstable : (prefixWord ++ tailWord_3287779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287779).length < 2 ^ (prefixWord ++ tailWord_3287779).sum := by decide
  have hdescent : baseEnd_3287779 < baseStart_3287779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287794 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_3287794 : Nat := 118140960795 + 3287794 * 2 ^ 59
def prefixEnd_3287794 : Nat := 4983230072969 + 3 ^ 40 * 3287794 * 2
def baseEnd_3287794 : Nat := 1125479076645609816369811

theorem tailTrace_3287794 : CollatzResearch.WordTrace tailWord_3287794 prefixEnd_3287794 1125479076645609816369811 := by
  unfold tailWord_3287794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978924662722830839043609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79943799100594215570782957 29978924662722830839043609)
  ·
    refine ⟨22484193497042123129282707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29978924662722830839043609 22484193497042123129282707)
    ·
      refine ⟨33726290245563184693924061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22484193497042123129282707 33726290245563184693924061)
      ·
        refine ⟨12647358842086194260221523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33726290245563184693924061 12647358842086194260221523)
        ·
          refine ⟨18971038263129291390332285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12647358842086194260221523 18971038263129291390332285)
          ·
            refine ⟨7114139348673484271374607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18971038263129291390332285 7114139348673484271374607)
            ·
              refine ⟨10671209023010226407061911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7114139348673484271374607 10671209023010226407061911)
              ·
                refine ⟨16006813534515339610592867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10671209023010226407061911 16006813534515339610592867)
                ·
                  refine ⟨24010220301773009415889301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16006813534515339610592867 24010220301773009415889301)
                  ·
                    refine ⟨1125479076645609816369811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24010220301773009415889301 1125479076645609816369811)
                    ·
                      rfl

theorem cell22_3287794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_3287794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287794 prefixEnd_3287794 := by exact prefixLift 3287794
  have htrace : WordTrace (prefixWord ++ tailWord_3287794) baseStart_3287794 baseEnd_3287794 := by
    simpa [prefixWord, tailWord_3287794, baseEnd_3287794] using wordTrace_append hprefix tailTrace_3287794
  have hstable : (prefixWord ++ tailWord_3287794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287794).length < 2 ^ (prefixWord ++ tailWord_3287794).sum := by decide
  have hdescent : baseEnd_3287794 < baseStart_3287794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287916 : List Nat := [2, 2, 1, 1, 4, 1, 2, 5, 4]
def baseStart_3287916 : Nat := 118140960795 + 3287916 * 2 ^ 59
def prefixEnd_3287916 : Nat := 4983230072969 + 3 ^ 40 * 3287916 * 2
def baseEnd_3287916 : Nat := 375173613246280721606479

theorem tailTrace_3287916 : CollatzResearch.WordTrace tailWord_3287916 prefixEnd_3287916 375173613246280721606479 := by
  unfold tailWord_3287916
  simp only [CollatzResearch.WordTrace]
  refine ⟨59960074178224669096057801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79946765570966225461410401 59960074178224669096057801)
  ·
    refine ⟨44970055633668501822043351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59960074178224669096057801 44970055633668501822043351)
    ·
      refine ⟨67455083450502752733065027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44970055633668501822043351 67455083450502752733065027)
      ·
        refine ⟨101182625175754129099597541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67455083450502752733065027 101182625175754129099597541)
        ·
          refine ⟨18971742220453899206174539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101182625175754129099597541 18971742220453899206174539)
          ·
            refine ⟨28457613330680848809261809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18971742220453899206174539 28457613330680848809261809)
            ·
              refine ⟨21343209998010636606946357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28457613330680848809261809 21343209998010636606946357)
              ·
                refine ⟨2000925937313497181901221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21343209998010636606946357 2000925937313497181901221)
                ·
                  refine ⟨375173613246280721606479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000925937313497181901221 375173613246280721606479)
                  ·
                    rfl

theorem cell22_3287916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_3287916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287916 prefixEnd_3287916 := by exact prefixLift 3287916
  have htrace : WordTrace (prefixWord ++ tailWord_3287916) baseStart_3287916 baseEnd_3287916 := by
    simpa [prefixWord, tailWord_3287916, baseEnd_3287916] using wordTrace_append hprefix tailTrace_3287916
  have hstable : (prefixWord ++ tailWord_3287916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287916).length < 2 ^ (prefixWord ++ tailWord_3287916).sum := by decide
  have hdescent : baseEnd_3287916 < baseStart_3287916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287931 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 2, 3]
def baseStart_3287931 : Nat := 118140960795 + 3287931 * 2 ^ 59
def prefixEnd_3287931 : Nat := 4983230072969 + 3 ^ 40 * 3287931 * 2
def baseEnd_3287931 : Nat := 1125525974545387125694391

theorem tailTrace_3287931 : CollatzResearch.WordTrace tailWord_3287931 prefixEnd_3287931 1125525974545387125694391 := by
  unfold tailWord_3287931
  simp only [CollatzResearch.WordTrace]
  refine ⟨119920695451394995753911647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79947130300929997169274431 119920695451394995753911647)
  ·
    refine ⟨179881043177092493630867471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119920695451394995753911647 179881043177092493630867471)
    ·
      refine ⟨269821564765638740446301207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179881043177092493630867471 269821564765638740446301207)
      ·
        refine ⟨404732347148458110669451811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269821564765638740446301207 404732347148458110669451811)
        ·
          refine ⟨607098520722687166004177717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404732347148458110669451811 607098520722687166004177717)
          ·
            refine ⟨56915486317751921812891661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 607098520722687166004177717 56915486317751921812891661)
            ·
              refine ⟨21343307369156970679834373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56915486317751921812891661 21343307369156970679834373)
              ·
                refine ⟨4001870131716932002468945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21343307369156970679834373 4001870131716932002468945)
                ·
                  refine ⟨3001402598787699001851709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4001870131716932002468945 3001402598787699001851709)
                  ·
                    refine ⟨1125525974545387125694391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001402598787699001851709 1125525974545387125694391)
                    ·
                      rfl

theorem cell22_3287931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 3].length) (baseStart_3287931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287931 prefixEnd_3287931 := by exact prefixLift 3287931
  have htrace : WordTrace (prefixWord ++ tailWord_3287931) baseStart_3287931 baseEnd_3287931 := by
    simpa [prefixWord, tailWord_3287931, baseEnd_3287931] using wordTrace_append hprefix tailTrace_3287931
  have hstable : (prefixWord ++ tailWord_3287931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287931).length < 2 ^ (prefixWord ++ tailWord_3287931).sum := by decide
  have hdescent : baseEnd_3287931 < baseStart_3287931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287933 : List Nat := [1, 4, 1, 1, 2, 1, 6, 2, 4]
def baseStart_3287933 : Nat := 118140960795 + 3287933 * 2 ^ 59
def prefixEnd_3287933 : Nat := 4983230072969 + 3 ^ 40 * 3287933 * 2
def baseEnd_3287933 : Nat := 375175553062086595714795

theorem tailTrace_3287933 : CollatzResearch.WordTrace tailWord_3287933 prefixEnd_3287933 375175553062086595714795 := by
  unfold tailWord_3287933
  simp only [CollatzResearch.WordTrace]
  refine ⟨119920768397387750095484453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79947178931591833396989635 119920768397387750095484453)
  ·
    refine ⟨22485144074510203142903335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119920768397387750095484453 22485144074510203142903335)
    ·
      refine ⟨33727716111765304714355003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22485144074510203142903335 33727716111765304714355003)
      ·
        refine ⟨50591574167647957071532505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33727716111765304714355003 50591574167647957071532505)
        ·
          refine ⟨37943680625735967803649379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50591574167647957071532505 37943680625735967803649379)
          ·
            refine ⟨56915520938603951705474069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37943680625735967803649379 56915520938603951705474069)
            ·
              refine ⟨2667915043997060236194097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56915520938603951705474069 2667915043997060236194097)
              ·
                refine ⟨2000936282997795177145573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667915043997060236194097 2000936282997795177145573)
                ·
                  refine ⟨375175553062086595714795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000936282997795177145573 375175553062086595714795)
                  ·
                    rfl

theorem cell22_3287933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_3287933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287933 prefixEnd_3287933 := by exact prefixLift 3287933
  have htrace : WordTrace (prefixWord ++ tailWord_3287933) baseStart_3287933 baseEnd_3287933 := by
    simpa [prefixWord, tailWord_3287933, baseEnd_3287933] using wordTrace_append hprefix tailTrace_3287933
  have hstable : (prefixWord ++ tailWord_3287933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287933).length < 2 ^ (prefixWord ++ tailWord_3287933).sum := by decide
  have hdescent : baseEnd_3287933 < baseStart_3287933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3287993 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 3, 3]
def baseStart_3287993 : Nat := 118140960795 + 3287993 * 2 ^ 59
def prefixEnd_3287993 : Nat := 4983230072969 + 3 ^ 40 * 3287993 * 2
def baseEnd_3287993 : Nat := 1125547198412439630644201

theorem tailTrace_3287993 : CollatzResearch.WordTrace tailWord_3287993 prefixEnd_3287993 1125547198412439630644201 := by
  unfold tailWord_3287993
  simp only [CollatzResearch.WordTrace]
  refine ⟨119922956777170380342668633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79948637851446920228445755 119922956777170380342668633)
  ·
    refine ⟨89942217582877785257001475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119922956777170380342668633 89942217582877785257001475)
    ·
      refine ⟨134913326374316677885502213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89942217582877785257001475 134913326374316677885502213)
      ·
        refine ⟨25296248695184377103531665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134913326374316677885502213 25296248695184377103531665)
        ·
          refine ⟨18972186521388282827648749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25296248695184377103531665 18972186521388282827648749)
          ·
            refine ⟨7114569945520606060368281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18972186521388282827648749 7114569945520606060368281)
            ·
              refine ⟨5335927459140454545276211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7114569945520606060368281 5335927459140454545276211)
              ·
                refine ⟨8003891188710681817914317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335927459140454545276211 8003891188710681817914317)
                ·
                  refine ⟨3001459195766505681717869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8003891188710681817914317 3001459195766505681717869)
                  ·
                    refine ⟨1125547198412439630644201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001459195766505681717869 1125547198412439630644201)
                    ·
                      rfl

theorem cell22_3287993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_3287993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3287993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3287993 prefixEnd_3287993 := by exact prefixLift 3287993
  have htrace : WordTrace (prefixWord ++ tailWord_3287993) baseStart_3287993 baseEnd_3287993 := by
    simpa [prefixWord, tailWord_3287993, baseEnd_3287993] using wordTrace_append hprefix tailTrace_3287993
  have hstable : (prefixWord ++ tailWord_3287993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3287993).length < 2 ^ (prefixWord ++ tailWord_3287993).sum := by decide
  have hdescent : baseEnd_3287993 < baseStart_3287993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3287993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288096 : List Nat := [2, 1, 1, 7, 11]
def baseStart_3288096 : Nat := 118140960795 + 3288096 * 2 ^ 59
def prefixEnd_3288096 : Nat := 4983230072969 + 3 ^ 40 * 3288096 * 2
def baseEnd_3288096 : Nat := 4632026573734081050695

theorem tailTrace_3288096 : CollatzResearch.WordTrace tailWord_3288096 prefixEnd_3288096 4632026573734081050695 := by
  unfold tailWord_3288096
  simp only [CollatzResearch.WordTrace]
  refine ⟨59963356747898614466834071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79951142330531485955778761 59963356747898614466834071)
  ·
    refine ⟨89945035121847921700251107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59963356747898614466834071 89945035121847921700251107)
    ·
      refine ⟨134917552682771882550376661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89945035121847921700251107 134917552682771882550376661)
      ·
        refine ⟨3162130141002465997274453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 134917552682771882550376661 3162130141002465997274453)
        ·
          refine ⟨4632026573734081050695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3162130141002465997274453 4632026573734081050695)
          ·
            rfl

theorem cell22_3288096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 11].length) (baseStart_3288096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288096 prefixEnd_3288096 := by exact prefixLift 3288096
  have htrace : WordTrace (prefixWord ++ tailWord_3288096) baseStart_3288096 baseEnd_3288096 := by
    simpa [prefixWord, tailWord_3288096, baseEnd_3288096] using wordTrace_append hprefix tailTrace_3288096
  have hstable : (prefixWord ++ tailWord_3288096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288096).length < 2 ^ (prefixWord ++ tailWord_3288096).sum := by decide
  have hdescent : baseEnd_3288096 < baseStart_3288096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288098 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3288098 : Nat := 118140960795 + 3288098 * 2 ^ 59
def prefixEnd_3288098 : Nat := 4983230072969 + 3 ^ 40 * 3288098 * 2
def baseEnd_3288098 : Nat := 1125583142058254356768879

theorem tailTrace_3288098 : CollatzResearch.WordTrace tailWord_3288098 prefixEnd_3288098 1125583142058254356768879 := by
  unfold tailWord_3288098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29981696610447495818810237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79951190961193322183493965 29981696610447495818810237)
  ·
    refine ⟨11243136228917810932053839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29981696610447495818810237 11243136228917810932053839)
    ·
      refine ⟨16864704343376716398080759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11243136228917810932053839 16864704343376716398080759)
      ·
        refine ⟨25297056515065074597121139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16864704343376716398080759 25297056515065074597121139)
        ·
          refine ⟨37945584772597611895681709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25297056515065074597121139 37945584772597611895681709)
          ·
            refine ⟨14229594289724104460880641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37945584772597611895681709 14229594289724104460880641)
            ·
              refine ⟨10672195717293078345660481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14229594289724104460880641 10672195717293078345660481)
              ·
                refine ⟨8004146787969808759245361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10672195717293078345660481 8004146787969808759245361)
                ·
                  refine ⟨6003110090977356569434021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8004146787969808759245361 6003110090977356569434021)
                  ·
                    refine ⟨1125583142058254356768879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6003110090977356569434021 1125583142058254356768879)
                    ·
                      rfl

theorem cell22_3288098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3288098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288098 prefixEnd_3288098 := by exact prefixLift 3288098
  have htrace : WordTrace (prefixWord ++ tailWord_3288098) baseStart_3288098 baseEnd_3288098 := by
    simpa [prefixWord, tailWord_3288098, baseEnd_3288098] using wordTrace_append hprefix tailTrace_3288098
  have hstable : (prefixWord ++ tailWord_3288098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288098).length < 2 ^ (prefixWord ++ tailWord_3288098).sum := by decide
  have hdescent : baseEnd_3288098 < baseStart_3288098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288100 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_3288100 : Nat := 118140960795 + 3288100 * 2 ^ 59
def prefixEnd_3288100 : Nat := 4983230072969 + 3 ^ 40 * 3288100 * 2
def baseEnd_3288100 : Nat := 1125583826699127018218873

theorem tailTrace_3288100 : CollatzResearch.WordTrace tailWord_3288100 prefixEnd_3288100 1125583826699127018218873 := by
  unfold tailWord_3288100
  simp only [CollatzResearch.WordTrace]
  refine ⟨59963429693891368808406877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79951239591855158411209169 59963429693891368808406877)
  ·
    refine ⟨22486286135209263303152579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59963429693891368808406877 22486286135209263303152579)
    ·
      refine ⟨33729429202813894954728869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22486286135209263303152579 33729429202813894954728869)
      ·
        refine ⟨6324267975527605304011663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33729429202813894954728869 6324267975527605304011663)
        ·
          refine ⟨9486401963291407956017495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324267975527605304011663 9486401963291407956017495)
          ·
            refine ⟨14229602944937111934026243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486401963291407956017495 14229602944937111934026243)
            ·
              refine ⟨21344404417405667901039365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14229602944937111934026243 21344404417405667901039365)
              ·
                refine ⟨4002075828263562731444881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21344404417405667901039365 4002075828263562731444881)
                ·
                  refine ⟨3001556871197672048583661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4002075828263562731444881 3001556871197672048583661)
                  ·
                    refine ⟨1125583826699127018218873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001556871197672048583661 1125583826699127018218873)
                    ·
                      rfl

theorem cell22_3288100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_3288100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288100 prefixEnd_3288100 := by exact prefixLift 3288100
  have htrace : WordTrace (prefixWord ++ tailWord_3288100) baseStart_3288100 baseEnd_3288100 := by
    simpa [prefixWord, tailWord_3288100, baseEnd_3288100] using wordTrace_append hprefix tailTrace_3288100
  have hstable : (prefixWord ++ tailWord_3288100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288100).length < 2 ^ (prefixWord ++ tailWord_3288100).sum := by decide
  have hdescent : baseEnd_3288100 < baseStart_3288100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288128 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 3, 3]
def baseStart_3288128 : Nat := 118140960795 + 3288128 * 2 ^ 59
def prefixEnd_3288128 : Nat := 4983230072969 + 3 ^ 40 * 3288128 * 2
def baseEnd_3288128 : Nat := 1125593411671344278518787

theorem tailTrace_3288128 : CollatzResearch.WordTrace tailWord_3288128 prefixEnd_3288128 1125593411671344278518787 := by
  unfold tailWord_3288128
  simp only [CollatzResearch.WordTrace]
  refine ⟨59963940315840649199416519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79951920421120865599222025 59963940315840649199416519)
  ·
    refine ⟨89945910473760973799124779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59963940315840649199416519 89945910473760973799124779)
    ·
      refine ⟨134918865710641460698687169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89945910473760973799124779 134918865710641460698687169)
      ·
        refine ⟨101189149282981095524015377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134918865710641460698687169 101189149282981095524015377)
        ·
          refine ⟨75891861962235821643011533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101189149282981095524015377 75891861962235821643011533)
          ·
            refine ⟨28459448235838433116129325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75891861962235821643011533 28459448235838433116129325)
            ·
              refine ⟨10672293088439412418548497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28459448235838433116129325 10672293088439412418548497)
              ·
                refine ⟨8004219816329559313911373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10672293088439412418548497 8004219816329559313911373)
                ·
                  refine ⟨3001582431123584742716765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8004219816329559313911373 3001582431123584742716765)
                  ·
                    refine ⟨1125593411671344278518787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001582431123584742716765 1125593411671344278518787)
                    ·
                      rfl

theorem cell22_3288128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_3288128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288128 prefixEnd_3288128 := by exact prefixLift 3288128
  have htrace : WordTrace (prefixWord ++ tailWord_3288128) baseStart_3288128 baseEnd_3288128 := by
    simpa [prefixWord, tailWord_3288128, baseEnd_3288128] using wordTrace_append hprefix tailTrace_3288128
  have hstable : (prefixWord ++ tailWord_3288128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288128).length < 2 ^ (prefixWord ++ tailWord_3288128).sum := by decide
  have hdescent : baseEnd_3288128 < baseStart_3288128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288145 : List Nat := [1, 2, 2, 1, 3, 1, 3, 5, 1, 3]
def baseStart_3288145 : Nat := 118140960795 + 3288145 * 2 ^ 59
def prefixEnd_3288145 : Nat := 4983230072969 + 3 ^ 40 * 3288145 * 2
def baseEnd_3288145 : Nat := 1125599231118761900843735

theorem tailTrace_3288145 : CollatzResearch.WordTrace tailWord_3288145 prefixEnd_3288145 1125599231118761900843735 := by
  unfold tailWord_3288145
  simp only [CollatzResearch.WordTrace]
  refine ⟨119928500672619710302201889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79952333781746473534801259 119928500672619710302201889)
  ·
    refine ⟨89946375504464782726651417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119928500672619710302201889 89946375504464782726651417)
    ·
      refine ⟨67459781628348587044988563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89946375504464782726651417 67459781628348587044988563)
      ·
        refine ⟨101189672442522880567482845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67459781628348587044988563 101189672442522880567482845)
        ·
          refine ⟨37946127165946080212806067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101189672442522880567482845 37946127165946080212806067)
          ·
            refine ⟨56919190748919120319209101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37946127165946080212806067 56919190748919120319209101)
            ·
              refine ⟨21344696530844670119703413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56919190748919120319209101 21344696530844670119703413)
              ·
                refine ⟨2001065299766687823722195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21344696530844670119703413 2001065299766687823722195)
                ·
                  refine ⟨3001597949650031735583293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001065299766687823722195 3001597949650031735583293)
                  ·
                    refine ⟨1125599231118761900843735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001597949650031735583293 1125599231118761900843735)
                    ·
                      rfl

theorem cell22_3288145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_3288145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288145 prefixEnd_3288145 := by exact prefixLift 3288145
  have htrace : WordTrace (prefixWord ++ tailWord_3288145) baseStart_3288145 baseEnd_3288145 := by
    simpa [prefixWord, tailWord_3288145, baseEnd_3288145] using wordTrace_append hprefix tailTrace_3288145
  have hstable : (prefixWord ++ tailWord_3288145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288145).length < 2 ^ (prefixWord ++ tailWord_3288145).sum := by decide
  have hdescent : baseEnd_3288145 < baseStart_3288145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288162 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3288162 : Nat := 118140960795 + 3288162 * 2 ^ 59
def prefixEnd_3288162 : Nat := 4983230072969 + 3 ^ 40 * 3288162 * 2
def baseEnd_3288162 : Nat := 1125605050566179523168683

theorem tailTrace_3288162 : CollatzResearch.WordTrace tailWord_3288162 prefixEnd_3288162 1125605050566179523168683 := by
  unfold tailWord_3288162
  simp only [CollatzResearch.WordTrace]
  refine ⟨29982280178389530551392685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79952747142372081470380493 29982280178389530551392685)
  ·
    refine ⟨11243355066896073956772257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29982280178389530551392685 11243355066896073956772257)
    ·
      refine ⟨8432516300172055467579193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11243355066896073956772257 8432516300172055467579193)
      ·
        refine ⟨6324387225129041600684395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8432516300172055467579193 6324387225129041600684395)
        ·
          refine ⟨9486580837693562401026593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324387225129041600684395 9486580837693562401026593)
          ·
            refine ⟨7114935628270171800769945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9486580837693562401026593 7114935628270171800769945)
            ·
              refine ⟨5336201721202628850577459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7114935628270171800769945 5336201721202628850577459)
              ·
                refine ⟨8004302581803943275866189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5336201721202628850577459 8004302581803943275866189)
                ·
                  refine ⟨3001613468176478728449821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8004302581803943275866189 3001613468176478728449821)
                  ·
                    refine ⟨1125605050566179523168683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001613468176478728449821 1125605050566179523168683)
                    ·
                      rfl

theorem cell22_3288162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3288162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288162 prefixEnd_3288162 := by exact prefixLift 3288162
  have htrace : WordTrace (prefixWord ++ tailWord_3288162) baseStart_3288162 baseEnd_3288162 := by
    simpa [prefixWord, tailWord_3288162, baseEnd_3288162] using wordTrace_append hprefix tailTrace_3288162
  have hstable : (prefixWord ++ tailWord_3288162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288162).length < 2 ^ (prefixWord ++ tailWord_3288162).sum := by decide
  have hdescent : baseEnd_3288162 < baseStart_3288162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288173 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3288173 : Nat := 118140960795 + 3288173 * 2 ^ 59
def prefixEnd_3288173 : Nat := 4983230072969 + 3 ^ 40 * 3288173 * 2
def baseEnd_3288173 : Nat := 1125608816090979161143649

theorem tailTrace_3288173 : CollatzResearch.WordTrace tailWord_3288173 prefixEnd_3288173 1125608816090979161143649 := by
  unfold tailWord_3288173
  simp only [CollatzResearch.WordTrace]
  refine ⟨119929521916518271084221173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79953014611012180722814115 119929521916518271084221173)
  ·
    refine ⟨11243392679673587914145735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119929521916518271084221173 11243392679673587914145735)
    ·
      refine ⟨16865089019510381871218603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11243392679673587914145735 16865089019510381871218603)
      ·
        refine ⟨25297633529265572806827905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16865089019510381871218603 25297633529265572806827905)
        ·
          refine ⟨18973225146949179605120929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25297633529265572806827905 18973225146949179605120929)
          ·
            refine ⟨14229918860211884703840697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18973225146949179605120929 14229918860211884703840697)
            ·
              refine ⟨10672439145158913527880523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14229918860211884703840697 10672439145158913527880523)
              ·
                refine ⟨16008658717738370291820785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10672439145158913527880523 16008658717738370291820785)
                ·
                  refine ⟨12006494038303777718865589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16008658717738370291820785 12006494038303777718865589)
                  ·
                    refine ⟨1125608816090979161143649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12006494038303777718865589 1125608816090979161143649)
                    ·
                      rfl

theorem cell22_3288173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3288173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288173 prefixEnd_3288173 := by exact prefixLift 3288173
  have htrace : WordTrace (prefixWord ++ tailWord_3288173) baseStart_3288173 baseEnd_3288173 := by
    simpa [prefixWord, tailWord_3288173, baseEnd_3288173] using wordTrace_append hprefix tailTrace_3288173
  have hstable : (prefixWord ++ tailWord_3288173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288173).length < 2 ^ (prefixWord ++ tailWord_3288173).sum := by decide
  have hdescent : baseEnd_3288173 < baseStart_3288173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288220 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 6]
def baseStart_3288220 : Nat := 118140960795 + 3288220 * 2 ^ 59
def prefixEnd_3288220 : Nat := 4983230072969 + 3 ^ 40 * 3288220 * 2
def baseEnd_3288220 : Nat := 375208301717162235072835

theorem tailTrace_3288220 : CollatzResearch.WordTrace tailWord_3288220 prefixEnd_3288220 375208301717162235072835 := by
  unfold tailWord_3288220
  simp only [CollatzResearch.WordTrace]
  refine ⟨59965618073673999055591057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79954157431565332074121409 59965618073673999055591057)
  ·
    refine ⟨44974213555255499291693293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59965618073673999055591057 44974213555255499291693293)
    ·
      refine ⟨16865330083220812234384985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44974213555255499291693293 16865330083220812234384985)
      ·
        refine ⟨12648997562415609175788739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16865330083220812234384985 12648997562415609175788739)
        ·
          refine ⟨18973496343623413763683109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12648997562415609175788739 18973496343623413763683109)
          ·
            refine ⟨3557530564429390080690583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18973496343623413763683109 3557530564429390080690583)
            ·
              refine ⟨5336295846644085121035875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557530564429390080690583 5336295846644085121035875)
              ·
                refine ⟨8004443769966127681553813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5336295846644085121035875 8004443769966127681553813)
                ·
                  refine ⟨375208301717162235072835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8004443769966127681553813 375208301717162235072835)
                  ·
                    rfl

theorem cell22_3288220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_3288220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288220 prefixEnd_3288220 := by exact prefixLift 3288220
  have htrace : WordTrace (prefixWord ++ tailWord_3288220) baseStart_3288220 baseEnd_3288220 := by
    simpa [prefixWord, tailWord_3288220, baseEnd_3288220] using wordTrace_append hprefix tailTrace_3288220
  have hstable : (prefixWord ++ tailWord_3288220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288220).length < 2 ^ (prefixWord ++ tailWord_3288220).sum := by decide
  have hdescent : baseEnd_3288220 < baseStart_3288220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288357 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_3288357 : Nat := 118140960795 + 3288357 * 2 ^ 59
def prefixEnd_3288357 : Nat := 4983230072969 + 3 ^ 40 * 3288357 * 2
def baseEnd_3288357 : Nat := 1125671803051264014543085

theorem tailTrace_3288357 : CollatzResearch.WordTrace tailWord_3288357 prefixEnd_3288357 1125671803051264014543085 := by
  unfold tailWord_3288357
  simp only [CollatzResearch.WordTrace]
  refine ⟨119936232947851670508919325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79957488631901113672612883 119936232947851670508919325)
  ·
    refine ⟨44976087355444376440844747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119936232947851670508919325 44976087355444376440844747)
    ·
      refine ⟨67464131033166564661267121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44976087355444376440844747 67464131033166564661267121)
      ·
        refine ⟨50598098274874923495950341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67464131033166564661267121 50598098274874923495950341)
        ·
          refine ⟨9487143426539048155490689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50598098274874923495950341 9487143426539048155490689)
          ·
            refine ⟨7115357569904286116618017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9487143426539048155490689 7115357569904286116618017)
            ·
              refine ⟨5336518177428214587463513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7115357569904286116618017 5336518177428214587463513)
              ·
                refine ⟨4002388633071160940597635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5336518177428214587463513 4002388633071160940597635)
                ·
                  refine ⟨6003582949606741410896453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002388633071160940597635 6003582949606741410896453)
                  ·
                    refine ⟨1125671803051264014543085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6003582949606741410896453 1125671803051264014543085)
                    ·
                      rfl

theorem cell22_3288357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_3288357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288357 prefixEnd_3288357 := by exact prefixLift 3288357
  have htrace : WordTrace (prefixWord ++ tailWord_3288357) baseStart_3288357 baseEnd_3288357 := by
    simpa [prefixWord, tailWord_3288357, baseEnd_3288357] using wordTrace_append hprefix tailTrace_3288357
  have hstable : (prefixWord ++ tailWord_3288357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288357).length < 2 ^ (prefixWord ++ tailWord_3288357).sum := by decide
  have hdescent : baseEnd_3288357 < baseStart_3288357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288368 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_3288368 : Nat := 118140960795 + 3288368 * 2 ^ 59
def prefixEnd_3288368 : Nat := 4983230072969 + 3 ^ 40 * 3288368 * 2
def baseEnd_3288368 : Nat := 1125675568576063652518051

theorem tailTrace_3288368 : CollatzResearch.WordTrace tailWord_3288368 prefixEnd_3288368 1125675568576063652518051 := by
  unfold tailWord_3288368
  simp only [CollatzResearch.WordTrace]
  refine ⟨59968317075405909693784879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79957756100541212925046505 59968317075405909693784879)
  ·
    refine ⟨89952475613108864540677319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59968317075405909693784879 89952475613108864540677319)
    ·
      refine ⟨134928713419663296811015979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89952475613108864540677319 134928713419663296811015979)
      ·
        refine ⟨202393070129494945216523969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134928713419663296811015979 202393070129494945216523969)
        ·
          refine ⟨151794802597121208912392977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202393070129494945216523969 151794802597121208912392977)
          ·
            refine ⟨113846101947840906684294733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151794802597121208912392977 113846101947840906684294733)
            ·
              refine ⟨42692288230440340006610525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113846101947840906684294733 42692288230440340006610525)
              ·
                refine ⟨16009608086415127502478947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42692288230440340006610525 16009608086415127502478947)
                ·
                  refine ⟨24014412129622691253718421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16009608086415127502478947 24014412129622691253718421)
                  ·
                    refine ⟨1125675568576063652518051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24014412129622691253718421 1125675568576063652518051)
                    ·
                      rfl

theorem cell22_3288368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_3288368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288368 prefixEnd_3288368 := by exact prefixLift 3288368
  have htrace : WordTrace (prefixWord ++ tailWord_3288368) baseStart_3288368 baseEnd_3288368 := by
    simpa [prefixWord, tailWord_3288368, baseEnd_3288368] using wordTrace_append hprefix tailTrace_3288368
  have hstable : (prefixWord ++ tailWord_3288368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288368).length < 2 ^ (prefixWord ++ tailWord_3288368).sum := by decide
  have hdescent : baseEnd_3288368 < baseStart_3288368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288383 : List Nat := [1, 1, 2, 2, 4, 2, 10]
def baseStart_3288383 : Nat := 118140960795 + 3288383 * 2 ^ 59
def prefixEnd_3288383 : Nat := 4983230072969 + 3 ^ 40 * 3288383 * 2
def baseEnd_3288383 : Nat := 41691877903059578273815

theorem tailTrace_3288383 : CollatzResearch.WordTrace tailWord_3288383 prefixEnd_3288383 41691877903059578273815 := by
  unfold tailWord_3288383
  simp only [CollatzResearch.WordTrace]
  refine ⟨119937181245757476949365803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79958120830504984632910535 119937181245757476949365803)
  ·
    refine ⟨179905771868636215424048705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119937181245757476949365803 179905771868636215424048705)
    ·
      refine ⟨134929328901477161568036529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179905771868636215424048705 134929328901477161568036529)
      ·
        refine ⟨101196996676107871176027397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134929328901477161568036529 101196996676107871176027397)
        ·
          refine ⟨18974436876770225845505137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101196996676107871176027397 18974436876770225845505137)
          ·
            refine ⟨14230827657577669384128853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18974436876770225845505137 14230827657577669384128853)
            ·
              refine ⟨41691877903059578273815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14230827657577669384128853 41691877903059578273815)
              ·
                rfl

theorem cell22_3288383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 10].length) (baseStart_3288383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288383 prefixEnd_3288383 := by exact prefixLift 3288383
  have htrace : WordTrace (prefixWord ++ tailWord_3288383) baseStart_3288383 baseEnd_3288383 := by
    simpa [prefixWord, tailWord_3288383, baseEnd_3288383] using wordTrace_append hprefix tailTrace_3288383
  have hstable : (prefixWord ++ tailWord_3288383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288383).length < 2 ^ (prefixWord ++ tailWord_3288383).sum := by decide
  have hdescent : baseEnd_3288383 < baseStart_3288383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288415 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 5, 3]
def baseStart_3288415 : Nat := 118140960795 + 3288415 * 2 ^ 59
def prefixEnd_3288415 : Nat := 4983230072969 + 3 ^ 40 * 3288415 * 2
def baseEnd_3288415 : Nat := 1125691657636571196592907

theorem tailTrace_3288415 : CollatzResearch.WordTrace tailWord_3288415 prefixEnd_3288415 1125691657636571196592907 := by
  unfold tailWord_3288415
  simp only [CollatzResearch.WordTrace]
  refine ⟨119938348381641546414530699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79958898921094364276353799 119938348381641546414530699)
  ·
    refine ⟨179907522572462319621796049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119938348381641546414530699 179907522572462319621796049)
    ·
      refine ⟨134930641929346739716347037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179907522572462319621796049 134930641929346739716347037)
      ·
        refine ⟨50598990723505027393630139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134930641929346739716347037 50598990723505027393630139)
        ·
          refine ⟨75898486085257541090445209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50598990723505027393630139 75898486085257541090445209)
          ·
            refine ⟨56923864563943155817833907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75898486085257541090445209 56923864563943155817833907)
            ·
              refine ⟨85385796845914733726750861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56923864563943155817833907 85385796845914733726750861)
              ·
                refine ⟨32019673817218025147531573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85385796845914733726750861 32019673817218025147531573)
                ·
                  refine ⟨3001844420364189857581085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32019673817218025147531573 3001844420364189857581085)
                  ·
                    refine ⟨1125691657636571196592907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001844420364189857581085 1125691657636571196592907)
                    ·
                      rfl

theorem cell22_3288415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_3288415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288415 prefixEnd_3288415 := by exact prefixLift 3288415
  have htrace : WordTrace (prefixWord ++ tailWord_3288415) baseStart_3288415 baseEnd_3288415 := by
    simpa [prefixWord, tailWord_3288415, baseEnd_3288415] using wordTrace_append hprefix tailTrace_3288415
  have hstable : (prefixWord ++ tailWord_3288415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288415).length < 2 ^ (prefixWord ++ tailWord_3288415).sum := by decide
  have hdescent : baseEnd_3288415 < baseStart_3288415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288460 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_3288460 : Nat := 118140960795 + 3288460 * 2 ^ 59
def prefixEnd_3288460 : Nat := 4983230072969 + 3 ^ 40 * 3288460 * 2
def baseEnd_3288460 : Nat := 1125707062056206079217769

theorem tailTrace_3288460 : CollatzResearch.WordTrace tailWord_3288460 prefixEnd_3288460 1125707062056206079217769 := by
  unfold tailWord_3288460
  simp only [CollatzResearch.WordTrace]
  refine ⟨59969994833239259549959417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79959993110985679399945889 59969994833239259549959417)
  ·
    refine ⟨44977496124929444662469563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59969994833239259549959417 44977496124929444662469563)
    ·
      refine ⟨67466244187394166993704345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44977496124929444662469563 67466244187394166993704345)
      ·
        refine ⟨50599683140545625245278259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67466244187394166993704345 50599683140545625245278259)
        ·
          refine ⟨75899524710818437867917389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50599683140545625245278259 75899524710818437867917389)
          ·
            refine ⟨28462321766556914200469021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75899524710818437867917389 28462321766556914200469021)
            ·
              refine ⟨10673370662458842825175883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28462321766556914200469021 10673370662458842825175883)
              ·
                refine ⟨16010055993688264237763825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10673370662458842825175883 16010055993688264237763825)
                ·
                  refine ⟨12007541995266198178322869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16010055993688264237763825 12007541995266198178322869)
                  ·
                    refine ⟨1125707062056206079217769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12007541995266198178322869 1125707062056206079217769)
                    ·
                      rfl

theorem cell22_3288460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_3288460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288460 prefixEnd_3288460 := by exact prefixLift 3288460
  have htrace : WordTrace (prefixWord ++ tailWord_3288460) baseStart_3288460 baseEnd_3288460 := by
    simpa [prefixWord, tailWord_3288460, baseEnd_3288460] using wordTrace_append hprefix tailTrace_3288460
  have hstable : (prefixWord ++ tailWord_3288460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288460).length < 2 ^ (prefixWord ++ tailWord_3288460).sum := by decide
  have hdescent : baseEnd_3288460 < baseStart_3288460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288466 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3288466 : Nat := 118140960795 + 3288466 * 2 ^ 59
def prefixEnd_3288466 : Nat := 4983230072969 + 3 ^ 40 * 3288466 * 2
def baseEnd_3288466 : Nat := 1125709115978824063567751

theorem tailTrace_3288466 : CollatzResearch.WordTrace tailWord_3288466 prefixEnd_3288466 1125709115978824063567751 := by
  unfold tailWord_3288466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29985052126114195531159313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79960139002971188083091501 29985052126114195531159313)
  ·
    refine ⟨22488789094585646648369485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29985052126114195531159313 22488789094585646648369485)
    ·
      refine ⟨8433295910469617493138557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22488789094585646648369485 8433295910469617493138557)
      ·
        refine ⟨3162485966426106559926959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8433295910469617493138557 3162485966426106559926959)
        ·
          refine ⟨4743728949639159839890439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162485966426106559926959 4743728949639159839890439)
          ·
            refine ⟨7115593424458739759835659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743728949639159839890439 7115593424458739759835659)
            ·
              refine ⟨10673390136688109639753489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115593424458739759835659 10673390136688109639753489)
              ·
                refine ⟨8005042602516082229815117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10673390136688109639753489 8005042602516082229815117)
                ·
                  refine ⟨3001890975943530836180669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8005042602516082229815117 3001890975943530836180669)
                  ·
                    refine ⟨1125709115978824063567751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001890975943530836180669 1125709115978824063567751)
                    ·
                      rfl

theorem cell22_3288466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3288466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288466 prefixEnd_3288466 := by exact prefixLift 3288466
  have htrace : WordTrace (prefixWord ++ tailWord_3288466) baseStart_3288466 baseEnd_3288466 := by
    simpa [prefixWord, tailWord_3288466, baseEnd_3288466] using wordTrace_append hprefix tailTrace_3288466
  have hstable : (prefixWord ++ tailWord_3288466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288466).length < 2 ^ (prefixWord ++ tailWord_3288466).sum := by decide
  have hdescent : baseEnd_3288466 < baseStart_3288466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288520 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3288520 : Nat := 118140960795 + 3288520 * 2 ^ 59
def prefixEnd_3288520 : Nat := 4983230072969 + 3 ^ 40 * 3288520 * 2
def baseEnd_3288520 : Nat := 1125727601282385922717585

theorem tailTrace_3288520 : CollatzResearch.WordTrace tailWord_3288520 prefixEnd_3288520 1125727601282385922717585 := by
  unfold tailWord_3288520
  simp only [CollatzResearch.WordTrace]
  refine ⟨59971089023130574673551507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79961452030840766231402009 59971089023130574673551507)
  ·
    refine ⟨89956633534695862010327261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59971089023130574673551507 89956633534695862010327261)
    ·
      refine ⟨33733737575510948253872723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89956633534695862010327261 33733737575510948253872723)
      ·
        refine ⟨50600606363266422380809085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33733737575510948253872723 50600606363266422380809085)
        ·
          refine ⟨18975227386224908392803407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50600606363266422380809085 18975227386224908392803407)
          ·
            refine ⟨28462841079337362589205111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18975227386224908392803407 28462841079337362589205111)
            ·
              refine ⟨42694261619006043883807667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28462841079337362589205111 42694261619006043883807667)
              ·
                refine ⟨64041392428509065825711501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42694261619006043883807667 64041392428509065825711501)
                ·
                  refine ⟨24015522160690899684641813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64041392428509065825711501 24015522160690899684641813)
                  ·
                    refine ⟨1125727601282385922717585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24015522160690899684641813 1125727601282385922717585)
                    ·
                      rfl

theorem cell22_3288520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3288520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288520 prefixEnd_3288520 := by exact prefixLift 3288520
  have htrace : WordTrace (prefixWord ++ tailWord_3288520) baseStart_3288520 baseEnd_3288520 := by
    simpa [prefixWord, tailWord_3288520, baseEnd_3288520] using wordTrace_append hprefix tailTrace_3288520
  have hstable : (prefixWord ++ tailWord_3288520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288520).length < 2 ^ (prefixWord ++ tailWord_3288520).sum := by decide
  have hdescent : baseEnd_3288520 < baseStart_3288520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288522 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_3288522 : Nat := 118140960795 + 3288522 * 2 ^ 59
def prefixEnd_3288522 : Nat := 4983230072969 + 3 ^ 40 * 3288522 * 2
def baseEnd_3288522 : Nat := 1125728285923258584167579

theorem tailTrace_3288522 : CollatzResearch.WordTrace tailWord_3288522 prefixEnd_3288522 1125728285923258584167579 := by
  unfold tailWord_3288522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29985562748063475922168955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79961500661502602459117213 29985562748063475922168955)
  ·
    refine ⟨44978344122095213883253433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29985562748063475922168955 44978344122095213883253433)
    ·
      refine ⟨33733758091571410412440075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44978344122095213883253433 33733758091571410412440075)
      ·
        refine ⟨50600637137357115618660113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33733758091571410412440075 50600637137357115618660113)
        ·
          refine ⟨37950477853017836713995085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50600637137357115618660113 37950477853017836713995085)
          ·
            refine ⟨14231429194881688767748157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37950477853017836713995085 14231429194881688767748157)
            ·
              refine ⟨5336785948080633287905559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14231429194881688767748157 5336785948080633287905559)
              ·
                refine ⟨8005178922120949931858339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5336785948080633287905559 8005178922120949931858339)
                ·
                  refine ⟨12007768383181424897787509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8005178922120949931858339 12007768383181424897787509)
                  ·
                    refine ⟨1125728285923258584167579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12007768383181424897787509 1125728285923258584167579)
                    ·
                      rfl

theorem cell22_3288522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_3288522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288522 prefixEnd_3288522 := by exact prefixLift 3288522
  have htrace : WordTrace (prefixWord ++ tailWord_3288522) baseStart_3288522 baseEnd_3288522 := by
    simpa [prefixWord, tailWord_3288522, baseEnd_3288522] using wordTrace_append hprefix tailTrace_3288522
  have hstable : (prefixWord ++ tailWord_3288522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288522).length < 2 ^ (prefixWord ++ tailWord_3288522).sum := by decide
  have hdescent : baseEnd_3288522 < baseStart_3288522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288541 : List Nat := [1, 4, 3, 1, 1, 4, 1, 3, 4]
def baseStart_3288541 : Nat := 118140960795 + 3288541 * 2 ^ 59
def prefixEnd_3288541 : Nat := 4983230072969 + 3 ^ 40 * 3288541 * 2
def baseEnd_3288541 : Nat := 375244930003849622647507

theorem tailTrace_3288541 : CollatzResearch.WordTrace tailWord_3288541 prefixEnd_3288541 375244930003849622647507 := by
  unfold tailWord_3288541
  simp only [CollatzResearch.WordTrace]
  refine ⟨119942943979185069933617477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79961962652790046622411651 119942943979185069933617477)
  ·
    refine ⟨22489301996097200612553277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119942943979185069933617477 22489301996097200612553277)
    ·
      refine ⟨8433488248536450229707479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22489301996097200612553277 8433488248536450229707479)
      ·
        refine ⟨12650232372804675344561219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8433488248536450229707479 12650232372804675344561219)
        ·
          refine ⟨18975348559207013016841829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650232372804675344561219 18975348559207013016841829)
          ·
            refine ⟨3557877854851314940657843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18975348559207013016841829 3557877854851314940657843)
            ·
              refine ⟨5336816782276972410986765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557877854851314940657843 5336816782276972410986765)
              ·
                refine ⟨2001306293353864654120037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5336816782276972410986765 2001306293353864654120037)
                ·
                  refine ⟨375244930003849622647507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001306293353864654120037 375244930003849622647507)
                  ·
                    rfl

theorem cell22_3288541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_3288541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288541 prefixEnd_3288541 := by exact prefixLift 3288541
  have htrace : WordTrace (prefixWord ++ tailWord_3288541) baseStart_3288541 baseEnd_3288541 := by
    simpa [prefixWord, tailWord_3288541, baseEnd_3288541] using wordTrace_append hprefix tailTrace_3288541
  have hstable : (prefixWord ++ tailWord_3288541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288541).length < 2 ^ (prefixWord ++ tailWord_3288541).sum := by decide
  have hdescent : baseEnd_3288541 < baseStart_3288541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288554 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3288554 : Nat := 118140960795 + 3288554 * 2 ^ 59
def prefixEnd_3288554 : Nat := 4983230072969 + 3 ^ 40 * 3288554 * 2
def baseEnd_3288554 : Nat := 1125739240177221167367481

theorem tailTrace_3288554 : CollatzResearch.WordTrace tailWord_3288554 prefixEnd_3288554 1125739240177221167367481 := by
  unfold tailWord_3288554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29985854532034493288460179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79962278752091982102560477 29985854532034493288460179)
  ·
    refine ⟨44978781798051739932690269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29985854532034493288460179 44978781798051739932690269)
    ·
      refine ⟨16867043174269402474758851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44978781798051739932690269 16867043174269402474758851)
      ·
        refine ⟨25300564761404103712138277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16867043174269402474758851 25300564761404103712138277)
        ·
          refine ⟨4743855892763269446025927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25300564761404103712138277 4743855892763269446025927)
          ·
            refine ⟨7115783839144904169038891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743855892763269446025927 7115783839144904169038891)
            ·
              refine ⟨10673675758717356253558337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115783839144904169038891 10673675758717356253558337)
              ·
                refine ⟨8005256819038017190168753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10673675758717356253558337 8005256819038017190168753)
                ·
                  refine ⟨6003942614278512892626565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005256819038017190168753 6003942614278512892626565)
                  ·
                    refine ⟨1125739240177221167367481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6003942614278512892626565 1125739240177221167367481)
                    ·
                      rfl

theorem cell22_3288554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3288554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288554 prefixEnd_3288554 := by exact prefixLift 3288554
  have htrace : WordTrace (prefixWord ++ tailWord_3288554) baseStart_3288554 baseEnd_3288554 := by
    simpa [prefixWord, tailWord_3288554, baseEnd_3288554] using wordTrace_append hprefix tailTrace_3288554
  have hstable : (prefixWord ++ tailWord_3288554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288554).length < 2 ^ (prefixWord ++ tailWord_3288554).sum := by decide
  have hdescent : baseEnd_3288554 < baseStart_3288554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288567 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 3, 3]
def baseStart_3288567 : Nat := 118140960795 + 3288567 * 2 ^ 59
def prefixEnd_3288567 : Nat := 4983230072969 + 3 ^ 40 * 3288567 * 2
def baseEnd_3288567 : Nat := 1125743690342893466792441

theorem tailTrace_3288567 : CollatzResearch.WordTrace tailWord_3288567 prefixEnd_3288567 1125743690342893466792441 := by
  unfold tailWord_3288567
  simp only [CollatzResearch.WordTrace]
  refine ⟨119943892277090876374063955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79962594851393917582709303 119943892277090876374063955)
  ·
    refine ⟨179915838415636314561095933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119943892277090876374063955 179915838415636314561095933)
    ·
      refine ⟨67468439405863617960410975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179915838415636314561095933 67468439405863617960410975)
      ·
        refine ⟨101202659108795426940616463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67468439405863617960410975 101202659108795426940616463)
        ·
          refine ⟨151803988663193140410924695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101202659108795426940616463 151803988663193140410924695)
          ·
            refine ⟨227705982994789710616387043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151803988663193140410924695 227705982994789710616387043)
            ·
              refine ⟨341558974492184565924580565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227705982994789710616387043 341558974492184565924580565)
              ·
                refine ⟨8005288464660575763857357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 341558974492184565924580565 8005288464660575763857357)
                ·
                  refine ⟨3001983174247715911446509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8005288464660575763857357 3001983174247715911446509)
                  ·
                    refine ⟨1125743690342893466792441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001983174247715911446509 1125743690342893466792441)
                    ·
                      rfl

theorem cell22_3288567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_3288567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288567 prefixEnd_3288567 := by exact prefixLift 3288567
  have htrace : WordTrace (prefixWord ++ tailWord_3288567) baseStart_3288567 baseEnd_3288567 := by
    simpa [prefixWord, tailWord_3288567, baseEnd_3288567] using wordTrace_append hprefix tailTrace_3288567
  have hstable : (prefixWord ++ tailWord_3288567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288567).length < 2 ^ (prefixWord ++ tailWord_3288567).sum := by decide
  have hdescent : baseEnd_3288567 < baseStart_3288567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288627 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 3, 4]
def baseStart_3288627 : Nat := 118140960795 + 3288627 * 2 ^ 59
def prefixEnd_3288627 : Nat := 4983230072969 + 3 ^ 40 * 3288627 * 2
def baseEnd_3288627 : Nat := 1125764229569073310292257

theorem tailTrace_3288627 : CollatzResearch.WordTrace tailWord_3288627 prefixEnd_3288627 1125764229569073310292257 := by
  unfold tailWord_3288627
  simp only [CollatzResearch.WordTrace]
  refine ⟨119946080656873506621248135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79964053771249004414165423 119946080656873506621248135)
  ·
    refine ⟨179919120985310259931872203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119946080656873506621248135 179919120985310259931872203)
    ·
      refine ⟨269878681477965389897808305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179919120985310259931872203 269878681477965389897808305)
      ·
        refine ⟨202409011108474042423356229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269878681477965389897808305 202409011108474042423356229)
        ·
          refine ⟨37951689582838882954379293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202409011108474042423356229 37951689582838882954379293)
          ·
            refine ⟨14231883593564581107892235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37951689582838882954379293 14231883593564581107892235)
            ·
              refine ⟨21347825390346871661838353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14231883593564581107892235 21347825390346871661838353)
              ·
                refine ⟨16010869042760153746378765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21347825390346871661838353 16010869042760153746378765)
                ·
                  refine ⟨6004075891035057654892037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16010869042760153746378765 6004075891035057654892037)
                  ·
                    refine ⟨1125764229569073310292257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004075891035057654892037 1125764229569073310292257)
                    ·
                      rfl

theorem cell22_3288627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_3288627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288627 prefixEnd_3288627 := by exact prefixLift 3288627
  have htrace : WordTrace (prefixWord ++ tailWord_3288627) baseStart_3288627 baseEnd_3288627 := by
    simpa [prefixWord, tailWord_3288627, baseEnd_3288627] using wordTrace_append hprefix tailTrace_3288627
  have hstable : (prefixWord ++ tailWord_3288627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288627).length < 2 ^ (prefixWord ++ tailWord_3288627).sum := by decide
  have hdescent : baseEnd_3288627 < baseStart_3288627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288657 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3288657 : Nat := 118140960795 + 3288657 * 2 ^ 59
def prefixEnd_3288657 : Nat := 4983230072969 + 3 ^ 40 * 3288657 * 2
def baseEnd_3288657 : Nat := 1125774499182163232042165

theorem tailTrace_3288657 : CollatzResearch.WordTrace tailWord_3288657 prefixEnd_3288657 1125774499182163232042165 := by
  unfold tailWord_3288657
  simp only [CollatzResearch.WordTrace]
  refine ⟨119947174846764821744840225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79964783231176547829893483 119947174846764821744840225)
  ·
    refine ⟨89960381135073616308630169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119947174846764821744840225 89960381135073616308630169)
    ·
      refine ⟨67470285851305212231472627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89960381135073616308630169 67470285851305212231472627)
      ·
        refine ⟨101205428776957818347208941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67470285851305212231472627 101205428776957818347208941)
        ·
          refine ⟨37952035791359181880203353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101205428776957818347208941 37952035791359181880203353)
          ·
            refine ⟨28464026843519386410152515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37952035791359181880203353 28464026843519386410152515)
            ·
              refine ⟨42696040265279079615228773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28464026843519386410152515 42696040265279079615228773)
              ·
                refine ⟨8005507549739827427855395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42696040265279079615228773 8005507549739827427855395)
                ·
                  refine ⟨12008261324609741141783093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8005507549739827427855395 12008261324609741141783093)
                  ·
                    refine ⟨1125774499182163232042165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12008261324609741141783093 1125774499182163232042165)
                    ·
                      rfl

theorem cell22_3288657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3288657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288657 prefixEnd_3288657 := by exact prefixLift 3288657
  have htrace : WordTrace (prefixWord ++ tailWord_3288657) baseStart_3288657 baseEnd_3288657 := by
    simpa [prefixWord, tailWord_3288657, baseEnd_3288657] using wordTrace_append hprefix tailTrace_3288657
  have hstable : (prefixWord ++ tailWord_3288657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288657).length < 2 ^ (prefixWord ++ tailWord_3288657).sum := by decide
  have hdescent : baseEnd_3288657 < baseStart_3288657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288672 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_3288672 : Nat := 118140960795 + 3288672 * 2 ^ 59
def prefixEnd_3288672 : Nat := 4983230072969 + 3 ^ 40 * 3288672 * 2
def baseEnd_3288672 : Nat := 1125779633988708192917119

theorem tailTrace_3288672 : CollatzResearch.WordTrace tailWord_3288672 prefixEnd_3288672 1125779633988708192917119 := by
  unfold tailWord_3288672
  simp only [CollatzResearch.WordTrace]
  refine ⟨59973860970855239653318135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79965147961140319537757513 59973860970855239653318135)
  ·
    refine ⟨89960791456282859479977203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59973860970855239653318135 89960791456282859479977203)
    ·
      refine ⟨134941187184424289219965805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89960791456282859479977203 134941187184424289219965805)
      ·
        refine ⟨50602945194159108457487177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134941187184424289219965805 50602945194159108457487177)
        ·
          refine ⟨37952208895619331343115383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50602945194159108457487177 37952208895619331343115383)
          ·
            refine ⟨56928313343428997014673075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37952208895619331343115383 56928313343428997014673075)
            ·
              refine ⟨85392470015143495522009613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56928313343428997014673075 85392470015143495522009613)
              ·
                refine ⟨32022176255678810820753605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85392470015143495522009613 32022176255678810820753605)
                ·
                  refine ⟨6004158047939777028891301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32022176255678810820753605 6004158047939777028891301)
                  ·
                    refine ⟨1125779633988708192917119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004158047939777028891301 1125779633988708192917119)
                    ·
                      rfl

theorem cell22_3288672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_3288672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288672 prefixEnd_3288672 := by exact prefixLift 3288672
  have htrace : WordTrace (prefixWord ++ tailWord_3288672) baseStart_3288672 baseEnd_3288672 := by
    simpa [prefixWord, tailWord_3288672, baseEnd_3288672] using wordTrace_append hprefix tailTrace_3288672
  have hstable : (prefixWord ++ tailWord_3288672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288672).length < 2 ^ (prefixWord ++ tailWord_3288672).sum := by decide
  have hdescent : baseEnd_3288672 < baseStart_3288672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288736 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 3, 3]
def baseStart_3288736 : Nat := 118140960795 + 3288736 * 2 ^ 59
def prefixEnd_3288736 : Nat := 4983230072969 + 3 ^ 40 * 3288736 * 2
def baseEnd_3288736 : Nat := 1125801542496633359316923

theorem tailTrace_3288736 : CollatzResearch.WordTrace tailWord_3288736 prefixEnd_3288736 1125801542496633359316923 := by
  unfold tailWord_3288736
  simp only [CollatzResearch.WordTrace]
  refine ⟨59975028106739309118483031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79966704142319078824644041 59975028106739309118483031)
  ·
    refine ⟨89962542160108963677724547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59975028106739309118483031 89962542160108963677724547)
    ·
      refine ⟨134943813240163445516586821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89962542160108963677724547 134943813240163445516586821)
      ·
        refine ⟨25301964982530646034360029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134943813240163445516586821 25301964982530646034360029)
        ·
          refine ⟨9488236868448992262885011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25301964982530646034360029 9488236868448992262885011)
          ·
            refine ⟨14232355302673488394327517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9488236868448992262885011 14232355302673488394327517)
            ·
              refine ⟨5337133238502558147872819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14232355302673488394327517 5337133238502558147872819)
              ·
                refine ⟨8005699857753837221809229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337133238502558147872819 8005699857753837221809229)
                ·
                  refine ⟨3002137446657688958178461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8005699857753837221809229 3002137446657688958178461)
                  ·
                    refine ⟨1125801542496633359316923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002137446657688958178461 1125801542496633359316923)
                    ·
                      rfl

theorem cell22_3288736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_3288736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288736 prefixEnd_3288736 := by exact prefixLift 3288736
  have htrace : WordTrace (prefixWord ++ tailWord_3288736) baseStart_3288736 baseEnd_3288736 := by
    simpa [prefixWord, tailWord_3288736, baseEnd_3288736] using wordTrace_append hprefix tailTrace_3288736
  have hstable : (prefixWord ++ tailWord_3288736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288736).length < 2 ^ (prefixWord ++ tailWord_3288736).sum := by decide
  have hdescent : baseEnd_3288736 < baseStart_3288736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288779 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 1, 4]
def baseStart_3288779 : Nat := 118140960795 + 3288779 * 2 ^ 59
def prefixEnd_3288779 : Nat := 4983230072969 + 3 ^ 40 * 3288779 * 2
def baseEnd_3288779 : Nat := 1125816262275395580491791

theorem tailTrace_3288779 : CollatzResearch.WordTrace tailWord_3288779 prefixEnd_3288779 1125816262275395580491791 := by
  unfold tailWord_3288779
  simp only [CollatzResearch.WordTrace]
  refine ⟨119951624552322836580781391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79967749701548557720520927 119951624552322836580781391)
  ·
    refine ⟨179927436828484254871172087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119951624552322836580781391 179927436828484254871172087)
    ·
      refine ⟨269891155242726382306758131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179927436828484254871172087 269891155242726382306758131)
      ·
        refine ⟨404836732864089573460137197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269891155242726382306758131 404836732864089573460137197)
        ·
          refine ⟨151813774824033590047551449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404836732864089573460137197 151813774824033590047551449)
          ·
            refine ⟨113860331118025192535663587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151813774824033590047551449 113860331118025192535663587)
            ·
              refine ⟨170790496677037788803495381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113860331118025192535663587 170790496677037788803495381)
              ·
                refine ⟨4002902265868073175081923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 170790496677037788803495381 4002902265868073175081923)
                ·
                  refine ⟨6004353398802109762622885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002902265868073175081923 6004353398802109762622885)
                  ·
                    refine ⟨1125816262275395580491791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004353398802109762622885 1125816262275395580491791)
                    ·
                      rfl

theorem cell22_3288779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 4].length) (baseStart_3288779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288779 prefixEnd_3288779 := by exact prefixLift 3288779
  have htrace : WordTrace (prefixWord ++ tailWord_3288779) baseStart_3288779 baseEnd_3288779 := by
    simpa [prefixWord, tailWord_3288779, baseEnd_3288779] using wordTrace_append hprefix tailTrace_3288779
  have hstable : (prefixWord ++ tailWord_3288779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288779).length < 2 ^ (prefixWord ++ tailWord_3288779).sum := by decide
  have hdescent : baseEnd_3288779 < baseStart_3288779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288809 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 6, 3]
def baseStart_3288809 : Nat := 118140960795 + 3288809 * 2 ^ 59
def prefixEnd_3288809 : Nat := 4983230072969 + 3 ^ 40 * 3288809 * 2
def baseEnd_3288809 : Nat := 1125826531888485502241699

theorem tailTrace_3288809 : CollatzResearch.WordTrace tailWord_3288809 prefixEnd_3288809 1125826531888485502241699 := by
  unfold tailWord_3288809
  simp only [CollatzResearch.WordTrace]
  refine ⟨119952718742214151704373481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79968479161476101136248987 119952718742214151704373481)
  ·
    refine ⟨89964539056660613778280111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119952718742214151704373481 89964539056660613778280111)
    ·
      refine ⟨134946808584990920667420167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89964539056660613778280111 134946808584990920667420167)
      ·
        refine ⟨202420212877486381001130251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134946808584990920667420167 202420212877486381001130251)
        ·
          refine ⟨303630319316229571501695377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202420212877486381001130251 303630319316229571501695377)
          ·
            refine ⟨227722739487172178626271533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303630319316229571501695377 227722739487172178626271533)
            ·
              refine ⟨85396027307689566984851825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227722739487172178626271533 85396027307689566984851825)
              ·
                refine ⟨64047020480767175238638869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85396027307689566984851825 64047020480767175238638869)
                ·
                  refine ⟨3002204085035961339311197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64047020480767175238638869 3002204085035961339311197)
                  ·
                    refine ⟨1125826531888485502241699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002204085035961339311197 1125826531888485502241699)
                    ·
                      rfl

theorem cell22_3288809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_3288809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288809 prefixEnd_3288809 := by exact prefixLift 3288809
  have htrace : WordTrace (prefixWord ++ tailWord_3288809) baseStart_3288809 baseEnd_3288809 := by
    simpa [prefixWord, tailWord_3288809, baseEnd_3288809] using wordTrace_append hprefix tailTrace_3288809
  have hstable : (prefixWord ++ tailWord_3288809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288809).length < 2 ^ (prefixWord ++ tailWord_3288809).sum := by decide
  have hdescent : baseEnd_3288809 < baseStart_3288809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288824 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_3288824 : Nat := 118140960795 + 3288824 * 2 ^ 59
def prefixEnd_3288824 : Nat := 4983230072969 + 3 ^ 40 * 3288824 * 2
def baseEnd_3288824 : Nat := 1125831666695030463116653

theorem tailTrace_3288824 : CollatzResearch.WordTrace tailWord_3288824 prefixEnd_3288824 1125831666695030463116653 := by
  unfold tailWord_3288824
  simp only [CollatzResearch.WordTrace]
  refine ⟨59976632918579904633084763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79968843891439872844113017 59976632918579904633084763)
  ·
    refine ⟨89964949377869856949627145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59976632918579904633084763 89964949377869856949627145)
    ·
      refine ⟨67473712033402392712220359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89964949377869856949627145 67473712033402392712220359)
      ·
        refine ⟨101210568050103589068330539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67473712033402392712220359 101210568050103589068330539)
        ·
          refine ⟨151815852075155383602495809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101210568050103589068330539 151815852075155383602495809)
          ·
            refine ⟨113861889056366537701871857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151815852075155383602495809 113861889056366537701871857)
            ·
              refine ⟨85396416792274903276403893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113861889056366537701871857 85396416792274903276403893)
              ·
                refine ⟨8005914074275772182162865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85396416792274903276403893 8005914074275772182162865)
                ·
                  refine ⟨6004435555706829136622149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005914074275772182162865 6004435555706829136622149)
                  ·
                    refine ⟨1125831666695030463116653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004435555706829136622149 1125831666695030463116653)
                    ·
                      rfl

theorem cell22_3288824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_3288824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288824 prefixEnd_3288824 := by exact prefixLift 3288824
  have htrace : WordTrace (prefixWord ++ tailWord_3288824) baseStart_3288824 baseEnd_3288824 := by
    simpa [prefixWord, tailWord_3288824, baseEnd_3288824] using wordTrace_append hprefix tailTrace_3288824
  have hstable : (prefixWord ++ tailWord_3288824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288824).length < 2 ^ (prefixWord ++ tailWord_3288824).sum := by decide
  have hdescent : baseEnd_3288824 < baseStart_3288824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288905 : List Nat := [1, 2, 1, 1, 2, 4, 5, 2, 1, 3]
def baseStart_3288905 : Nat := 118140960795 + 3288905 * 2 ^ 59
def prefixEnd_3288905 : Nat := 4983230072969 + 3 ^ 40 * 3288905 * 2
def baseEnd_3288905 : Nat := 1125859394650373251841405

theorem tailTrace_3288905 : CollatzResearch.WordTrace tailWord_3288905 prefixEnd_3288905 1125859394650373251841405 := by
  unfold tailWord_3288905
  simp only [CollatzResearch.WordTrace]
  refine ⟨119956220149866360099868169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79970813433244240066578779 119956220149866360099868169)
  ·
    refine ⟨89967165112399770074901127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119956220149866360099868169 89967165112399770074901127)
    ·
      refine ⟨134950747668599655112351691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89967165112399770074901127 134950747668599655112351691)
      ·
        refine ⟨202426121502899482668527537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134950747668599655112351691 202426121502899482668527537)
        ·
          refine ⟨151819591127174612001395653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202426121502899482668527537 151819591127174612001395653)
          ·
            refine ⟨28466173336345239750261685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151819591127174612001395653 28466173336345239750261685)
            ·
              refine ⟨2668703750282366226587033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28466173336345239750261685 2668703750282366226587033)
              ·
                refine ⟨2001527812711774669940275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2668703750282366226587033 2001527812711774669940275)
                ·
                  refine ⟨3002291719067662004910413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001527812711774669940275 3002291719067662004910413)
                  ·
                    refine ⟨1125859394650373251841405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002291719067662004910413 1125859394650373251841405)
                    ·
                      rfl

theorem cell22_3288905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 3].length) (baseStart_3288905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288905 prefixEnd_3288905 := by exact prefixLift 3288905
  have htrace : WordTrace (prefixWord ++ tailWord_3288905) baseStart_3288905 baseEnd_3288905 := by
    simpa [prefixWord, tailWord_3288905, baseEnd_3288905] using wordTrace_append hprefix tailTrace_3288905
  have hstable : (prefixWord ++ tailWord_3288905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288905).length < 2 ^ (prefixWord ++ tailWord_3288905).sum := by decide
  have hdescent : baseEnd_3288905 < baseStart_3288905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288929 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 8]
def baseStart_3288929 : Nat := 118140960795 + 3288929 * 2 ^ 59
def prefixEnd_3288929 : Nat := 4983230072969 + 3 ^ 40 * 3288929 * 2
def baseEnd_3288929 : Nat := 375289203446948396413777

theorem tailTrace_3288929 : CollatzResearch.WordTrace tailWord_3288929 prefixEnd_3288929 375289203446948396413777 := by
  unfold tailWord_3288929
  simp only [CollatzResearch.WordTrace]
  refine ⟨119957095501779412198741841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79971397001186274799161227 119957095501779412198741841)
  ·
    refine ⟨89967821626334559149056381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119957095501779412198741841 89967821626334559149056381)
    ·
      refine ⟨33737933109875459680896143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89967821626334559149056381 33737933109875459680896143)
      ·
        refine ⟨50606899664813189521344215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33737933109875459680896143 50606899664813189521344215)
        ·
          refine ⟨75910349497219784282016323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50606899664813189521344215 75910349497219784282016323)
          ·
            refine ⟨113865524245829676423024485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75910349497219784282016323 113865524245829676423024485)
            ·
              refine ⟨21349785796093064329317091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113865524245829676423024485 21349785796093064329317091)
              ·
                refine ⟨32024678694139596493975637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21349785796093064329317091 32024678694139596493975637)
                ·
                  refine ⟨375289203446948396413777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32024678694139596493975637 375289203446948396413777)
                  ·
                    rfl

theorem cell22_3288929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_3288929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288929 prefixEnd_3288929 := by exact prefixLift 3288929
  have htrace : WordTrace (prefixWord ++ tailWord_3288929) baseStart_3288929 baseEnd_3288929 := by
    simpa [prefixWord, tailWord_3288929, baseEnd_3288929] using wordTrace_append hprefix tailTrace_3288929
  have hstable : (prefixWord ++ tailWord_3288929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288929).length < 2 ^ (prefixWord ++ tailWord_3288929).sum := by decide
  have hdescent : baseEnd_3288929 < baseStart_3288929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288959 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 3, 6]
def baseStart_3288959 : Nat := 118140960795 + 3288959 * 2 ^ 59
def prefixEnd_3288959 : Nat := 4983230072969 + 3 ^ 40 * 3288959 * 2
def baseEnd_3288959 : Nat := 1125877879953935110991239

theorem tailTrace_3288959 : CollatzResearch.WordTrace tailWord_3288959 prefixEnd_3288959 1125877879953935110991239 := by
  unfold tailWord_3288959
  simp only [CollatzResearch.WordTrace]
  refine ⟨119958189691670727322333931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79972126461113818214889287 119958189691670727322333931)
  ·
    refine ⟨179937284537506090983500897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119958189691670727322333931 179937284537506090983500897)
    ·
      refine ⟨134952963403129568237625673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179937284537506090983500897 134952963403129568237625673)
      ·
        refine ⟨101214722552347176178219255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134952963403129568237625673 101214722552347176178219255)
        ·
          refine ⟨151822083828520764267328883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101214722552347176178219255 151822083828520764267328883)
          ·
            refine ⟨227733125742781146400993325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151822083828520764267328883 227733125742781146400993325)
            ·
              refine ⟨85399922153542929900372497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227733125742781146400993325 85399922153542929900372497)
              ·
                refine ⟨64049941615157197425279373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85399922153542929900372497 64049941615157197425279373)
                ·
                  refine ⟨24018728105683949034479765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64049941615157197425279373 24018728105683949034479765)
                  ·
                    refine ⟨1125877879953935110991239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24018728105683949034479765 1125877879953935110991239)
                    ·
                      rfl

theorem cell22_3288959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_3288959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288959 prefixEnd_3288959 := by exact prefixLift 3288959
  have htrace : WordTrace (prefixWord ++ tailWord_3288959) baseStart_3288959 baseEnd_3288959 := by
    simpa [prefixWord, tailWord_3288959, baseEnd_3288959] using wordTrace_append hprefix tailTrace_3288959
  have hstable : (prefixWord ++ tailWord_3288959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288959).length < 2 ^ (prefixWord ++ tailWord_3288959).sum := by decide
  have hdescent : baseEnd_3288959 < baseStart_3288959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288963 : List Nat := [1, 1, 1, 3, 4, 3, 1, 4, 4]
def baseStart_3288963 : Nat := 118140960795 + 3288963 * 2 ^ 59
def prefixEnd_3288963 : Nat := 4983230072969 + 3 ^ 40 * 3288963 * 2
def baseEnd_3288963 : Nat := 375293083078560144630409

theorem tailTrace_3288963 : CollatzResearch.WordTrace tailWord_3288963 prefixEnd_3288963 375293083078560144630409 := by
  unfold tailWord_3288963
  simp only [CollatzResearch.WordTrace]
  refine ⟨119958335583656236005479543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79972223722437490670319695 119958335583656236005479543)
  ·
    refine ⟨179937503375484354008219315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119958335583656236005479543 179937503375484354008219315)
    ·
      refine ⟨269906255063226531012328973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179937503375484354008219315 269906255063226531012328973)
      ·
        refine ⟨101214845648709949129623365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269906255063226531012328973 101214845648709949129623365)
        ·
          refine ⟨18977783559133115461804381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101214845648709949129623365 18977783559133115461804381)
          ·
            refine ⟨7116668834674918298176643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18977783559133115461804381 7116668834674918298176643)
            ·
              refine ⟨10675003252012377447264965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116668834674918298176643 10675003252012377447264965)
              ·
                refine ⟨2001563109752320771362181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10675003252012377447264965 2001563109752320771362181)
                ·
                  refine ⟨375293083078560144630409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001563109752320771362181 375293083078560144630409)
                  ·
                    rfl

theorem cell22_3288963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 4].length) (baseStart_3288963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288963 prefixEnd_3288963 := by exact prefixLift 3288963
  have htrace : WordTrace (prefixWord ++ tailWord_3288963) baseStart_3288963 baseEnd_3288963 := by
    simpa [prefixWord, tailWord_3288963, baseEnd_3288963] using wordTrace_append hprefix tailTrace_3288963
  have hstable : (prefixWord ++ tailWord_3288963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288963).length < 2 ^ (prefixWord ++ tailWord_3288963).sum := by decide
  have hdescent : baseEnd_3288963 < baseStart_3288963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288978 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3288978 : Nat := 118140960795 + 3288978 * 2 ^ 59
def prefixEnd_3288978 : Nat := 4983230072969 + 3 ^ 40 * 3288978 * 2
def baseEnd_3288978 : Nat := 1125884384042225394766181

theorem tailTrace_3288978 : CollatzResearch.WordTrace tailWord_3288978 prefixEnd_3288978 1125884384042225394766181 := by
  unfold tailWord_3288978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29989720669650473391818897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79972588452401262378183725 29989720669650473391818897)
  ·
    refine ⟨22492290502237855043864173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29989720669650473391818897 22492290502237855043864173)
    ·
      refine ⟨8434608938339195641449065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22492290502237855043864173 8434608938339195641449065)
      ·
        refine ⟨6325956703754396731086799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8434608938339195641449065 6325956703754396731086799)
        ·
          refine ⟨9488935055631595096630199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6325956703754396731086799 9488935055631595096630199)
          ·
            refine ⟨14233402583447392644945299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9488935055631595096630199 14233402583447392644945299)
            ·
              refine ⟨21350103875171088967417949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14233402583447392644945299 21350103875171088967417949)
              ·
                refine ⟨8006288953189158362781731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21350103875171088967417949 8006288953189158362781731)
                ·
                  refine ⟨12009433429783737544172597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006288953189158362781731 12009433429783737544172597)
                  ·
                    refine ⟨1125884384042225394766181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12009433429783737544172597 1125884384042225394766181)
                    ·
                      rfl

theorem cell22_3288978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3288978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288978 prefixEnd_3288978 := by exact prefixLift 3288978
  have htrace : WordTrace (prefixWord ++ tailWord_3288978) baseStart_3288978 baseEnd_3288978 := by
    simpa [prefixWord, tailWord_3288978, baseEnd_3288978] using wordTrace_append hprefix tailTrace_3288978
  have hstable : (prefixWord ++ tailWord_3288978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288978).length < 2 ^ (prefixWord ++ tailWord_3288978).sum := by decide
  have hdescent : baseEnd_3288978 < baseStart_3288978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3288993 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3288993 : Nat := 118140960795 + 3288993 * 2 ^ 59
def prefixEnd_3288993 : Nat := 4983230072969 + 3 ^ 40 * 3288993 * 2
def baseEnd_3288993 : Nat := 1125889518848770355641135

theorem tailTrace_3288993 : CollatzResearch.WordTrace tailWord_3288993 prefixEnd_3288993 1125889518848770355641135 := by
  unfold tailWord_3288993
  simp only [CollatzResearch.WordTrace]
  refine ⟨119959429773547551129071633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79972953182365034086047755 119959429773547551129071633)
  ·
    refine ⟨89969572330160663346803725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119959429773547551129071633 89969572330160663346803725)
    ·
      refine ⟨33738589623810248755051397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89969572330160663346803725 33738589623810248755051397)
      ·
        refine ⟨6325985554464421641572137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33738589623810248755051397 6325985554464421641572137)
        ·
          refine ⟨4744489165848316231179103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6325985554464421641572137 4744489165848316231179103)
          ·
            refine ⟨7116733748772474346768655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744489165848316231179103 7116733748772474346768655)
            ·
              refine ⟨10675100623158711520152983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116733748772474346768655 10675100623158711520152983)
              ·
                refine ⟨16012650934738067280229475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10675100623158711520152983 16012650934738067280229475)
                ·
                  refine ⟨24018976402107100920344213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16012650934738067280229475 24018976402107100920344213)
                  ·
                    refine ⟨1125889518848770355641135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24018976402107100920344213 1125889518848770355641135)
                    ·
                      rfl

theorem cell22_3288993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3288993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3288993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3288993 prefixEnd_3288993 := by exact prefixLift 3288993
  have htrace : WordTrace (prefixWord ++ tailWord_3288993) baseStart_3288993 baseEnd_3288993 := by
    simpa [prefixWord, tailWord_3288993, baseEnd_3288993] using wordTrace_append hprefix tailTrace_3288993
  have hstable : (prefixWord ++ tailWord_3288993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3288993).length < 2 ^ (prefixWord ++ tailWord_3288993).sum := by decide
  have hdescent : baseEnd_3288993 < baseStart_3288993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3288993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289012 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3289012 : Nat := 118140960795 + 3289012 * 2 ^ 59
def prefixEnd_3289012 : Nat := 4983230072969 + 3 ^ 40 * 3289012 * 2
def baseEnd_3289012 : Nat := 1125896022937060639416077

theorem tailTrace_3289012 : CollatzResearch.WordTrace tailWord_3289012 prefixEnd_3289012 1125896022937060639416077 := by
  unfold tailWord_3289012
  simp only [CollatzResearch.WordTrace]
  refine ⟨59980061380239358687006645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79973415173652478249342193 59980061380239358687006645)
  ·
    refine ⟨5623130754397439876906873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59980061380239358687006645 5623130754397439876906873)
    ·
      refine ⟨4217348065798079907680155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5623130754397439876906873 4217348065798079907680155)
      ·
        refine ⟨6326022098697119861520233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4217348065798079907680155 6326022098697119861520233)
        ·
          refine ⟨4744516574022839896140175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6326022098697119861520233 4744516574022839896140175)
          ·
            refine ⟨7116774861034259844210263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744516574022839896140175 7116774861034259844210263)
            ·
              refine ⟨10675162291551389766315395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116774861034259844210263 10675162291551389766315395)
              ·
                refine ⟨16012743437327084649473093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10675162291551389766315395 16012743437327084649473093)
                ·
                  refine ⟨3002389394498828371776205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16012743437327084649473093 3002389394498828371776205)
                  ·
                    refine ⟨1125896022937060639416077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002389394498828371776205 1125896022937060639416077)
                    ·
                      rfl

theorem cell22_3289012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3289012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289012 prefixEnd_3289012 := by exact prefixLift 3289012
  have htrace : WordTrace (prefixWord ++ tailWord_3289012) baseStart_3289012 baseEnd_3289012 := by
    simpa [prefixWord, tailWord_3289012, baseEnd_3289012] using wordTrace_append hprefix tailTrace_3289012
  have hstable : (prefixWord ++ tailWord_3289012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289012).length < 2 ^ (prefixWord ++ tailWord_3289012).sum := by decide
  have hdescent : baseEnd_3289012 < baseStart_3289012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289023 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 3, 3]
def baseStart_3289023 : Nat := 118140960795 + 3289023 * 2 ^ 59
def prefixEnd_3289023 : Nat := 4983230072969 + 3 ^ 40 * 3289023 * 2
def baseEnd_3289023 : Nat := 1125899788461860277391043

theorem tailTrace_3289023 : CollatzResearch.WordTrace tailWord_3289023 prefixEnd_3289023 1125899788461860277391043 := by
  unfold tailWord_3289023
  simp only [CollatzResearch.WordTrace]
  refine ⟨119960523963438866252663723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79973682642292577501775815 119960523963438866252663723)
  ·
    refine ⟨179940785945158299378995585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119960523963438866252663723 179940785945158299378995585)
    ·
      refine ⟨134955589458868724534246689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179940785945158299378995585 134955589458868724534246689)
      ·
        refine ⟨101216692094151543400685017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134955589458868724534246689 101216692094151543400685017)
        ·
          refine ⟨75912519070613657550513763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101216692094151543400685017 75912519070613657550513763)
          ·
            refine ⟨113868778605920486325770645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75912519070613657550513763 113868778605920486325770645)
            ·
              refine ⟨5337598997152522796520499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113868778605920486325770645 5337598997152522796520499)
              ·
                refine ⟨8006398495728784194780749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337598997152522796520499 8006398495728784194780749)
                ·
                  refine ⟨3002399435898294073042781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8006398495728784194780749 3002399435898294073042781)
                  ·
                    refine ⟨1125899788461860277391043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002399435898294073042781 1125899788461860277391043)
                    ·
                      rfl

theorem cell22_3289023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_3289023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289023 prefixEnd_3289023 := by exact prefixLift 3289023
  have htrace : WordTrace (prefixWord ++ tailWord_3289023) baseStart_3289023 baseEnd_3289023 := by
    simpa [prefixWord, tailWord_3289023, baseEnd_3289023] using wordTrace_append hprefix tailTrace_3289023
  have hstable : (prefixWord ++ tailWord_3289023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289023).length < 2 ^ (prefixWord ++ tailWord_3289023).sum := by decide
  have hdescent : baseEnd_3289023 < baseStart_3289023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289042 : List Nat := [3, 2, 2, 3, 3, 1, 2, 6]
def baseStart_3289042 : Nat := 118140960795 + 3289042 * 2 ^ 59
def prefixEnd_3289042 : Nat := 4983230072969 + 3 ^ 40 * 3289042 * 2
def baseEnd_3289042 : Nat := 125100699172238951240665

theorem tailTrace_3289042 : CollatzResearch.WordTrace tailWord_3289042 prefixEnd_3289042 125100699172238951240665 := by
  unfold tailWord_3289042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29990304237592508124401345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79974144633580021665070253 29990304237592508124401345)
  ·
    refine ⟨22492728178194381093301009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29990304237592508124401345 22492728178194381093301009)
    ·
      refine ⟨16869546133645785819975757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22492728178194381093301009 16869546133645785819975757)
      ·
        refine ⟨6326079800117169682490909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16869546133645785819975757 6326079800117169682490909)
        ·
          refine ⟨2372279925043938630934091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6326079800117169682490909 2372279925043938630934091)
          ·
            refine ⟨3558419887565907946401137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372279925043938630934091 3558419887565907946401137)
            ·
              refine ⟨2668814915674430959800853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3558419887565907946401137 2668814915674430959800853)
              ·
                refine ⟨125100699172238951240665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2668814915674430959800853 125100699172238951240665)
                ·
                  rfl

theorem cell22_3289042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_3289042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289042 prefixEnd_3289042 := by exact prefixLift 3289042
  have htrace : WordTrace (prefixWord ++ tailWord_3289042) baseStart_3289042 baseEnd_3289042 := by
    simpa [prefixWord, tailWord_3289042, baseEnd_3289042] using wordTrace_append hprefix tailTrace_3289042
  have hstable : (prefixWord ++ tailWord_3289042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289042).length < 2 ^ (prefixWord ++ tailWord_3289042).sum := by decide
  have hdescent : baseEnd_3289042 < baseStart_3289042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289117 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_3289117 : Nat := 118140960795 + 3289117 * 2 ^ 59
def prefixEnd_3289117 : Nat := 4983230072969 + 3 ^ 40 * 3289117 * 2
def baseEnd_3289117 : Nat := 1125931966582875365540755

theorem tailTrace_3289117 : CollatzResearch.WordTrace tailWord_3289117 prefixEnd_3289117 1125931966582875365540755 := by
  unfold tailWord_3289117
  simp only [CollatzResearch.WordTrace]
  refine ⟨119963952425098320306585605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79975968283398880204390403 119963952425098320306585605)
  ·
    refine ⟨22493241079705935057484801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119963952425098320306585605 22493241079705935057484801)
    ·
      refine ⟨16869930809779451293113601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22493241079705935057484801 16869930809779451293113601)
      ·
        refine ⟨12652448107334588469835201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16869930809779451293113601 12652448107334588469835201)
        ·
          refine ⟨9489336080500941352376401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12652448107334588469835201 9489336080500941352376401)
          ·
            refine ⟨7117002060375706014282301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9489336080500941352376401 7117002060375706014282301)
            ·
              refine ⟨2668875772640889755355863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7117002060375706014282301 2668875772640889755355863)
              ·
                refine ⟨4003313658961334633033795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668875772640889755355863 4003313658961334633033795)
                ·
                  refine ⟨6004970488442001949550693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003313658961334633033795 6004970488442001949550693)
                  ·
                    refine ⟨1125931966582875365540755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004970488442001949550693 1125931966582875365540755)
                    ·
                      rfl

theorem cell22_3289117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_3289117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289117 prefixEnd_3289117 := by exact prefixLift 3289117
  have htrace : WordTrace (prefixWord ++ tailWord_3289117) baseStart_3289117 baseEnd_3289117 := by
    simpa [prefixWord, tailWord_3289117, baseEnd_3289117] using wordTrace_append hprefix tailTrace_3289117
  have hstable : (prefixWord ++ tailWord_3289117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289117).length < 2 ^ (prefixWord ++ tailWord_3289117).sum := by decide
  have hdescent : baseEnd_3289117 < baseStart_3289117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289263 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 6, 4]
def baseStart_3289263 : Nat := 118140960795 + 3289263 * 2 ^ 59
def prefixEnd_3289263 : Nat := 4983230072969 + 3 ^ 40 * 3289263 * 2
def baseEnd_3289263 : Nat := 1125981945366579651390307

theorem tailTrace_3289263 : CollatzResearch.WordTrace tailWord_3289263 prefixEnd_3289263 1125981945366579651390307 := by
  unfold tailWord_3289263
  simp only [CollatzResearch.WordTrace]
  refine ⟨119969277482569387241400443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79979518321712924827600295 119969277482569387241400443)
  ·
    refine ⟨179953916223854080862100665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119969277482569387241400443 179953916223854080862100665)
    ·
      refine ⟨134965437167890560646575499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179953916223854080862100665 134965437167890560646575499)
      ·
        refine ⟨202448155751835840969863249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134965437167890560646575499 202448155751835840969863249)
        ·
          refine ⟨151836116813876880727397437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202448155751835840969863249 151836116813876880727397437)
          ·
            refine ⟨56938543805203830272774039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151836116813876880727397437 56938543805203830272774039)
            ·
              refine ⟨85407815707805745409161059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56938543805203830272774039 85407815707805745409161059)
              ·
                refine ⟨128111723561708618113741589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85407815707805745409161059 128111723561708618113741589)
                ·
                  refine ⟨6005237041955091474081637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128111723561708618113741589 6005237041955091474081637)
                  ·
                    refine ⟨1125981945366579651390307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005237041955091474081637 1125981945366579651390307)
                    ·
                      rfl

theorem cell22_3289263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_3289263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289263 prefixEnd_3289263 := by exact prefixLift 3289263
  have htrace : WordTrace (prefixWord ++ tailWord_3289263) baseStart_3289263 baseEnd_3289263 := by
    simpa [prefixWord, tailWord_3289263, baseEnd_3289263] using wordTrace_append hprefix tailTrace_3289263
  have hstable : (prefixWord ++ tailWord_3289263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289263).length < 2 ^ (prefixWord ++ tailWord_3289263).sum := by decide
  have hdescent : baseEnd_3289263 < baseStart_3289263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289280 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_3289280 : Nat := 118140960795 + 3289280 * 2 ^ 59
def prefixEnd_3289280 : Nat := 4983230072969 + 3 ^ 40 * 3289280 * 2
def baseEnd_3289280 : Nat := 1125987764813997273715255

theorem tailTrace_3289280 : CollatzResearch.WordTrace tailWord_3289280 prefixEnd_3289280 1125987764813997273715255 := by
  unfold tailWord_3289280
  simp only [CollatzResearch.WordTrace]
  refine ⟨59984948761753899572384647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79979931682338532763179529 59984948761753899572384647)
  ·
    refine ⟨89977423142630849358576971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59984948761753899572384647 89977423142630849358576971)
    ·
      refine ⟨134966134713946274037865457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89977423142630849358576971 134966134713946274037865457)
      ·
        refine ⟨101224601035459705528399093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134966134713946274037865457 101224601035459705528399093)
        ·
          refine ⟨9489806347074347393287415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101224601035459705528399093 9489806347074347393287415)
          ·
            refine ⟨14234709520611521089931123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489806347074347393287415 14234709520611521089931123)
            ·
              refine ⟨21352064280917281634896685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14234709520611521089931123 21352064280917281634896685)
              ·
                refine ⟨8007024105343980613086257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21352064280917281634896685 8007024105343980613086257)
                ·
                  refine ⟨6005268079007985459814693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8007024105343980613086257 6005268079007985459814693)
                  ·
                    refine ⟨1125987764813997273715255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005268079007985459814693 1125987764813997273715255)
                    ·
                      rfl

theorem cell22_3289280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_3289280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289280 prefixEnd_3289280 := by exact prefixLift 3289280
  have htrace : WordTrace (prefixWord ++ tailWord_3289280) baseStart_3289280 baseEnd_3289280 := by
    simpa [prefixWord, tailWord_3289280, baseEnd_3289280] using wordTrace_append hprefix tailTrace_3289280
  have hstable : (prefixWord ++ tailWord_3289280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289280).length < 2 ^ (prefixWord ++ tailWord_3289280).sum := by decide
  have hdescent : baseEnd_3289280 < baseStart_3289280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289301 : List Nat := [1, 3, 2, 4, 2, 2, 2, 2, 4]
def baseStart_3289301 : Nat := 118140960795 + 3289301 * 2 ^ 59
def prefixEnd_3289301 : Nat := 4983230072969 + 3 ^ 40 * 3289301 * 2
def baseEnd_3289301 : Nat := 375331651181053406313397

theorem tailTrace_3289301 : CollatzResearch.WordTrace tailWord_3289301 prefixEnd_3289301 375331651181053406313397 := by
  unfold tailWord_3289301
  simp only [CollatzResearch.WordTrace]
  refine ⟨119970663456431719731283757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79980442304287813154189171 119970663456431719731283757)
  ·
    refine ⟨44988998796161894899231409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119970663456431719731283757 44988998796161894899231409)
    ·
      refine ⟨33741749097121421174423557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44988998796161894899231409 33741749097121421174423557)
      ·
        refine ⟨6326577955710266470204417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33741749097121421174423557 6326577955710266470204417)
        ·
          refine ⟨4744933466782699852653313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6326577955710266470204417 4744933466782699852653313)
          ·
            refine ⟨3558700100087024889489985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4744933466782699852653313 3558700100087024889489985)
            ·
              refine ⟨2669025075065268667117489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3558700100087024889489985 2669025075065268667117489)
              ·
                refine ⟨2001768806298951500338117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669025075065268667117489 2001768806298951500338117)
                ·
                  refine ⟨375331651181053406313397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001768806298951500338117 375331651181053406313397)
                  ·
                    rfl

theorem cell22_3289301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_3289301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289301 prefixEnd_3289301 := by exact prefixLift 3289301
  have htrace : WordTrace (prefixWord ++ tailWord_3289301) baseStart_3289301 baseEnd_3289301 := by
    simpa [prefixWord, tailWord_3289301, baseEnd_3289301] using wordTrace_append hprefix tailTrace_3289301
  have hstable : (prefixWord ++ tailWord_3289301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289301).length < 2 ^ (prefixWord ++ tailWord_3289301).sum := by decide
  have hdescent : baseEnd_3289301 < baseStart_3289301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289327 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 3, 3]
def baseStart_3289327 : Nat := 118140960795 + 3289327 * 2 ^ 59
def prefixEnd_3289327 : Nat := 4983230072969 + 3 ^ 40 * 3289327 * 2
def baseEnd_3289327 : Nat := 1126003853874504817790111

theorem tailTrace_3289327 : CollatzResearch.WordTrace tailWord_3289327 prefixEnd_3289327 1126003853874504817790111 := by
  unfold tailWord_3289327
  simp only [CollatzResearch.WordTrace]
  refine ⟨119971611754337526171730235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79981074502891684114486823 119971611754337526171730235)
  ·
    refine ⟨179957417631506289257595353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119971611754337526171730235 179957417631506289257595353)
    ·
      refine ⟨134968063223629716943196515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179957417631506289257595353 134968063223629716943196515)
      ·
        refine ⟨202452094835444575414794773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134968063223629716943196515 202452094835444575414794773)
        ·
          refine ⟨9489941945411464472568505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202452094835444575414794773 9489941945411464472568505)
          ·
            refine ⟨7117456459058598354426379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9489941945411464472568505 7117456459058598354426379)
            ·
              refine ⟨10676184688587897531639569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117456459058598354426379 10676184688587897531639569)
              ·
                refine ⟨8007138516440923148729677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10676184688587897531639569 8007138516440923148729677)
                ·
                  refine ⟨3002676943665346180773629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8007138516440923148729677 3002676943665346180773629)
                  ·
                    refine ⟨1126003853874504817790111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002676943665346180773629 1126003853874504817790111)
                    ·
                      rfl

theorem cell22_3289327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_3289327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289327 prefixEnd_3289327 := by exact prefixLift 3289327
  have htrace : WordTrace (prefixWord ++ tailWord_3289327) baseStart_3289327 baseEnd_3289327 := by
    simpa [prefixWord, tailWord_3289327, baseEnd_3289327] using wordTrace_append hprefix tailTrace_3289327
  have hstable : (prefixWord ++ tailWord_3289327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289327).length < 2 ^ (prefixWord ++ tailWord_3289327).sum := by decide
  have hdescent : baseEnd_3289327 < baseStart_3289327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289400 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_3289400 : Nat := 118140960795 + 3289400 * 2 ^ 59
def prefixEnd_3289400 : Nat := 4983230072969 + 3 ^ 40 * 3289400 * 2
def baseEnd_3289400 : Nat := 1126028843266356960714887

theorem tailTrace_3289400 : CollatzResearch.WordTrace tailWord_3289400 prefixEnd_3289400 1126028843266356960714887 := by
  unfold tailWord_3289400
  simp only [CollatzResearch.WordTrace]
  refine ⟨59987137141536529819568827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79982849522048706426091769 59987137141536529819568827)
  ·
    refine ⟨89980705712304794729353241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59987137141536529819568827 89980705712304794729353241)
    ·
      refine ⟨67485529284228596047014931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89980705712304794729353241 67485529284228596047014931)
      ·
        refine ⟨101228293926342894070522397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67485529284228596047014931 101228293926342894070522397)
        ·
          refine ⟨37960610222378585276445899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101228293926342894070522397 37960610222378585276445899)
          ·
            refine ⟨56940915333567877914668849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37960610222378585276445899 56940915333567877914668849)
            ·
              refine ⟨42705686500175908436001637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56940915333567877914668849 42705686500175908436001637)
              ·
                refine ⟨8007316218782982831750307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42705686500175908436001637 8007316218782982831750307)
                ·
                  refine ⟨12010974328174474247625461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8007316218782982831750307 12010974328174474247625461)
                  ·
                    refine ⟨1126028843266356960714887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12010974328174474247625461 1126028843266356960714887)
                    ·
                      rfl

theorem cell22_3289400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_3289400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289400 prefixEnd_3289400 := by exact prefixLift 3289400
  have htrace : WordTrace (prefixWord ++ tailWord_3289400) baseStart_3289400 baseEnd_3289400 := by
    simpa [prefixWord, tailWord_3289400, baseEnd_3289400] using wordTrace_append hprefix tailTrace_3289400
  have hstable : (prefixWord ++ tailWord_3289400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289400).length < 2 ^ (prefixWord ++ tailWord_3289400).sum := by decide
  have hdescent : baseEnd_3289400 < baseStart_3289400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289417 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 2, 3]
def baseStart_3289417 : Nat := 118140960795 + 3289417 * 2 ^ 59
def prefixEnd_3289417 : Nat := 4983230072969 + 3 ^ 40 * 3289417 * 2
def baseEnd_3289417 : Nat := 1126034662713774583039835

theorem tailTrace_3289417 : CollatzResearch.WordTrace tailWord_3289417 prefixEnd_3289417 1126034662713774583039835 := by
  unfold tailWord_3289417
  simp only [CollatzResearch.WordTrace]
  refine ⟨119974894324011471542506505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79983262882674314361671003 119974894324011471542506505)
  ·
    refine ⟨89981170743008603656879879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119974894324011471542506505 89981170743008603656879879)
    ·
      refine ⟨134971756114512905485319819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89981170743008603656879879 134971756114512905485319819)
      ·
        refine ⟨202457634171769358227979729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134971756114512905485319819 202457634171769358227979729)
        ·
          refine ⟨151843225628827018670984797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202457634171769358227979729 151843225628827018670984797)
          ·
            refine ⟨56941209610810132001619299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151843225628827018670984797 56941209610810132001619299)
            ·
              refine ⟨85411814416215198002428949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56941209610810132001619299 85411814416215198002428949)
              ·
                refine ⟨4003678800760087406363857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85411814416215198002428949 4003678800760087406363857)
                ·
                  refine ⟨3002759100570065554772893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4003678800760087406363857 3002759100570065554772893)
                  ·
                    refine ⟨1126034662713774583039835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002759100570065554772893 1126034662713774583039835)
                    ·
                      rfl

theorem cell22_3289417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_3289417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289417 prefixEnd_3289417 := by exact prefixLift 3289417
  have htrace : WordTrace (prefixWord ++ tailWord_3289417) baseStart_3289417 baseEnd_3289417 := by
    simpa [prefixWord, tailWord_3289417, baseEnd_3289417] using wordTrace_append hprefix tailTrace_3289417
  have hstable : (prefixWord ++ tailWord_3289417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289417).length < 2 ^ (prefixWord ++ tailWord_3289417).sum := by decide
  have hdescent : baseEnd_3289417 < baseStart_3289417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289535 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 9]
def baseStart_3289535 : Nat := 118140960795 + 3289535 * 2 ^ 59
def prefixEnd_3289535 : Nat := 4983230072969 + 3 ^ 40 * 3289535 * 2
def baseEnd_3289535 : Nat := 1126075056525261608589473

theorem tailTrace_3289535 : CollatzResearch.WordTrace tailWord_3289535 prefixEnd_3289535 1126075056525261608589473 := by
  unfold tailWord_3289535
  simp only [CollatzResearch.WordTrace]
  refine ⟨119979198137583977695302059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79986132091722651796868039 119979198137583977695302059)
  ·
    refine ⟨179968797206375966542953089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119979198137583977695302059 179968797206375966542953089)
    ·
      refine ⟨134976597904781974907214817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179968797206375966542953089 134976597904781974907214817)
      ·
        refine ⟨101232448428586481180411113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134976597904781974907214817 101232448428586481180411113)
        ·
          refine ⟨75924336321439860885308335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101232448428586481180411113 75924336321439860885308335)
          ·
            refine ⟨113886504482159791327962503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75924336321439860885308335 113886504482159791327962503)
            ·
              refine ⟨170829756723239686991943755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113886504482159791327962503 170829756723239686991943755)
              ·
                refine ⟨256244635084859530487915633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170829756723239686991943755 256244635084859530487915633)
                ·
                  refine ⟨192183476313644647865936725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256244635084859530487915633 192183476313644647865936725)
                  ·
                    refine ⟨1126075056525261608589473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192183476313644647865936725 1126075056525261608589473)
                    ·
                      rfl

theorem cell22_3289535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_3289535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289535 prefixEnd_3289535 := by exact prefixLift 3289535
  have htrace : WordTrace (prefixWord ++ tailWord_3289535) baseStart_3289535 baseEnd_3289535 := by
    simpa [prefixWord, tailWord_3289535, baseEnd_3289535] using wordTrace_append hprefix tailTrace_3289535
  have hstable : (prefixWord ++ tailWord_3289535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289535).length < 2 ^ (prefixWord ++ tailWord_3289535).sum := by decide
  have hdescent : baseEnd_3289535 < baseStart_3289535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289552 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 8, 3]
def baseStart_3289552 : Nat := 118140960795 + 3289552 * 2 ^ 59
def prefixEnd_3289552 : Nat := 4983230072969 + 3 ^ 40 * 3289552 * 2
def baseEnd_3289552 : Nat := 1126080875972679230914421

theorem tailTrace_3289552 : CollatzResearch.WordTrace tailWord_3289552 prefixEnd_3289552 1126080875972679230914421 := by
  unfold tailWord_3289552
  simp only [CollatzResearch.WordTrace]
  refine ⟨59989909089261194799335455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79986545452348259732447273 59989909089261194799335455)
  ·
    refine ⟨89984863633891792199003183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59989909089261194799335455 89984863633891792199003183)
    ·
      refine ⟨134977295450837688298504775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89984863633891792199003183 134977295450837688298504775)
      ·
        refine ⟨202465943176256532447757163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134977295450837688298504775 202465943176256532447757163)
        ·
          refine ⟨303698914764384798671635745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202465943176256532447757163 303698914764384798671635745)
          ·
            refine ⟨227774186073288599003726809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303698914764384798671635745 227774186073288599003726809)
            ·
              refine ⟨170830639554966449252795107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227774186073288599003726809 170830639554966449252795107)
              ·
                refine ⟨256245959332449673879192661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170830639554966449252795107 256245959332449673879192661)
                ·
                  refine ⟨3002882335927144615771789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 256245959332449673879192661 3002882335927144615771789)
                  ·
                    refine ⟨1126080875972679230914421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002882335927144615771789 1126080875972679230914421)
                    ·
                      rfl

theorem cell22_3289552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_3289552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289552 prefixEnd_3289552 := by exact prefixLift 3289552
  have htrace : WordTrace (prefixWord ++ tailWord_3289552) baseStart_3289552 baseEnd_3289552 := by
    simpa [prefixWord, tailWord_3289552, baseEnd_3289552] using wordTrace_append hprefix tailTrace_3289552
  have hstable : (prefixWord ++ tailWord_3289552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289552).length < 2 ^ (prefixWord ++ tailWord_3289552).sum := by decide
  have hdescent : baseEnd_3289552 < baseStart_3289552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289556 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3289556 : Nat := 118140960795 + 3289556 * 2 ^ 59
def prefixEnd_3289556 : Nat := 4983230072969 + 3 ^ 40 * 3289556 * 2
def baseEnd_3289556 : Nat := 1126082245254424553814409

theorem tailTrace_3289556 : CollatzResearch.WordTrace tailWord_3289556 prefixEnd_3289556 1126082245254424553814409 := by
  unfold tailWord_3289556
  simp only [CollatzResearch.WordTrace]
  refine ⟨59989982035253949140908261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79986642713671932187877681 59989982035253949140908261)
  ·
    refine ⟨11248121631610115463920299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59989982035253949140908261 11248121631610115463920299)
    ·
      refine ⟨16872182447415173195880449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11248121631610115463920299 16872182447415173195880449)
      ·
        refine ⟨12654136835561379896910337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16872182447415173195880449 12654136835561379896910337)
        ·
          refine ⟨9490602626671034922682753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12654136835561379896910337 9490602626671034922682753)
          ·
            refine ⟨7117951970003276192012065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9490602626671034922682753 7117951970003276192012065)
            ·
              refine ⟨5338463977502457144009049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7117951970003276192012065 5338463977502457144009049)
              ·
                refine ⟨4003847983126842858006787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338463977502457144009049 4003847983126842858006787)
                ·
                  refine ⟨6005771974690264287010181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003847983126842858006787 6005771974690264287010181)
                  ·
                    refine ⟨1126082245254424553814409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005771974690264287010181 1126082245254424553814409)
                    ·
                      rfl

theorem cell22_3289556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3289556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289556 prefixEnd_3289556 := by exact prefixLift 3289556
  have htrace : WordTrace (prefixWord ++ tailWord_3289556) baseStart_3289556 baseEnd_3289556 := by
    simpa [prefixWord, tailWord_3289556, baseEnd_3289556] using wordTrace_append hprefix tailTrace_3289556
  have hstable : (prefixWord ++ tailWord_3289556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289556).length < 2 ^ (prefixWord ++ tailWord_3289556).sum := by decide
  have hdescent : baseEnd_3289556 < baseStart_3289556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289567 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 1, 6]
def baseStart_3289567 : Nat := 118140960795 + 3289567 * 2 ^ 59
def prefixEnd_3289567 : Nat := 4983230072969 + 3 ^ 40 * 3289567 * 2
def baseEnd_3289567 : Nat := 1126086010779224191789375

theorem tailTrace_3289567 : CollatzResearch.WordTrace tailWord_3289567 prefixEnd_3289567 1126086010779224191789375 := by
  unfold tailWord_3289567
  simp only [CollatzResearch.WordTrace]
  refine ⟨119980365273468047160466955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79986910182312031440311303 119980365273468047160466955)
  ·
    refine ⟨179970547910202070740700433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119980365273468047160466955 179970547910202070740700433)
    ·
      refine ⟨134977910932651553055525325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179970547910202070740700433 134977910932651553055525325)
      ·
        refine ⟨50616716599744332395821997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134977910932651553055525325 50616716599744332395821997)
        ·
          refine ⟨18981268724904124648433249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50616716599744332395821997 18981268724904124648433249)
          ·
            refine ⟨14235951543678093486324937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18981268724904124648433249 14235951543678093486324937)
            ·
              refine ⟨10676963657758570114743703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14235951543678093486324937 10676963657758570114743703)
              ·
                refine ⟨16015445486637855172115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10676963657758570114743703 16015445486637855172115555)
                ·
                  refine ⟨24023168229956782758173333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16015445486637855172115555 24023168229956782758173333)
                  ·
                    refine ⟨1126086010779224191789375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24023168229956782758173333 1126086010779224191789375)
                    ·
                      rfl

theorem cell22_3289567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_3289567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289567 prefixEnd_3289567 := by exact prefixLift 3289567
  have htrace : WordTrace (prefixWord ++ tailWord_3289567) baseStart_3289567 baseEnd_3289567 := by
    simpa [prefixWord, tailWord_3289567, baseEnd_3289567] using wordTrace_append hprefix tailTrace_3289567
  have hstable : (prefixWord ++ tailWord_3289567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289567).length < 2 ^ (prefixWord ++ tailWord_3289567).sum := by decide
  have hdescent : baseEnd_3289567 < baseStart_3289567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289582 : List Nat := [4, 1, 2, 1, 2, 2, 10]
def baseStart_3289582 : Nat := 118140960795 + 3289582 * 2 ^ 59
def prefixEnd_3289582 : Nat := 4983230072969 + 3 ^ 40 * 3289582 * 2
def baseEnd_3289582 : Nat := 41707079466139598246827

theorem tailTrace_3289582 : CollatzResearch.WordTrace tailWord_3289582 prefixEnd_3289582 41707079466139598246827 := by
  unfold tailWord_3289582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997614046051713090282875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79987274912275803148175333 14997614046051713090282875)
  ·
    refine ⟨22496421069077569635424313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14997614046051713090282875 22496421069077569635424313)
    ·
      refine ⟨16872315801808177226568235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22496421069077569635424313 16872315801808177226568235)
      ·
        refine ⟨25308473702712265839852353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16872315801808177226568235 25308473702712265839852353)
        ·
          refine ⟨18981355277034199379889265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25308473702712265839852353 18981355277034199379889265)
          ·
            refine ⟨14236016457775649534916949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18981355277034199379889265 14236016457775649534916949)
            ·
              refine ⟨41707079466139598246827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14236016457775649534916949 41707079466139598246827)
              ·
                rfl

theorem cell22_3289582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 10].length) (baseStart_3289582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289582 prefixEnd_3289582 := by exact prefixLift 3289582
  have htrace : WordTrace (prefixWord ++ tailWord_3289582) baseStart_3289582 baseEnd_3289582 := by
    simpa [prefixWord, tailWord_3289582, baseEnd_3289582] using wordTrace_append hprefix tailTrace_3289582
  have hstable : (prefixWord ++ tailWord_3289582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289582).length < 2 ^ (prefixWord ++ tailWord_3289582).sum := by decide
  have hdescent : baseEnd_3289582 < baseStart_3289582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289631 : List Nat := [1, 1, 2, 4, 1, 1, 1, 7, 1, 3]
def baseStart_3289631 : Nat := 118140960795 + 3289631 * 2 ^ 59
def prefixEnd_3289631 : Nat := 4983230072969 + 3 ^ 40 * 3289631 * 2
def baseEnd_3289631 : Nat := 1126107919287149358189179

theorem tailTrace_3289631 : CollatzResearch.WordTrace tailWord_3289631 prefixEnd_3289631 1126107919287149358189179 := by
  unfold tailWord_3289631
  simp only [CollatzResearch.WordTrace]
  refine ⟨119982699545236186090796747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79988466363490790727197831 119982699545236186090796747)
  ·
    refine ⟨179974049317854279136195121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119982699545236186090796747 179974049317854279136195121)
    ·
      refine ⟨134980536988390709352146341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179974049317854279136195121 134980536988390709352146341)
      ·
        refine ⟨25308850685323258003527439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134980536988390709352146341 25308850685323258003527439)
        ·
          refine ⟨37963276027984887005291159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25308850685323258003527439 37963276027984887005291159)
          ·
            refine ⟨56944914041977330507936739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37963276027984887005291159 56944914041977330507936739)
            ·
              refine ⟨85417371062965995761905109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56944914041977330507936739 85417371062965995761905109)
              ·
                refine ⟨2001969634288265525669651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85417371062965995761905109 2001969634288265525669651)
                ·
                  refine ⟨3002954451432398288504477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001969634288265525669651 3002954451432398288504477)
                  ·
                    refine ⟨1126107919287149358189179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002954451432398288504477 1126107919287149358189179)
                    ·
                      rfl

theorem cell22_3289631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 3].length) (baseStart_3289631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289631 prefixEnd_3289631 := by exact prefixLift 3289631
  have htrace : WordTrace (prefixWord ++ tailWord_3289631) baseStart_3289631 baseEnd_3289631 := by
    simpa [prefixWord, tailWord_3289631, baseEnd_3289631] using wordTrace_append hprefix tailTrace_3289631
  have hstable : (prefixWord ++ tailWord_3289631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289631).length < 2 ^ (prefixWord ++ tailWord_3289631).sum := by decide
  have hdescent : baseEnd_3289631 < baseStart_3289631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289648 : List Nat := [2, 1, 1, 1, 2, 3, 6, 2, 1, 3]
def baseStart_3289648 : Nat := 118140960795 + 3289648 * 2 ^ 59
def prefixEnd_3289648 : Nat := 4983230072969 + 3 ^ 40 * 3289648 * 2
def baseEnd_3289648 : Nat := 1126113738734566980514127

theorem tailTrace_3289648 : CollatzResearch.WordTrace tailWord_3289648 prefixEnd_3289648 1126113738734566980514127 := by
  unfold tailWord_3289648
  simp only [CollatzResearch.WordTrace]
  refine ⟨59991659793087298997082799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79988879724116398662777065 59991659793087298997082799)
  ·
    refine ⟨89987489689630948495624199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59991659793087298997082799 89987489689630948495624199)
    ·
      refine ⟨134981234534446422743436299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89987489689630948495624199 134981234534446422743436299)
      ·
        refine ⟨202471851801669634115154449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134981234534446422743436299 202471851801669634115154449)
        ·
          refine ⟨151853888851252225586365837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202471851801669634115154449 151853888851252225586365837)
          ·
            refine ⟨56945208319219584594887189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151853888851252225586365837 56945208319219584594887189)
            ·
              refine ⟨2669306639963418027885337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56945208319219584594887189 2669306639963418027885337)
              ·
                refine ⟨2001979979972563520914003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669306639963418027885337 2001979979972563520914003)
                ·
                  refine ⟨3002969969958845281371005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001979979972563520914003 3002969969958845281371005)
                  ·
                    refine ⟨1126113738734566980514127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002969969958845281371005 1126113738734566980514127)
                    ·
                      rfl

theorem cell22_3289648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 3].length) (baseStart_3289648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289648 prefixEnd_3289648 := by exact prefixLift 3289648
  have htrace : WordTrace (prefixWord ++ tailWord_3289648) baseStart_3289648 baseEnd_3289648 := by
    simpa [prefixWord, tailWord_3289648, baseEnd_3289648] using wordTrace_append hprefix tailTrace_3289648
  have hstable : (prefixWord ++ tailWord_3289648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289648).length < 2 ^ (prefixWord ++ tailWord_3289648).sum := by decide
  have hdescent : baseEnd_3289648 < baseStart_3289648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289674 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_3289674 : Nat := 118140960795 + 3289674 * 2 ^ 59
def prefixEnd_3289674 : Nat := 4983230072969 + 3 ^ 40 * 3289674 * 2
def baseEnd_3289674 : Nat := 1126122639065911579364047

theorem tailTrace_3289674 : CollatzResearch.WordTrace tailWord_3289674 prefixEnd_3289674 1126122639065911579364047 := by
  unfold tailWord_3289674
  simp only [CollatzResearch.WordTrace]
  refine ⟨29996066971020101108653019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79989511922720269623074717 29996066971020101108653019)
  ·
    refine ⟨44994100456530151662979529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29996066971020101108653019 44994100456530151662979529)
    ·
      refine ⟨33745575342397613747234647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44994100456530151662979529 33745575342397613747234647)
      ·
        refine ⟨50618363013596420620851971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33745575342397613747234647 50618363013596420620851971)
        ·
          refine ⟨75927544520394630931277957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50618363013596420620851971 75927544520394630931277957)
          ·
            refine ⟨14236414597573993299614617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75927544520394630931277957 14236414597573993299614617)
            ·
              refine ⟨10677310948180494974710963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14236414597573993299614617 10677310948180494974710963)
              ·
                refine ⟨16015966422270742462066445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10677310948180494974710963 16015966422270742462066445)
                ·
                  refine ⟨6005987408351528423274917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16015966422270742462066445 6005987408351528423274917)
                  ·
                    refine ⟨1126122639065911579364047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005987408351528423274917 1126122639065911579364047)
                    ·
                      rfl

theorem cell22_3289674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_3289674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289674 prefixEnd_3289674 := by exact prefixLift 3289674
  have htrace : WordTrace (prefixWord ++ tailWord_3289674) baseStart_3289674 baseEnd_3289674 := by
    simpa [prefixWord, tailWord_3289674, baseEnd_3289674] using wordTrace_append hprefix tailTrace_3289674
  have hstable : (prefixWord ++ tailWord_3289674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289674).length < 2 ^ (prefixWord ++ tailWord_3289674).sum := by decide
  have hdescent : baseEnd_3289674 < baseStart_3289674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289706 : List Nat := [3, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_3289706 : Nat := 118140960795 + 3289706 * 2 ^ 59
def prefixEnd_3289706 : Nat := 4983230072969 + 3 ^ 40 * 3289706 * 2
def baseEnd_3289706 : Nat := 375377864439958054187983

theorem tailTrace_3289706 : CollatzResearch.WordTrace tailWord_3289706 prefixEnd_3289706 375377864439958054187983 := by
  unfold tailWord_3289706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29996358754991118474944243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79990290013309649266517981 29996358754991118474944243)
  ·
    refine ⟨44994538132486677712416365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29996358754991118474944243 44994538132486677712416365)
    ·
      refine ⟨16872951799682504142156137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44994538132486677712416365 16872951799682504142156137)
      ·
        refine ⟨12654713849761878106617103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16872951799682504142156137 12654713849761878106617103)
        ·
          refine ⟨18982070774642817159925655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12654713849761878106617103 18982070774642817159925655)
          ·
            refine ⟨28473106161964225739888483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18982070774642817159925655 28473106161964225739888483)
            ·
              refine ⟨42709659242946338609832725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28473106161964225739888483 42709659242946338609832725)
              ·
                refine ⟨2002015277013109622335909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42709659242946338609832725 2002015277013109622335909)
                ·
                  refine ⟨375377864439958054187983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002015277013109622335909 375377864439958054187983)
                  ·
                    rfl

theorem cell22_3289706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_3289706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289706 prefixEnd_3289706 := by exact prefixLift 3289706
  have htrace : WordTrace (prefixWord ++ tailWord_3289706) baseStart_3289706 baseEnd_3289706 := by
    simpa [prefixWord, tailWord_3289706, baseEnd_3289706] using wordTrace_append hprefix tailTrace_3289706
  have hstable : (prefixWord ++ tailWord_3289706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289706).length < 2 ^ (prefixWord ++ tailWord_3289706).sum := by decide
  have hdescent : baseEnd_3289706 < baseStart_3289706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289721 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 1, 5]
def baseStart_3289721 : Nat := 118140960795 + 3289721 * 2 ^ 59
def prefixEnd_3289721 : Nat := 4983230072969 + 3 ^ 40 * 3289721 * 2
def baseEnd_3289721 : Nat := 1126138728126419123438903

theorem tailTrace_3289721 : CollatzResearch.WordTrace tailWord_3289721 prefixEnd_3289721 1126138728126419123438903 := by
  unfold tailWord_3289721
  simp only [CollatzResearch.WordTrace]
  refine ⟨119985982114910131461573017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79990654743273420974382011 119985982114910131461573017)
  ·
    refine ⟨89989486586182598596179763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119985982114910131461573017 89989486586182598596179763)
    ·
      refine ⟨134984229879273897894269645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89989486586182598596179763 134984229879273897894269645)
      ·
        refine ⟨50619086204727711710351117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134984229879273897894269645 50619086204727711710351117)
        ·
          refine ⟨18982157326772891891381669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50619086204727711710351117 18982157326772891891381669)
          ·
            refine ⟨3559154498769917229634063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18982157326772891891381669 3559154498769917229634063)
            ·
              refine ⟨5338731748154875844451095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559154498769917229634063 5338731748154875844451095)
              ·
                refine ⟨8008097622232313766676643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5338731748154875844451095 8008097622232313766676643)
                ·
                  refine ⟨12012146433348470650014965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8008097622232313766676643 12012146433348470650014965)
                  ·
                    refine ⟨1126138728126419123438903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12012146433348470650014965 1126138728126419123438903)
                    ·
                      rfl

theorem cell22_3289721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_3289721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289721 prefixEnd_3289721 := by exact prefixLift 3289721
  have htrace : WordTrace (prefixWord ++ tailWord_3289721) baseStart_3289721 baseEnd_3289721 := by
    simpa [prefixWord, tailWord_3289721, baseEnd_3289721] using wordTrace_append hprefix tailTrace_3289721
  have hstable : (prefixWord ++ tailWord_3289721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289721).length < 2 ^ (prefixWord ++ tailWord_3289721).sum := by decide
  have hdescent : baseEnd_3289721 < baseStart_3289721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289764 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_3289764 : Nat := 118140960795 + 3289764 * 2 ^ 59
def prefixEnd_3289764 : Nat := 4983230072969 + 3 ^ 40 * 3289764 * 2
def baseEnd_3289764 : Nat := 1126153447905181344613771

theorem tailTrace_3289764 : CollatzResearch.WordTrace tailWord_3289764 prefixEnd_3289764 1126153447905181344613771 := by
  unfold tailWord_3289764
  simp only [CollatzResearch.WordTrace]
  refine ⟨59993775226877174902694173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79991700302502899870258897 59993775226877174902694173)
  ·
    refine ⟨22497665710078940588510315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59993775226877174902694173 22497665710078940588510315)
    ·
      refine ⟨33746498565118410882765473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22497665710078940588510315 33746498565118410882765473)
      ·
        refine ⟨25309873923838808162074105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33746498565118410882765473 25309873923838808162074105)
        ·
          refine ⟨18982405442879106121555579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25309873923838808162074105 18982405442879106121555579)
          ·
            refine ⟨28473608164318659182333369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18982405442879106121555579 28473608164318659182333369)
            ·
              refine ⟨21355206123238994386750027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28473608164318659182333369 21355206123238994386750027)
              ·
                refine ⟨32032809184858491580125041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21355206123238994386750027 32032809184858491580125041)
                ·
                  refine ⟨24024606888643868685093781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32032809184858491580125041 24024606888643868685093781)
                  ·
                    refine ⟨1126153447905181344613771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24024606888643868685093781 1126153447905181344613771)
                    ·
                      rfl

theorem cell22_3289764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_3289764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289764 prefixEnd_3289764 := by exact prefixLift 3289764
  have htrace : WordTrace (prefixWord ++ tailWord_3289764) baseStart_3289764 baseEnd_3289764 := by
    simpa [prefixWord, tailWord_3289764, baseEnd_3289764] using wordTrace_append hprefix tailTrace_3289764
  have hstable : (prefixWord ++ tailWord_3289764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289764).length < 2 ^ (prefixWord ++ tailWord_3289764).sum := by decide
  have hdescent : baseEnd_3289764 < baseStart_3289764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289824 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 6]
def baseStart_3289824 : Nat := 118140960795 + 3289824 * 2 ^ 59
def prefixEnd_3289824 : Nat := 4983230072969 + 3 ^ 40 * 3289824 * 2
def baseEnd_3289824 : Nat := 375391329043787062704529

theorem tailTrace_3289824 : CollatzResearch.WordTrace tailWord_3289824 prefixEnd_3289824 375391329043787062704529 := by
  unfold tailWord_3289824
  simp only [CollatzResearch.WordTrace]
  refine ⟨59994869416768490026286263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79993159222357986701715017 59994869416768490026286263)
  ·
    refine ⟨89992304125152735039429395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59994869416768490026286263 89992304125152735039429395)
    ·
      refine ⟨134988456187729102559144093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89992304125152735039429395 134988456187729102559144093)
      ·
        refine ⟨50620671070398413459679035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134988456187729102559144093 50620671070398413459679035)
        ·
          refine ⟨75931006605597620189518553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50620671070398413459679035 75931006605597620189518553)
          ·
            refine ⟨56948254954198215142138915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75931006605597620189518553 56948254954198215142138915)
            ·
              refine ⟨85422382431297322713208373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56948254954198215142138915 85422382431297322713208373)
              ·
                refine ⟨8008348352934124004363285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85422382431297322713208373 8008348352934124004363285)
                ·
                  refine ⟨375391329043787062704529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8008348352934124004363285 375391329043787062704529)
                  ·
                    rfl

theorem cell22_3289824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_3289824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289824 prefixEnd_3289824 := by exact prefixLift 3289824
  have htrace : WordTrace (prefixWord ++ tailWord_3289824) baseStart_3289824 baseEnd_3289824 := by
    simpa [prefixWord, tailWord_3289824, baseEnd_3289824] using wordTrace_append hprefix tailTrace_3289824
  have hstable : (prefixWord ++ tailWord_3289824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289824).length < 2 ^ (prefixWord ++ tailWord_3289824).sum := by decide
  have hdescent : baseEnd_3289824 < baseStart_3289824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289873 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 2, 3]
def baseStart_3289873 : Nat := 118140960795 + 3289873 * 2 ^ 59
def prefixEnd_3289873 : Nat := 4983230072969 + 3 ^ 40 * 3289873 * 2
def baseEnd_3289873 : Nat := 1126190760832741393638437

theorem tailTrace_3289873 : CollatzResearch.WordTrace tailWord_3289873 prefixEnd_3289873 1126190760832741393638437 := by
  unfold tailWord_3289873
  simp only [CollatzResearch.WordTrace]
  refine ⟨119991526010359461421106273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79994350673572974280737515 119991526010359461421106273)
  ·
    refine ⟨89993644507769596065829705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119991526010359461421106273 89993644507769596065829705)
    ·
      refine ⟨67495233380827197049372279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89993644507769596065829705 67495233380827197049372279)
      ·
        refine ⟨101242850071240795574058419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67495233380827197049372279 101242850071240795574058419)
        ·
          refine ⟨151864275106861193361087629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101242850071240795574058419 151864275106861193361087629)
          ·
            refine ⟨56949103165072947510407861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151864275106861193361087629 56949103165072947510407861)
            ·
              refine ⟨5338978421725588829100737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56949103165072947510407861 5338978421725588829100737)
              ·
                refine ⟨4004233816294191621825553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338978421725588829100737 4004233816294191621825553)
                ·
                  refine ⟨3003175362220643716369165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4004233816294191621825553 3003175362220643716369165)
                  ·
                    refine ⟨1126190760832741393638437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3003175362220643716369165 1126190760832741393638437)
                    ·
                      rfl

theorem cell22_3289873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_3289873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289873 prefixEnd_3289873 := by exact prefixLift 3289873
  have htrace : WordTrace (prefixWord ++ tailWord_3289873) baseStart_3289873 baseEnd_3289873 := by
    simpa [prefixWord, tailWord_3289873, baseEnd_3289873] using wordTrace_append hprefix tailTrace_3289873
  have hstable : (prefixWord ++ tailWord_3289873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289873).length < 2 ^ (prefixWord ++ tailWord_3289873).sum := by decide
  have hdescent : baseEnd_3289873 < baseStart_3289873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289899 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 4, 6]
def baseStart_3289899 : Nat := 118140960795 + 3289899 * 2 ^ 59
def prefixEnd_3289899 : Nat := 4983230072969 + 3 ^ 40 * 3289899 * 2
def baseEnd_3289899 : Nat := 1126199661164085992488357

theorem tailTrace_3289899 : CollatzResearch.WordTrace tailWord_3289899 prefixEnd_3289899 1126199661164085992488357 := by
  unfold tailWord_3289899
  simp only [CollatzResearch.WordTrace]
  refine ⟨119992474308265267861552751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79994982872176845241035167 119992474308265267861552751)
  ·
    refine ⟨179988711462397901792329127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119992474308265267861552751 179988711462397901792329127)
    ·
      refine ⟨269983067193596852688493691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179988711462397901792329127 269983067193596852688493691)
      ·
        refine ⟨404974600790395279032740537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269983067193596852688493691 404974600790395279032740537)
        ·
          refine ⟨303730950592796459274555403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404974600790395279032740537 303730950592796459274555403)
          ·
            refine ⟨455596425889194688911833105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303730950592796459274555403 455596425889194688911833105)
            ·
              refine ⟨341697319416896016683874829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455596425889194688911833105 341697319416896016683874829)
              ·
                refine ⟨128136494781336006256453061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341697319416896016683874829 128136494781336006256453061)
                ·
                  refine ⟨24025592771500501173084949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128136494781336006256453061 24025592771500501173084949)
                  ·
                    refine ⟨1126199661164085992488357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24025592771500501173084949 1126199661164085992488357)
                    ·
                      rfl

theorem cell22_3289899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_3289899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289899 prefixEnd_3289899 := by exact prefixLift 3289899
  have htrace : WordTrace (prefixWord ++ tailWord_3289899) baseStart_3289899 baseEnd_3289899 := by
    simpa [prefixWord, tailWord_3289899, baseEnd_3289899] using wordTrace_append hprefix tailTrace_3289899
  have hstable : (prefixWord ++ tailWord_3289899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289899).length < 2 ^ (prefixWord ++ tailWord_3289899).sum := by decide
  have hdescent : baseEnd_3289899 < baseStart_3289899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289982 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_3289982 : Nat := 118140960795 + 3289982 * 2 ^ 59
def prefixEnd_3289982 : Nat := 4983230072969 + 3 ^ 40 * 3289982 * 2
def baseEnd_3289982 : Nat := 375409357920100480887701

theorem tailTrace_3289982 : CollatzResearch.WordTrace tailWord_3289982 prefixEnd_3289982 375409357920100480887701 := by
  unfold tailWord_3289982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14999437695870571629603025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79997001044643048691216133 14999437695870571629603025)
  ·
    refine ⟨11249578271902928722202269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14999437695870571629603025 11249578271902928722202269)
    ·
      refine ⟨4218591851963598270825851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11249578271902928722202269 4218591851963598270825851)
      ·
        refine ⟨6327887777945397406238777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218591851963598270825851 6327887777945397406238777)
        ·
          refine ⟨4745915833459048054679083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6327887777945397406238777 4745915833459048054679083)
          ·
            refine ⟨7118873750188572082018625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745915833459048054679083 7118873750188572082018625)
            ·
              refine ⟨5339155312641429061513969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7118873750188572082018625 5339155312641429061513969)
              ·
                refine ⟨4004366484481071796135477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339155312641429061513969 4004366484481071796135477)
                ·
                  refine ⟨375409357920100480887701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4004366484481071796135477 375409357920100480887701)
                  ·
                    rfl

theorem cell22_3289982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_3289982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289982 prefixEnd_3289982 := by exact prefixLift 3289982
  have htrace : WordTrace (prefixWord ++ tailWord_3289982) baseStart_3289982 baseEnd_3289982 := by
    simpa [prefixWord, tailWord_3289982, baseEnd_3289982] using wordTrace_append hprefix tailTrace_3289982
  have hstable : (prefixWord ++ tailWord_3289982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289982).length < 2 ^ (prefixWord ++ tailWord_3289982).sum := by decide
  have hdescent : baseEnd_3289982 < baseStart_3289982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3289986 : List Nat := [3, 4, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3289986 : Nat := 118140960795 + 3289986 * 2 ^ 59
def prefixEnd_3289986 : Nat := 4983230072969 + 3 ^ 40 * 3289986 * 2
def baseEnd_3289986 : Nat := 1126229443042046765563091

theorem tailTrace_3289986 : CollatzResearch.WordTrace tailWord_3289986 prefixEnd_3289986 1126229443042046765563091 := by
  unfold tailWord_3289986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29998911864737520429992453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79997098305966721146646541 29998911864737520429992453)
  ·
    refine ⟨5624795974638285080623585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29998911864737520429992453 5624795974638285080623585)
    ·
      refine ⟨4218596980978713810467689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5624795974638285080623585 4218596980978713810467689)
      ·
        refine ⟨3163947735734035357850767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4218596980978713810467689 3163947735734035357850767)
        ·
          refine ⟨4745921603601053036776151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163947735734035357850767 4745921603601053036776151)
          ·
            refine ⟨7118882405401579555164227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745921603601053036776151 7118882405401579555164227)
            ·
              refine ⟨10678323608102369332746341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7118882405401579555164227 10678323608102369332746341)
              ·
                refine ⟨2002185676519194249889939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10678323608102369332746341 2002185676519194249889939)
                ·
                  refine ⟨3003278514778791374834909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002185676519194249889939 3003278514778791374834909)
                  ·
                    refine ⟨1126229443042046765563091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3003278514778791374834909 1126229443042046765563091)
                    ·
                      rfl

theorem cell22_3289986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3289986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3289986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3289986 prefixEnd_3289986 := by exact prefixLift 3289986
  have htrace : WordTrace (prefixWord ++ tailWord_3289986) baseStart_3289986 baseEnd_3289986 := by
    simpa [prefixWord, tailWord_3289986, baseEnd_3289986] using wordTrace_append hprefix tailTrace_3289986
  have hstable : (prefixWord ++ tailWord_3289986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3289986).length < 2 ^ (prefixWord ++ tailWord_3289986).sum := by decide
  have hdescent : baseEnd_3289986 < baseStart_3289986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3289986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290143 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 3, 5]
def baseStart_3290143 : Nat := 118140960795 + 3290143 * 2 ^ 59
def prefixEnd_3290143 : Nat := 4983230072969 + 3 ^ 40 * 3290143 * 2
def baseEnd_3290143 : Nat := 1126283187350550689387609

theorem tailTrace_3290143 : CollatzResearch.WordTrace tailWord_3290143 prefixEnd_3290143 1126283187350550689387609 := by
  unfold tailWord_3290143
  simp only [CollatzResearch.WordTrace]
  refine ⟨120001373719381297533435083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80000915812920865022290055 120001373719381297533435083)
  ·
    refine ⟨180002060579071946300152625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120001373719381297533435083 180002060579071946300152625)
    ·
      refine ⟨135001545434303959725114469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180002060579071946300152625 135001545434303959725114469)
      ·
        refine ⟨25312789768931992448458963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135001545434303959725114469 25312789768931992448458963)
        ·
          refine ⟨37969184653397988672688445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25312789768931992448458963 37969184653397988672688445)
          ·
            refine ⟨14238444245024245752258167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37969184653397988672688445 14238444245024245752258167)
            ·
              refine ⟨21357666367536368628387251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14238444245024245752258167 21357666367536368628387251)
              ·
                refine ⟨32036499551304552942580877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21357666367536368628387251 32036499551304552942580877)
                ·
                  refine ⟨12013687331739207353467829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32036499551304552942580877 12013687331739207353467829)
                  ·
                    refine ⟨1126283187350550689387609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12013687331739207353467829 1126283187350550689387609)
                    ·
                      rfl

theorem cell22_3290143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_3290143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290143 prefixEnd_3290143 := by exact prefixLift 3290143
  have htrace : WordTrace (prefixWord ++ tailWord_3290143) baseStart_3290143 baseEnd_3290143 := by
    simpa [prefixWord, tailWord_3290143, baseEnd_3290143] using wordTrace_append hprefix tailTrace_3290143
  have hstable : (prefixWord ++ tailWord_3290143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290143).length < 2 ^ (prefixWord ++ tailWord_3290143).sum := by decide
  have hdescent : baseEnd_3290143 < baseStart_3290143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290147 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 1, 4]
def baseStart_3290147 : Nat := 118140960795 + 3290147 * 2 ^ 59
def prefixEnd_3290147 : Nat := 4983230072969 + 3 ^ 40 * 3290147 * 2
def baseEnd_3290147 : Nat := 1126284556632296012287597

theorem tailTrace_3290147 : CollatzResearch.WordTrace tailWord_3290147 prefixEnd_3290147 1126284556632296012287597 := by
  unfold tailWord_3290147
  simp only [CollatzResearch.WordTrace]
  refine ⟨120001519611366806216580695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80001013074244537477720463 120001519611366806216580695)
  ·
    refine ⟨180002279417050209324871043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120001519611366806216580695 180002279417050209324871043)
    ·
      refine ⟨270003419125575313987306565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180002279417050209324871043 270003419125575313987306565)
      ·
        refine ⟨50625641086045371372619981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270003419125575313987306565 50625641086045371372619981)
        ·
          refine ⟨18984615407267014264732493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50625641086045371372619981 18984615407267014264732493)
          ·
            refine ⟨7119230777725130349274685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18984615407267014264732493 7119230777725130349274685)
            ·
              refine ⟨2669711541646923880978007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7119230777725130349274685 2669711541646923880978007)
              ·
                refine ⟨4004567312470385821467011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669711541646923880978007 4004567312470385821467011)
                ·
                  refine ⟨6006850968705578732200517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004567312470385821467011 6006850968705578732200517)
                  ·
                    refine ⟨1126284556632296012287597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6006850968705578732200517 1126284556632296012287597)
                    ·
                      rfl

theorem cell22_3290147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 4].length) (baseStart_3290147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290147 prefixEnd_3290147 := by exact prefixLift 3290147
  have htrace : WordTrace (prefixWord ++ tailWord_3290147) baseStart_3290147 baseEnd_3290147 := by
    simpa [prefixWord, tailWord_3290147, baseEnd_3290147] using wordTrace_append hprefix tailTrace_3290147
  have hstable : (prefixWord ++ tailWord_3290147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290147).length < 2 ^ (prefixWord ++ tailWord_3290147).sum := by decide
  have hdescent : baseEnd_3290147 < baseStart_3290147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290177 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3290177 : Nat := 118140960795 + 3290177 * 2 ^ 59
def prefixEnd_3290177 : Nat := 4983230072969 + 3 ^ 40 * 3290177 * 2
def baseEnd_3290177 : Nat := 1126294826245385934037505

theorem tailTrace_3290177 : CollatzResearch.WordTrace tailWord_3290177 prefixEnd_3290177 1126294826245385934037505 := by
  unfold tailWord_3290177
  simp only [CollatzResearch.WordTrace]
  refine ⟨120002613801258121340172785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80001742534172080893448523 120002613801258121340172785)
  ·
    refine ⟨90001960350943591005129589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120002613801258121340172785 90001960350943591005129589)
    ·
      refine ⟨8437683782900961656730899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90001960350943591005129589 8437683782900961656730899)
      ·
        refine ⟨12656525674351442485096349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8437683782900961656730899 12656525674351442485096349)
        ·
          refine ⟨4746197127881790931911131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12656525674351442485096349 4746197127881790931911131)
          ·
            refine ⟨7119295691822686397866697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746197127881790931911131 7119295691822686397866697)
            ·
              refine ⟨5339471768867014798400023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119295691822686397866697 5339471768867014798400023)
              ·
                refine ⟨8009207653300522197600035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339471768867014798400023 8009207653300522197600035)
                ·
                  refine ⟨12013811479950783296400053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009207653300522197600035 12013811479950783296400053)
                  ·
                    refine ⟨1126294826245385934037505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12013811479950783296400053 1126294826245385934037505)
                    ·
                      rfl

theorem cell22_3290177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3290177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290177 prefixEnd_3290177 := by exact prefixLift 3290177
  have htrace : WordTrace (prefixWord ++ tailWord_3290177) baseStart_3290177 baseEnd_3290177 := by
    simpa [prefixWord, tailWord_3290177, baseEnd_3290177] using wordTrace_append hprefix tailTrace_3290177
  have hstable : (prefixWord ++ tailWord_3290177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290177).length < 2 ^ (prefixWord ++ tailWord_3290177).sum := by decide
  have hdescent : baseEnd_3290177 < baseStart_3290177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290190 : List Nat := [4, 1, 1, 1, 1, 3, 5, 6]
def baseStart_3290190 : Nat := 118140960795 + 3290190 * 2 ^ 59
def prefixEnd_3290190 : Nat := 4983230072969 + 3 ^ 40 * 3290190 * 2
def baseEnd_3290190 : Nat := 125144364045673137051385

theorem tailTrace_3290190 : CollatzResearch.WordTrace tailWord_3290190 prefixEnd_3290190 125144364045673137051385 := by
  unfold tailWord_3290190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000385993776378070049503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80002058633474016373597349 15000385993776378070049503)
  ·
    refine ⟨22500578990664567105074255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15000385993776378070049503 22500578990664567105074255)
    ·
      refine ⟨33750868485996850657611383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22500578990664567105074255 33750868485996850657611383)
      ·
        refine ⟨50626302728995275986417075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33750868485996850657611383 50626302728995275986417075)
        ·
          refine ⟨75939454093492913979625613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50626302728995275986417075 75939454093492913979625613)
          ·
            refine ⟨28477295285059842742359605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75939454093492913979625613 28477295285059842742359605)
            ·
              refine ⟨2669746432974360257096213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28477295285059842742359605 2669746432974360257096213)
              ·
                refine ⟨125144364045673137051385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2669746432974360257096213 125144364045673137051385)
                ·
                  rfl

theorem cell22_3290190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_3290190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290190 prefixEnd_3290190 := by exact prefixLift 3290190
  have htrace : WordTrace (prefixWord ++ tailWord_3290190) baseStart_3290190 baseEnd_3290190 := by
    simpa [prefixWord, tailWord_3290190, baseEnd_3290190] using wordTrace_append hprefix tailTrace_3290190
  have hstable : (prefixWord ++ tailWord_3290190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290190).length < 2 ^ (prefixWord ++ tailWord_3290190).sum := by decide
  have hdescent : baseEnd_3290190 < baseStart_3290190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290198 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3290198 : Nat := 118140960795 + 3290198 * 2 ^ 59
def prefixEnd_3290198 : Nat := 4983230072969 + 3 ^ 40 * 3290198 * 2
def baseEnd_3290198 : Nat := 1126302014974548879262441

theorem tailTrace_3290198 : CollatzResearch.WordTrace tailWord_3290198 prefixEnd_3290198 1126302014974548879262441 := by
  unfold tailWord_3290198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500211233386377620417953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80002253156121361284458165 7500211233386377620417953)
  ·
    refine ⟨5625158425039783215313465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7500211233386377620417953 5625158425039783215313465)
    ·
      refine ⟨4218868818779837411485099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5625158425039783215313465 4218868818779837411485099)
      ·
        refine ⟨6328303228169756117227649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218868818779837411485099 6328303228169756117227649)
        ·
          refine ⟨4746227421127317087920737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6328303228169756117227649 4746227421127317087920737)
          ·
            refine ⟨3559670565845487815940553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4746227421127317087920737 3559670565845487815940553)
            ·
              refine ⟨2669752924384115861955415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3559670565845487815940553 2669752924384115861955415)
              ·
                refine ⟨4004629386576173792933123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669752924384115861955415 4004629386576173792933123)
                ·
                  refine ⟨6006944079864260689399685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004629386576173792933123 6006944079864260689399685)
                  ·
                    refine ⟨1126302014974548879262441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6006944079864260689399685 1126302014974548879262441)
                    ·
                      rfl

theorem cell22_3290198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3290198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290198 prefixEnd_3290198 := by exact prefixLift 3290198
  have htrace : WordTrace (prefixWord ++ tailWord_3290198) baseStart_3290198 baseEnd_3290198 := by
    simpa [prefixWord, tailWord_3290198, baseEnd_3290198] using wordTrace_append hprefix tailTrace_3290198
  have hstable : (prefixWord ++ tailWord_3290198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290198).length < 2 ^ (prefixWord ++ tailWord_3290198).sum := by decide
  have hdescent : baseEnd_3290198 < baseStart_3290198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290222 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3290222 : Nat := 118140960795 + 3290222 * 2 ^ 59
def prefixEnd_3290222 : Nat := 4983230072969 + 3 ^ 40 * 3290222 * 2
def baseEnd_3290222 : Nat := 1126310230665020816662367

theorem tailTrace_3290222 : CollatzResearch.WordTrace tailWord_3290222 prefixEnd_3290222 1126310230665020816662367 := by
  unfold tailWord_3290222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000531885761886753195115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80002836724063396017040613 15000531885761886753195115)
  ·
    refine ⟨22500797828642830129792673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15000531885761886753195115 22500797828642830129792673)
    ·
      refine ⟨16875598371482122597344505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22500797828642830129792673 16875598371482122597344505)
      ·
        refine ⟨12656698778611591948008379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16875598371482122597344505 12656698778611591948008379)
        ·
          refine ⟨18985048167917387922012569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12656698778611591948008379 18985048167917387922012569)
          ·
            refine ⟨14238786125938040941509427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18985048167917387922012569 14238786125938040941509427)
            ·
              refine ⟨21358179188907061412264141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14238786125938040941509427 21358179188907061412264141)
              ·
                refine ⟨8009317195840148029599053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21358179188907061412264141 8009317195840148029599053)
                ·
                  refine ⟨3003493948440055511099645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8009317195840148029599053 3003493948440055511099645)
                  ·
                    refine ⟨1126310230665020816662367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3003493948440055511099645 1126310230665020816662367)
                    ·
                      rfl

theorem cell22_3290222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3290222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290222 prefixEnd_3290222 := by exact prefixLift 3290222
  have htrace : WordTrace (prefixWord ++ tailWord_3290222) baseStart_3290222 baseEnd_3290222 := by
    simpa [prefixWord, tailWord_3290222, baseEnd_3290222] using wordTrace_append hprefix tailTrace_3290222
  have hstable : (prefixWord ++ tailWord_3290222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290222).length < 2 ^ (prefixWord ++ tailWord_3290222).sum := by decide
  have hdescent : baseEnd_3290222 < baseStart_3290222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290295 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 1, 5]
def baseStart_3290295 : Nat := 118140960795 + 3290295 * 2 ^ 59
def prefixEnd_3290295 : Nat := 4983230072969 + 3 ^ 40 * 3290295 * 2
def baseEnd_3290295 : Nat := 1126335220056872959587143

theorem tailTrace_3290295 : CollatzResearch.WordTrace tailWord_3290295 prefixEnd_3290295 1126335220056872959587143 := by
  unfold tailWord_3290295
  simp only [CollatzResearch.WordTrace]
  refine ⟨120006917614830627492968339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80004611743220418328645559 120006917614830627492968339)
  ·
    refine ⟨180010376422245941239452509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120006917614830627492968339 180010376422245941239452509)
    ·
      refine ⟨67503891158342227964794691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180010376422245941239452509 67503891158342227964794691)
      ·
        refine ⟨101255836737513341947192037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67503891158342227964794691 101255836737513341947192037)
        ·
          refine ⟨18985469388283751615098507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101255836737513341947192037 18985469388283751615098507)
          ·
            refine ⟨28478204082425627422647761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18985469388283751615098507 28478204082425627422647761)
            ·
              refine ⟨21358653061819220566985821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28478204082425627422647761 21358653061819220566985821)
              ·
                refine ⟨8009494898182207712619683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21358653061819220566985821 8009494898182207712619683)
                ·
                  refine ⟨12014242347273311568929525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009494898182207712619683 12014242347273311568929525)
                  ·
                    refine ⟨1126335220056872959587143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12014242347273311568929525 1126335220056872959587143)
                    ·
                      rfl

theorem cell22_3290295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_3290295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290295 prefixEnd_3290295 := by exact prefixLift 3290295
  have htrace : WordTrace (prefixWord ++ tailWord_3290295) baseStart_3290295 baseEnd_3290295 := by
    simpa [prefixWord, tailWord_3290295, baseEnd_3290295] using wordTrace_append hprefix tailTrace_3290295
  have hstable : (prefixWord ++ tailWord_3290295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290295).length < 2 ^ (prefixWord ++ tailWord_3290295).sum := by decide
  have hdescent : baseEnd_3290295 < baseStart_3290295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290325 : List Nat := [1, 3, 2, 4, 1, 11]
def baseStart_3290325 : Nat := 118140960795 + 3290325 * 2 ^ 59
def prefixEnd_3290325 : Nat := 4983230072969 + 3 ^ 40 * 3290325 * 2
def baseEnd_3290325 : Nat := 13905499872468677547371

theorem tailTrace_3290325 : CollatzResearch.WordTrace tailWord_3290325 prefixEnd_3290325 13905499872468677547371 := by
  unfold tailWord_3290325
  simp only [CollatzResearch.WordTrace]
  refine ⟨120008011804721942616560429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80005341203147961744373619 120008011804721942616560429)
  ·
    refine ⟨45003004426770728481210161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120008011804721942616560429 45003004426770728481210161)
    ·
      refine ⟨33752253320078046360907621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45003004426770728481210161 33752253320078046360907621)
      ·
        refine ⟨6328547497514633692670179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33752253320078046360907621 6328547497514633692670179)
        ·
          refine ⟨9492821246271950539005269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328547497514633692670179 9492821246271950539005269)
          ·
            refine ⟨13905499872468677547371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9492821246271950539005269 13905499872468677547371)
            ·
              rfl

theorem cell22_3290325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 11].length) (baseStart_3290325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290325 prefixEnd_3290325 := by exact prefixLift 3290325
  have htrace : WordTrace (prefixWord ++ tailWord_3290325) baseStart_3290325 baseEnd_3290325 := by
    simpa [prefixWord, tailWord_3290325, baseEnd_3290325] using wordTrace_append hprefix tailTrace_3290325
  have hstable : (prefixWord ++ tailWord_3290325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290325).length < 2 ^ (prefixWord ++ tailWord_3290325).sum := by decide
  have hdescent : baseEnd_3290325 < baseStart_3290325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290385 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3290385 : Nat := 118140960795 + 3290385 * 2 ^ 59
def prefixEnd_3290385 : Nat := 4983230072969 + 3 ^ 40 * 3290385 * 2
def baseEnd_3290385 : Nat := 1126366028896142724836867

theorem tailTrace_3290385 : CollatzResearch.WordTrace tailWord_3290385 prefixEnd_3290385 1126366028896142724836867 := by
  unfold tailWord_3290385
  simp only [CollatzResearch.WordTrace]
  refine ⟨120010200184504572863744609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80006800123003048575829739 120010200184504572863744609)
  ·
    refine ⟨90007650138378429647808457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120010200184504572863744609 90007650138378429647808457)
    ·
      refine ⟨67505737603783822235856343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90007650138378429647808457 67505737603783822235856343)
      ·
        refine ⟨101258606405675733353784515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67505737603783822235856343 101258606405675733353784515)
        ·
          refine ⟨151887909608513600030676773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101258606405675733353784515 151887909608513600030676773)
          ·
            refine ⟨28478983051596300005751895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151887909608513600030676773 28478983051596300005751895)
            ·
              refine ⟨42718474577394450008627843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28478983051596300005751895 42718474577394450008627843)
              ·
                refine ⟨64077711866091675012941765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42718474577394450008627843 64077711866091675012941765)
                ·
                  refine ⟨12014570974892189064926581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64077711866091675012941765 12014570974892189064926581)
                  ·
                    refine ⟨1126366028896142724836867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12014570974892189064926581 1126366028896142724836867)
                    ·
                      rfl

theorem cell22_3290385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3290385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290385 prefixEnd_3290385 := by exact prefixLift 3290385
  have htrace : WordTrace (prefixWord ++ tailWord_3290385) baseStart_3290385 baseEnd_3290385 := by
    simpa [prefixWord, tailWord_3290385, baseEnd_3290385] using wordTrace_append hprefix tailTrace_3290385
  have hstable : (prefixWord ++ tailWord_3290385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290385).length < 2 ^ (prefixWord ++ tailWord_3290385).sum := by decide
  have hdescent : baseEnd_3290385 < baseStart_3290385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290404 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3290404 : Nat := 118140960795 + 3290404 * 2 ^ 59
def prefixEnd_3290404 : Nat := 4983230072969 + 3 ^ 40 * 3290404 * 2
def baseEnd_3290404 : Nat := 375457510994811002870603

theorem tailTrace_3290404 : CollatzResearch.WordTrace tailWord_3290404 prefixEnd_3290404 375457510994811002870603 := by
  unfold tailWord_3290404
  simp only [CollatzResearch.WordTrace]
  refine ⟨60005446585717869554343133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80007262114290492739124177 60005446585717869554343133)
  ·
    refine ⟨22502042469644201082878675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60005446585717869554343133 22502042469644201082878675)
    ·
      refine ⟨33753063704466301624318013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22502042469644201082878675 33753063704466301624318013)
      ·
        refine ⟨12657398889174863109119255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33753063704466301624318013 12657398889174863109119255)
        ·
          refine ⟨18986098333762294663678883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12657398889174863109119255 18986098333762294663678883)
          ·
            refine ⟨28479147500643441995518325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18986098333762294663678883 28479147500643441995518325)
            ·
              refine ⟨2669920078185322687079843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28479147500643441995518325 2669920078185322687079843)
              ·
                refine ⟨4004880117277984030619765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669920078185322687079843 4004880117277984030619765)
                ·
                  refine ⟨375457510994811002870603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4004880117277984030619765 375457510994811002870603)
                  ·
                    rfl

theorem cell22_3290404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3290404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290404 prefixEnd_3290404 := by exact prefixLift 3290404
  have htrace : WordTrace (prefixWord ++ tailWord_3290404) baseStart_3290404 baseEnd_3290404 := by
    simpa [prefixWord, tailWord_3290404, baseEnd_3290404] using wordTrace_append hprefix tailTrace_3290404
  have hstable : (prefixWord ++ tailWord_3290404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290404).length < 2 ^ (prefixWord ++ tailWord_3290404).sum := by decide
  have hdescent : baseEnd_3290404 < baseStart_3290404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290425 : List Nat := [1, 2, 1, 6, 3, 1, 1, 3, 1, 3]
def baseStart_3290425 : Nat := 118140960795 + 3290425 * 2 ^ 59
def prefixEnd_3290425 : Nat := 4983230072969 + 3 ^ 40 * 3290425 * 2
def baseEnd_3290425 : Nat := 1126379721713595953836745

theorem tailTrace_3290425 : CollatzResearch.WordTrace tailWord_3290425 prefixEnd_3290425 1126379721713595953836745 := by
  unfold tailWord_3290425
  simp only [CollatzResearch.WordTrace]
  refine ⟨120011659104359659695200729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80007772736239773130133819 120011659104359659695200729)
  ·
    refine ⟨90008744328269744771400547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120011659104359659695200729 90008744328269744771400547)
    ·
      refine ⟨135013116492404617157100821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90008744328269744771400547 135013116492404617157100821)
      ·
        refine ⟨6328739835581466429239101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135013116492404617157100821 6328739835581466429239101)
        ·
          refine ⟨2373277438343049910964663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6328739835581466429239101 2373277438343049910964663)
          ·
            refine ⟨3559916157514574866446995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373277438343049910964663 3559916157514574866446995)
            ·
              refine ⟨5339874236271862299670493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559916157514574866446995 5339874236271862299670493)
              ·
                refine ⟨2002452838601948362376435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5339874236271862299670493 2002452838601948362376435)
                ·
                  refine ⟨3003679257902922543564653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002452838601948362376435 3003679257902922543564653)
                  ·
                    refine ⟨1126379721713595953836745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3003679257902922543564653 1126379721713595953836745)
                    ·
                      rfl

theorem cell22_3290425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 3].length) (baseStart_3290425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290425 prefixEnd_3290425 := by exact prefixLift 3290425
  have htrace : WordTrace (prefixWord ++ tailWord_3290425) baseStart_3290425 baseEnd_3290425 := by
    simpa [prefixWord, tailWord_3290425, baseEnd_3290425] using wordTrace_append hprefix tailTrace_3290425
  have hstable : (prefixWord ++ tailWord_3290425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290425).length < 2 ^ (prefixWord ++ tailWord_3290425).sum := by decide
  have hdescent : baseEnd_3290425 < baseStart_3290425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290477 : List Nat := [1, 5, 1, 1, 1, 3, 2, 8]
def baseStart_3290477 : Nat := 118140960795 + 3290477 * 2 ^ 59
def prefixEnd_3290477 : Nat := 4983230072969 + 3 ^ 40 * 3290477 * 2
def baseEnd_3290477 : Nat := 125155280264031683504065

theorem tailTrace_3290477 : CollatzResearch.WordTrace tailWord_3290477 prefixEnd_3290477 125155280264031683504065 := by
  unfold tailWord_3290477
  simp only [CollatzResearch.WordTrace]
  refine ⟨120013555700171272576093685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80009037133447515050729123 120013555700171272576093685)
  ·
    refine ⟨11251270846891056804008783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120013555700171272576093685 11251270846891056804008783)
    ·
      refine ⟨16876906270336585206013175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11251270846891056804008783 16876906270336585206013175)
      ·
        refine ⟨25315359405504877809019763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16876906270336585206013175 25315359405504877809019763)
        ·
          refine ⟨37973039108257316713529645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25315359405504877809019763 37973039108257316713529645)
          ·
            refine ⟨14239889665596493767573617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37973039108257316713529645 14239889665596493767573617)
            ·
              refine ⟨10679917249197370325680213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14239889665596493767573617 10679917249197370325680213)
              ·
                refine ⟨125155280264031683504065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10679917249197370325680213 125155280264031683504065)
                ·
                  rfl

theorem cell22_3290477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 8].length) (baseStart_3290477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290477 prefixEnd_3290477 := by exact prefixLift 3290477
  have htrace : WordTrace (prefixWord ++ tailWord_3290477) baseStart_3290477 baseEnd_3290477 := by
    simpa [prefixWord, tailWord_3290477, baseEnd_3290477] using wordTrace_append hprefix tailTrace_3290477
  have hstable : (prefixWord ++ tailWord_3290477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290477).length < 2 ^ (prefixWord ++ tailWord_3290477).sum := by decide
  have hdescent : baseEnd_3290477 < baseStart_3290477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290494 : List Nat := [4, 2, 3, 2, 11]
def baseStart_3290494 : Nat := 118140960795 + 3290494 * 2 ^ 59
def prefixEnd_3290494 : Nat := 4983230072969 + 3 ^ 40 * 3290494 * 2
def baseEnd_3290494 : Nat := 4635404698862974378031

theorem tailTrace_3290494 : CollatzResearch.WordTrace tailWord_3290494 prefixEnd_3290494 4635404698862974378031 := by
  unfold tailWord_3290494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15001771967638710559932817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80009450494073122986308357 15001771967638710559932817)
  ·
    refine ⟨11251328975729032919949613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15001771967638710559932817 11251328975729032919949613)
    ·
      refine ⟨4219248365898387344981105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11251328975729032919949613 4219248365898387344981105)
      ·
        refine ⟨3164436274423790508735829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4219248365898387344981105 3164436274423790508735829)
        ·
          refine ⟨4635404698862974378031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3164436274423790508735829 4635404698862974378031)
          ·
            rfl

theorem cell22_3290494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 11].length) (baseStart_3290494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290494 prefixEnd_3290494 := by exact prefixLift 3290494
  have htrace : WordTrace (prefixWord ++ tailWord_3290494) baseStart_3290494 baseEnd_3290494 := by
    simpa [prefixWord, tailWord_3290494, baseEnd_3290494] using wordTrace_append hprefix tailTrace_3290494
  have hstable : (prefixWord ++ tailWord_3290494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290494).length < 2 ^ (prefixWord ++ tailWord_3290494).sum := by decide
  have hdescent : baseEnd_3290494 < baseStart_3290494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290498 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3290498 : Nat := 118140960795 + 3290498 * 2 ^ 59
def prefixEnd_3290498 : Nat := 4983230072969 + 3 ^ 40 * 3290498 * 2
def baseEnd_3290498 : Nat := 1126404711105448096761521

theorem tailTrace_3290498 : CollatzResearch.WordTrace tailWord_3290498 prefixEnd_3290498 1126404711105448096761521 := by
  unfold tailWord_3290498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30003580408273798290652037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80009547755396795441738765 30003580408273798290652037)
  ·
    refine ⟨5625671326551337179497257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30003580408273798290652037 5625671326551337179497257)
    ·
      refine ⟨4219253494913502884622943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5625671326551337179497257 4219253494913502884622943)
      ·
        refine ⟨6328880242370254326934415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219253494913502884622943 6328880242370254326934415)
        ·
          refine ⟨9493320363555381490401623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328880242370254326934415 9493320363555381490401623)
          ·
            refine ⟨14239980545333072235602435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9493320363555381490401623 14239980545333072235602435)
            ·
              refine ⟨21359970817999608353403653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14239980545333072235602435 21359970817999608353403653)
              ·
                refine ⟨4004994528374926566263185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21359970817999608353403653 4004994528374926566263185)
                ·
                  refine ⟨3003745896281194924697389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4004994528374926566263185 3003745896281194924697389)
                  ·
                    refine ⟨1126404711105448096761521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3003745896281194924697389 1126404711105448096761521)
                    ·
                      rfl

theorem cell22_3290498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3290498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290498 prefixEnd_3290498 := by exact prefixLift 3290498
  have htrace : WordTrace (prefixWord ++ tailWord_3290498) baseStart_3290498 baseEnd_3290498 := by
    simpa [prefixWord, tailWord_3290498, baseEnd_3290498] using wordTrace_append hprefix tailTrace_3290498
  have hstable : (prefixWord ++ tailWord_3290498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290498).length < 2 ^ (prefixWord ++ tailWord_3290498).sum := by decide
  have hdescent : baseEnd_3290498 < baseStart_3290498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290586 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_3290586 : Nat := 118140960795 + 3290586 * 2 ^ 59
def prefixEnd_3290586 : Nat := 4983230072969 + 3 ^ 40 * 3290586 * 2
def baseEnd_3290586 : Nat := 1126434835303845200561251

theorem tailTrace_3290586 : CollatzResearch.WordTrace tailWord_3290586 prefixEnd_3290586 1126434835303845200561251 := by
  unfold tailWord_3290586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30004382814194096047952903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80011687504517589461207741 30004382814194096047952903)
  ·
    refine ⟨45006574221291144071929355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30004382814194096047952903 45006574221291144071929355)
    ·
      refine ⟨67509861331936716107894033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45006574221291144071929355 67509861331936716107894033)
      ·
        refine ⟨50632395998952537080920525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67509861331936716107894033 50632395998952537080920525)
        ·
          refine ⟨18987148499607201405345197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50632395998952537080920525 18987148499607201405345197)
          ·
            refine ⟨7120180687352700527004449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18987148499607201405345197 7120180687352700527004449)
            ·
              refine ⟨5340135515514525395253337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7120180687352700527004449 5340135515514525395253337)
              ·
                refine ⟨4005101636635894046440003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340135515514525395253337 4005101636635894046440003)
                ·
                  refine ⟨6007652454953841069660005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005101636635894046440003 6007652454953841069660005)
                  ·
                    refine ⟨1126434835303845200561251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007652454953841069660005 1126434835303845200561251)
                    ·
                      rfl

theorem cell22_3290586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_3290586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290586 prefixEnd_3290586 := by exact prefixLift 3290586
  have htrace : WordTrace (prefixWord ++ tailWord_3290586) baseStart_3290586 baseEnd_3290586 := by
    simpa [prefixWord, tailWord_3290586, baseEnd_3290586] using wordTrace_append hprefix tailTrace_3290586
  have hstable : (prefixWord ++ tailWord_3290586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290586).length < 2 ^ (prefixWord ++ tailWord_3290586).sum := by decide
  have hdescent : baseEnd_3290586 < baseStart_3290586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290627 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 2, 7]
def baseStart_3290627 : Nat := 118140960795 + 3290627 * 2 ^ 59
def prefixEnd_3290627 : Nat := 4983230072969 + 3 ^ 40 * 3290627 * 2
def baseEnd_3290627 : Nat := 1126448870441734760286125

theorem tailTrace_3290627 : CollatzResearch.WordTrace tailWord_3290627 prefixEnd_3290627 1126448870441734760286125 := by
  unfold tailWord_3290627
  simp only [CollatzResearch.WordTrace]
  refine ⟨120019026649627848194054135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80012684433085232129369423 120019026649627848194054135)
  ·
    refine ⟨180028539974441772291081203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120019026649627848194054135 180028539974441772291081203)
    ·
      refine ⟨270042809961662658436621805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180028539974441772291081203 270042809961662658436621805)
      ·
        refine ⟨101266053735623496913733177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270042809961662658436621805 101266053735623496913733177)
        ·
          refine ⟨75949540301717622685299883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101266053735623496913733177 75949540301717622685299883)
          ·
            refine ⟨113924310452576434027949825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75949540301717622685299883 113924310452576434027949825)
            ·
              refine ⟨85443232839432325520962369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113924310452576434027949825 85443232839432325520962369)
              ·
                refine ⟨64082424629574244140721777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85443232839432325520962369 64082424629574244140721777)
                ·
                  refine ⟨48061818472180683105541333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64082424629574244140721777 48061818472180683105541333)
                  ·
                    refine ⟨1126448870441734760286125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48061818472180683105541333 1126448870441734760286125)
                    ·
                      rfl

theorem cell22_3290627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_3290627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290627 prefixEnd_3290627 := by exact prefixLift 3290627
  have htrace : WordTrace (prefixWord ++ tailWord_3290627) baseStart_3290627 baseEnd_3290627 := by
    simpa [prefixWord, tailWord_3290627, baseEnd_3290627] using wordTrace_append hprefix tailTrace_3290627
  have hstable : (prefixWord ++ tailWord_3290627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290627).length < 2 ^ (prefixWord ++ tailWord_3290627).sum := by decide
  have hdescent : baseEnd_3290627 < baseStart_3290627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290637 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3290637 : Nat := 118140960795 + 3290637 * 2 ^ 59
def prefixEnd_3290637 : Nat := 4983230072969 + 3 ^ 40 * 3290637 * 2
def baseEnd_3290637 : Nat := 1126452293646098067536095

theorem tailTrace_3290637 : CollatzResearch.WordTrace tailWord_3290637 prefixEnd_3290637 1126452293646098067536095 := by
  unfold tailWord_3290637
  simp only [CollatzResearch.WordTrace]
  refine ⟨120019391379591619901918165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80012927586394413267945443 120019391379591619901918165)
  ·
    refine ⟨2812954485459178591451207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 120019391379591619901918165 2812954485459178591451207)
    ·
      refine ⟨4219431728188767887176811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812954485459178591451207 4219431728188767887176811)
      ·
        refine ⟨6329147592283151830765217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219431728188767887176811 6329147592283151830765217)
        ·
          refine ⟨4746860694212363873073913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6329147592283151830765217 4746860694212363873073913)
          ·
            refine ⟨3560145520659272904805435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4746860694212363873073913 3560145520659272904805435)
            ·
              refine ⟨5340218280988909357208153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560145520659272904805435 5340218280988909357208153)
              ·
                refine ⟨4005163710741682017906115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340218280988909357208153 4005163710741682017906115)
                ·
                  refine ⟨6007745566112523026859173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005163710741682017906115 6007745566112523026859173)
                  ·
                    refine ⟨1126452293646098067536095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007745566112523026859173 1126452293646098067536095)
                    ·
                      rfl

theorem cell22_3290637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3290637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290637 prefixEnd_3290637 := by exact prefixLift 3290637
  have htrace : WordTrace (prefixWord ++ tailWord_3290637) baseStart_3290637 baseEnd_3290637 := by
    simpa [prefixWord, tailWord_3290637, baseEnd_3290637] using wordTrace_append hprefix tailTrace_3290637
  have hstable : (prefixWord ++ tailWord_3290637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290637).length < 2 ^ (prefixWord ++ tailWord_3290637).sum := by decide
  have hdescent : baseEnd_3290637 < baseStart_3290637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290654 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3290654 : Nat := 118140960795 + 3290654 * 2 ^ 59
def prefixEnd_3290654 : Nat := 4983230072969 + 3 ^ 40 * 3290654 * 2
def baseEnd_3290654 : Nat := 1126458113093515689861043

theorem tailTrace_3290654 : CollatzResearch.WordTrace tailWord_3290654 prefixEnd_3290654 1126458113093515689861043 := by
  unfold tailWord_3290654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15002501427566253975660877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80013340947020021203524677 15002501427566253975660877)
  ·
    refine ⟨5625938035337345240872829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15002501427566253975660877 5625938035337345240872829)
    ·
      refine ⟨2109726763251504465327311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5625938035337345240872829 2109726763251504465327311)
      ·
        refine ⟨3164590144877256697990967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109726763251504465327311 3164590144877256697990967)
        ·
          refine ⟨4746885217315885046986451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164590144877256697990967 4746885217315885046986451)
          ·
            refine ⟨7120327825973827570479677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746885217315885046986451 7120327825973827570479677)
            ·
              refine ⟨2670122934740185338929879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7120327825973827570479677 2670122934740185338929879)
              ·
                refine ⟨4005184402110278008394819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670122934740185338929879 4005184402110278008394819)
                ·
                  refine ⟨6007776603165417012592229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005184402110278008394819 6007776603165417012592229)
                  ·
                    refine ⟨1126458113093515689861043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007776603165417012592229 1126458113093515689861043)
                    ·
                      rfl

theorem cell22_3290654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3290654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290654 prefixEnd_3290654 := by exact prefixLift 3290654
  have htrace : WordTrace (prefixWord ++ tailWord_3290654) baseStart_3290654 baseEnd_3290654 := by
    simpa [prefixWord, tailWord_3290654, baseEnd_3290654] using wordTrace_append hprefix tailTrace_3290654
  have hstable : (prefixWord ++ tailWord_3290654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290654).length < 2 ^ (prefixWord ++ tailWord_3290654).sum := by decide
  have hdescent : baseEnd_3290654 < baseStart_3290654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290704 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_3290704 : Nat := 118140960795 + 3290704 * 2 ^ 59
def prefixEnd_3290704 : Nat := 4983230072969 + 3 ^ 40 * 3290704 * 2
def baseEnd_3290704 : Nat := 1126475229115332226110889

theorem tailTrace_3290704 : CollatzResearch.WordTrace tailWord_3290704 prefixEnd_3290704 1126475229115332226110889 := by
  unfold tailWord_3290704
  simp only [CollatzResearch.WordTrace]
  refine ⟨60010917535174445172303583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80014556713565926896404777 60010917535174445172303583)
  ·
    refine ⟨90016376302761667758455375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60010917535174445172303583 90016376302761667758455375)
    ·
      refine ⟨135024564454142501637683063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90016376302761667758455375 135024564454142501637683063)
      ·
        refine ⟨202536846681213752456524595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135024564454142501637683063 202536846681213752456524595)
        ·
          refine ⟨303805270021820628684786893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202536846681213752456524595 303805270021820628684786893)
          ·
            refine ⟨113926976258182735756795085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303805270021820628684786893 113926976258182735756795085)
            ·
              refine ⟨42722616096818525908798157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113926976258182735756795085 42722616096818525908798157)
              ·
                refine ⟨16020981036306947215799309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42722616096818525908798157 16020981036306947215799309)
                ·
                  refine ⟨6007867888615105205924741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16020981036306947215799309 6007867888615105205924741)
                  ·
                    refine ⟨1126475229115332226110889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007867888615105205924741 1126475229115332226110889)
                    ·
                      rfl

theorem cell22_3290704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_3290704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290704 prefixEnd_3290704 := by exact prefixLift 3290704
  have htrace : WordTrace (prefixWord ++ tailWord_3290704) baseStart_3290704 baseEnd_3290704 := by
    simpa [prefixWord, tailWord_3290704, baseEnd_3290704] using wordTrace_append hprefix tailTrace_3290704
  have hstable : (prefixWord ++ tailWord_3290704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290704).length < 2 ^ (prefixWord ++ tailWord_3290704).sum := by decide
  have hdescent : baseEnd_3290704 < baseStart_3290704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290721 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3290721 : Nat := 118140960795 + 3290721 * 2 ^ 59
def prefixEnd_3290721 : Nat := 4983230072969 + 3 ^ 40 * 3290721 * 2
def baseEnd_3290721 : Nat := 1126481048562749848435837

theorem tailTrace_3290721 : CollatzResearch.WordTrace tailWord_3290721 prefixEnd_3290721 1126481048562749848435837 := by
  unfold tailWord_3290721
  simp only [CollatzResearch.WordTrace]
  refine ⟨120022455111287302247976017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80014970074191534831984011 120022455111287302247976017)
  ·
    refine ⟨90016841333465476685982013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120022455111287302247976017 90016841333465476685982013)
    ·
      refine ⟨33756315500049553757243255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90016841333465476685982013 33756315500049553757243255)
      ·
        refine ⟨50634473250074330635864883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33756315500049553757243255 50634473250074330635864883)
        ·
          refine ⟨75951709875111495953797325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50634473250074330635864883 75951709875111495953797325)
          ·
            refine ⟨28481891203166810982673997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75951709875111495953797325 28481891203166810982673997)
            ·
              refine ⟨10680709201187554118502749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28481891203166810982673997 10680709201187554118502749)
              ·
                refine ⟨4005265950445332794438531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10680709201187554118502749 4005265950445332794438531)
                ·
                  refine ⟨6007898925667999191657797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005265950445332794438531 6007898925667999191657797)
                  ·
                    refine ⟨1126481048562749848435837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007898925667999191657797 1126481048562749848435837)
                    ·
                      rfl

theorem cell22_3290721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3290721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290721 prefixEnd_3290721 := by exact prefixLift 3290721
  have htrace : WordTrace (prefixWord ++ tailWord_3290721) baseStart_3290721 baseEnd_3290721 := by
    simpa [prefixWord, tailWord_3290721, baseEnd_3290721] using wordTrace_append hprefix tailTrace_3290721
  have hstable : (prefixWord ++ tailWord_3290721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290721).length < 2 ^ (prefixWord ++ tailWord_3290721).sum := by decide
  have hdescent : baseEnd_3290721 < baseStart_3290721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290736 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 6]
def baseStart_3290736 : Nat := 118140960795 + 3290736 * 2 ^ 59
def prefixEnd_3290736 : Nat := 4983230072969 + 3 ^ 40 * 3290736 * 2
def baseEnd_3290736 : Nat := 375495394456431603103597

theorem tailTrace_3290736 : CollatzResearch.WordTrace tailWord_3290736 prefixEnd_3290736 375495394456431603103597 := by
  unfold tailWord_3290736
  simp only [CollatzResearch.WordTrace]
  refine ⟨60011501103116479904886031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80015334804155306539848041 60011501103116479904886031)
  ·
    refine ⟨90017251654674719857329047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60011501103116479904886031 90017251654674719857329047)
    ·
      refine ⟨135025877482012079785993571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90017251654674719857329047 135025877482012079785993571)
      ·
        refine ⟨202538816223018119678990357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135025877482012079785993571 202538816223018119678990357)
        ·
          refine ⟨9494007010453974359952673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202538816223018119678990357 9494007010453974359952673)
          ·
            refine ⟨7120505257840480769964505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9494007010453974359952673 7120505257840480769964505)
            ·
              refine ⟨5340378943380360577473379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7120505257840480769964505 5340378943380360577473379)
              ·
                refine ⟨8010568415070540866210069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340378943380360577473379 8010568415070540866210069)
                ·
                  refine ⟨375495394456431603103597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8010568415070540866210069 375495394456431603103597)
                  ·
                    rfl

theorem cell22_3290736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_3290736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290736 prefixEnd_3290736 := by exact prefixLift 3290736
  have htrace : WordTrace (prefixWord ++ tailWord_3290736) baseStart_3290736 baseEnd_3290736 := by
    simpa [prefixWord, tailWord_3290736, baseEnd_3290736] using wordTrace_append hprefix tailTrace_3290736
  have hstable : (prefixWord ++ tailWord_3290736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290736).length < 2 ^ (prefixWord ++ tailWord_3290736).sum := by decide
  have hdescent : baseEnd_3290736 < baseStart_3290736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290764 : List Nat := [2, 2, 1, 2, 1, 1, 5, 8]
def baseStart_3290764 : Nat := 118140960795 + 3290764 * 2 ^ 59
def prefixEnd_3290764 : Nat := 4983230072969 + 3 ^ 40 * 3290764 * 2
def baseEnd_3290764 : Nat := 125166196482390229956745

theorem tailTrace_3290764 : CollatzResearch.WordTrace tailWord_3290764 prefixEnd_3290764 125166196482390229956745 := by
  unfold tailWord_3290764
  simp only [CollatzResearch.WordTrace]
  refine ⟨60012011725065760295895673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80016015633421013727860897 60012011725065760295895673)
  ·
    refine ⟨45009008793799320221921755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60012011725065760295895673 45009008793799320221921755)
    ·
      refine ⟨67513513190698980332882633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45009008793799320221921755 67513513190698980332882633)
      ·
        refine ⟨50635134893024235249661975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67513513190698980332882633 50635134893024235249661975)
        ·
          refine ⟨75952702339536352874492963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50635134893024235249661975 75952702339536352874492963)
          ·
            refine ⟨113929053509304529311739445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75952702339536352874492963 113929053509304529311739445)
            ·
              refine ⟨10680848766497299622975573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113929053509304529311739445 10680848766497299622975573)
              ·
                refine ⟨125166196482390229956745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10680848766497299622975573 125166196482390229956745)
                ·
                  rfl

theorem cell22_3290764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 8].length) (baseStart_3290764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290764 prefixEnd_3290764 := by exact prefixLift 3290764
  have htrace : WordTrace (prefixWord ++ tailWord_3290764) baseStart_3290764 baseEnd_3290764 := by
    simpa [prefixWord, tailWord_3290764, baseEnd_3290764] using wordTrace_append hprefix tailTrace_3290764
  have hstable : (prefixWord ++ tailWord_3290764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290764).length < 2 ^ (prefixWord ++ tailWord_3290764).sum := by decide
  have hdescent : baseEnd_3290764 < baseStart_3290764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290766 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3290766 : Nat := 118140960795 + 3290766 * 2 ^ 59
def prefixEnd_3290766 : Nat := 4983230072969 + 3 ^ 40 * 3290766 * 2
def baseEnd_3290766 : Nat := 1126496452982384731060699

theorem tailTrace_3290766 : CollatzResearch.WordTrace tailWord_3290766 prefixEnd_3290766 1126496452982384731060699 := by
  unfold tailWord_3290766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15003012049515534366670519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80016064264082849955576101 15003012049515534366670519)
  ·
    refine ⟨22504518074273301550005779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15003012049515534366670519 22504518074273301550005779)
    ·
      refine ⟨33756777111409952325008669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22504518074273301550005779 33756777111409952325008669)
      ·
        refine ⟨12658791416778732121878251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33756777111409952325008669 12658791416778732121878251)
        ·
          refine ⟨18988187125168098182817377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12658791416778732121878251 18988187125168098182817377)
          ·
            refine ⟨14241140343876073637113033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18988187125168098182817377 14241140343876073637113033)
            ·
              refine ⟨10680855257907055227834775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14241140343876073637113033 10680855257907055227834775)
              ·
                refine ⟨16021282886860582841752163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10680855257907055227834775 16021282886860582841752163)
                ·
                  refine ⟨24031924330290874262628245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16021282886860582841752163 24031924330290874262628245)
                  ·
                    refine ⟨1126496452982384731060699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24031924330290874262628245 1126496452982384731060699)
                    ·
                      rfl

theorem cell22_3290766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3290766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290766 prefixEnd_3290766 := by exact prefixLift 3290766
  have htrace : WordTrace (prefixWord ++ tailWord_3290766) baseStart_3290766 baseEnd_3290766 := by
    simpa [prefixWord, tailWord_3290766, baseEnd_3290766] using wordTrace_append hprefix tailTrace_3290766
  have hstable : (prefixWord ++ tailWord_3290766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290766).length < 2 ^ (prefixWord ++ tailWord_3290766).sum := by decide
  have hdescent : baseEnd_3290766 < baseStart_3290766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290830 : List Nat := [4, 1, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3290830 : Nat := 118140960795 + 3290830 * 2 ^ 59
def prefixEnd_3290830 : Nat := 4983230072969 + 3 ^ 40 * 3290830 * 2
def baseEnd_3290830 : Nat := 1126518361490309897460503

theorem tailTrace_3290830 : CollatzResearch.WordTrace tailWord_3290830 prefixEnd_3290830 1126518361490309897460503 := by
  unfold tailWord_3290830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15003303833486551732961743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80017620445261609242462629 15003303833486551732961743)
  ·
    refine ⟨22504955750229827599442615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15003303833486551732961743 22504955750229827599442615)
    ·
      refine ⟨33757433625344741399163923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22504955750229827599442615 33757433625344741399163923)
      ·
        refine ⟨50636150438017112098745885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33757433625344741399163923 50636150438017112098745885)
        ·
          refine ⟨18988556414256417037029707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50636150438017112098745885 18988556414256417037029707)
          ·
            refine ⟨28482834621384625555544561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18988556414256417037029707 28482834621384625555544561)
            ·
              refine ⟨21362125966038469166658421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28482834621384625555544561 21362125966038469166658421)
              ·
                refine ⟨2002699309316106484374227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21362125966038469166658421 2002699309316106484374227)
                ·
                  refine ⟨3004048963974159726561341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002699309316106484374227 3004048963974159726561341)
                  ·
                    refine ⟨1126518361490309897460503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3004048963974159726561341 1126518361490309897460503)
                    ·
                      rfl

theorem cell22_3290830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3290830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290830 prefixEnd_3290830 := by exact prefixLift 3290830
  have htrace : WordTrace (prefixWord ++ tailWord_3290830) baseStart_3290830 baseEnd_3290830 := by
    simpa [prefixWord, tailWord_3290830, baseEnd_3290830] using wordTrace_append hprefix tailTrace_3290830
  have hstable : (prefixWord ++ tailWord_3290830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290830).length < 2 ^ (prefixWord ++ tailWord_3290830).sum := by decide
  have hdescent : baseEnd_3290830 < baseStart_3290830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290890 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_3290890 : Nat := 118140960795 + 3290890 * 2 ^ 59
def prefixEnd_3290890 : Nat := 4983230072969 + 3 ^ 40 * 3290890 * 2
def baseEnd_3290890 : Nat := 1126538900716489740960319

theorem tailTrace_3290890 : CollatzResearch.WordTrace tailWord_3290890 prefixEnd_3290890 1126538900716489740960319 := by
  unfold tailWord_3290890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30007154761918761027719531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80019079365116696073918749 30007154761918761027719531)
  ·
    refine ⟨45010732142878141541579297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30007154761918761027719531 45010732142878141541579297)
    ·
      refine ⟨33758049107158606156184473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45010732142878141541579297 33758049107158606156184473)
      ·
        refine ⟨25318536830368954617138355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33758049107158606156184473 25318536830368954617138355)
        ·
          refine ⟨37977805245553431925707533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25318536830368954617138355 37977805245553431925707533)
          ·
            refine ⟨14241676967082536972140325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37977805245553431925707533 14241676967082536972140325)
            ·
              refine ⟨2670314431327975682276311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14241676967082536972140325 2670314431327975682276311)
              ·
                refine ⟨4005471646991963523414467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670314431327975682276311 4005471646991963523414467)
                ·
                  refine ⟨6008207470487945285121701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005471646991963523414467 6008207470487945285121701)
                  ·
                    refine ⟨1126538900716489740960319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6008207470487945285121701 1126538900716489740960319)
                    ·
                      rfl

theorem cell22_3290890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_3290890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290890 prefixEnd_3290890 := by exact prefixLift 3290890
  have htrace : WordTrace (prefixWord ++ tailWord_3290890) baseStart_3290890 baseEnd_3290890 := by
    simpa [prefixWord, tailWord_3290890, baseEnd_3290890] using wordTrace_append hprefix tailTrace_3290890
  have hstable : (prefixWord ++ tailWord_3290890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290890).length < 2 ^ (prefixWord ++ tailWord_3290890).sum := by decide
  have hdescent : baseEnd_3290890 < baseStart_3290890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290920 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3290920 : Nat := 118140960795 + 3290920 * 2 ^ 59
def prefixEnd_3290920 : Nat := 4983230072969 + 3 ^ 40 * 3290920 * 2
def baseEnd_3290920 : Nat := 1126549170329579662710227

theorem tailTrace_3290920 : CollatzResearch.WordTrace tailWord_3290920 prefixEnd_3290920 1126549170329579662710227 := by
  unfold tailWord_3290920
  simp only [CollatzResearch.WordTrace]
  refine ⟨60014856618783179617235107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80019808825044239489646809 60014856618783179617235107)
  ·
    refine ⟨90022284928174769425852661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60014856618783179617235107 90022284928174769425852661)
    ·
      refine ⟨8439589212016384633673687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90022284928174769425852661 8439589212016384633673687)
      ·
        refine ⟨12659383818024576950510531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8439589212016384633673687 12659383818024576950510531)
        ·
          refine ⟨18989075727036865425765797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12659383818024576950510531 18989075727036865425765797)
          ·
            refine ⟨3560451698819412267331087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18989075727036865425765797 3560451698819412267331087)
            ·
              refine ⟨5340677548229118400996631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560451698819412267331087 5340677548229118400996631)
              ·
                refine ⟨8011016322343677601494947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340677548229118400996631 8011016322343677601494947)
                ·
                  refine ⟨12016524483515516402242421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8011016322343677601494947 12016524483515516402242421)
                  ·
                    refine ⟨1126549170329579662710227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12016524483515516402242421 1126549170329579662710227)
                    ·
                      rfl

theorem cell22_3290920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3290920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290920 prefixEnd_3290920 := by exact prefixLift 3290920
  have htrace : WordTrace (prefixWord ++ tailWord_3290920) baseStart_3290920 baseEnd_3290920 := by
    simpa [prefixWord, tailWord_3290920, baseEnd_3290920] using wordTrace_append hprefix tailTrace_3290920
  have hstable : (prefixWord ++ tailWord_3290920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290920).length < 2 ^ (prefixWord ++ tailWord_3290920).sum := by decide
  have hdescent : baseEnd_3290920 < baseStart_3290920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290933 : List Nat := [1, 3, 3, 1, 4, 1, 1, 8]
def baseStart_3290933 : Nat := 118140960795 + 3290933 * 2 ^ 59
def prefixEnd_3290933 : Nat := 4983230072969 + 3 ^ 40 * 3290933 * 2
def baseEnd_3290933 : Nat := 125172624499472440237243

theorem tailTrace_3290933 : CollatzResearch.WordTrace tailWord_3290933 prefixEnd_3290933 125172624499472440237243 := by
  unfold tailWord_3290933
  simp only [CollatzResearch.WordTrace]
  refine ⟨120030187386519262454693453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80020124924346174969795635 120030187386519262454693453)
  ·
    refine ⟨45011320269944723420510045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120030187386519262454693453 45011320269944723420510045)
    ·
      refine ⟨16879245101229271282691267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45011320269944723420510045 16879245101229271282691267)
      ·
        refine ⟨25318867651843906924036901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16879245101229271282691267 25318867651843906924036901)
        ·
          refine ⟨4747287684720732548256919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25318867651843906924036901 4747287684720732548256919)
          ·
            refine ⟨7120931527081098822385379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747287684720732548256919 7120931527081098822385379)
            ·
              refine ⟨10681397290621648233578069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7120931527081098822385379 10681397290621648233578069)
              ·
                refine ⟨125172624499472440237243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10681397290621648233578069 125172624499472440237243)
                ·
                  rfl

theorem cell22_3290933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 8].length) (baseStart_3290933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290933 prefixEnd_3290933 := by exact prefixLift 3290933
  have htrace : WordTrace (prefixWord ++ tailWord_3290933) baseStart_3290933 baseEnd_3290933 := by
    simpa [prefixWord, tailWord_3290933, baseEnd_3290933] using wordTrace_append hprefix tailTrace_3290933
  have hstable : (prefixWord ++ tailWord_3290933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290933).length < 2 ^ (prefixWord ++ tailWord_3290933).sum := by decide
  have hdescent : baseEnd_3290933 < baseStart_3290933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290950 : List Nat := [6, 1, 1, 2, 1, 1, 10]
def baseStart_3290950 : Nat := 118140960795 + 3290950 * 2 ^ 59
def prefixEnd_3290950 : Nat := 4983230072969 + 3 ^ 40 * 3290950 * 2
def baseEnd_3290950 : Nat := 41724423701580354980005

theorem tailTrace_3290950 : CollatzResearch.WordTrace tailWord_3290950 prefixEnd_3290950 41724423701580354980005 := by
  unfold tailWord_3290950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750962732108052323689447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80020538284971782905374869 3750962732108052323689447)
  ·
    refine ⟨5626444098162078485534171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3750962732108052323689447 5626444098162078485534171)
    ·
      refine ⟨8439666147243117728301257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5626444098162078485534171 8439666147243117728301257)
      ·
        refine ⟨6329749610432338296225943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8439666147243117728301257 6329749610432338296225943)
        ·
          refine ⟨9494624415648507444338915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329749610432338296225943 9494624415648507444338915)
          ·
            refine ⟨14241936623472761166508373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9494624415648507444338915 14241936623472761166508373)
            ·
              refine ⟨41724423701580354980005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14241936623472761166508373 41724423701580354980005)
              ·
                rfl

theorem cell22_3290950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 10].length) (baseStart_3290950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290950 prefixEnd_3290950 := by exact prefixLift 3290950
  have htrace : WordTrace (prefixWord ++ tailWord_3290950) baseStart_3290950 baseEnd_3290950 := by
    simpa [prefixWord, tailWord_3290950, baseEnd_3290950] using wordTrace_append hprefix tailTrace_3290950
  have hstable : (prefixWord ++ tailWord_3290950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290950).length < 2 ^ (prefixWord ++ tailWord_3290950).sum := by decide
  have hdescent : baseEnd_3290950 < baseStart_3290950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3290965 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_3290965 : Nat := 118140960795 + 3290965 * 2 ^ 59
def prefixEnd_3290965 : Nat := 4983230072969 + 3 ^ 40 * 3290965 * 2
def baseEnd_3290965 : Nat := 1126564574749214545335089

theorem tailTrace_3290965 : CollatzResearch.WordTrace tailWord_3290965 prefixEnd_3290965 1126564574749214545335089 := by
  unfold tailWord_3290965
  simp only [CollatzResearch.WordTrace]
  refine ⟨120031354522403331919858349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80020903014935554613238899 120031354522403331919858349)
  ·
    refine ⟨45011757945901249469946881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120031354522403331919858349 45011757945901249469946881)
    ·
      refine ⟨33758818459425937102460161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45011757945901249469946881 33758818459425937102460161)
      ·
        refine ⟨25319113844569452826845121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33758818459425937102460161 25319113844569452826845121)
        ·
          refine ⟨18989335383427089620133841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25319113844569452826845121 18989335383427089620133841)
          ·
            refine ⟨14242001537570317215100381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18989335383427089620133841 14242001537570317215100381)
            ·
              refine ⟨5340750576588868955662643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14242001537570317215100381 5340750576588868955662643)
              ·
                refine ⟨8011125864883303433493965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340750576588868955662643 8011125864883303433493965)
                ·
                  refine ⟨3004172199331238787560237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8011125864883303433493965 3004172199331238787560237)
                  ·
                    refine ⟨1126564574749214545335089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3004172199331238787560237 1126564574749214545335089)
                    ·
                      rfl

theorem cell22_3290965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_3290965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3290965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3290965 prefixEnd_3290965 := by exact prefixLift 3290965
  have htrace : WordTrace (prefixWord ++ tailWord_3290965) baseStart_3290965 baseEnd_3290965 := by
    simpa [prefixWord, tailWord_3290965, baseEnd_3290965] using wordTrace_append hprefix tailTrace_3290965
  have hstable : (prefixWord ++ tailWord_3290965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3290965).length < 2 ^ (prefixWord ++ tailWord_3290965).sum := by decide
  have hdescent : baseEnd_3290965 < baseStart_3290965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3290965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291016 : List Nat := [2, 1, 3, 3, 3, 2, 2, 2, 1, 3]
def baseStart_3291016 : Nat := 118140960795 + 3291016 * 2 ^ 59
def prefixEnd_3291016 : Nat := 4983230072969 + 3 ^ 40 * 3291016 * 2
def baseEnd_3291016 : Nat := 1126582033091467412309933

theorem tailTrace_3291016 : CollatzResearch.WordTrace tailWord_3291016 prefixEnd_3291016 1126582033091467412309933 := by
  unfold tailWord_3291016
  simp only [CollatzResearch.WordTrace]
  refine ⟨60016607322609283814982451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80022143096812378419976601 60016607322609283814982451)
  ·
    refine ⟨90024910983913925722473677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60016607322609283814982451 90024910983913925722473677)
    ·
      refine ⟨33759341618967722145927629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90024910983913925722473677 33759341618967722145927629)
      ·
        refine ⟨12659753107112895804722861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33759341618967722145927629 12659753107112895804722861)
        ·
          refine ⟨4747407415167335926771073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12659753107112895804722861 4747407415167335926771073)
          ·
            refine ⟨3560555561375501945078305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4747407415167335926771073 3560555561375501945078305)
            ·
              refine ⟨2670416671031626458808729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3560555561375501945078305 2670416671031626458808729)
              ·
                refine ⟨2002812503273719844106547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670416671031626458808729 2002812503273719844106547)
                ·
                  refine ⟨3004218754910579766159821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002812503273719844106547 3004218754910579766159821)
                  ·
                    refine ⟨1126582033091467412309933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3004218754910579766159821 1126582033091467412309933)
                    ·
                      rfl

theorem cell22_3291016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_3291016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291016 prefixEnd_3291016 := by exact prefixLift 3291016
  have htrace : WordTrace (prefixWord ++ tailWord_3291016) baseStart_3291016 baseEnd_3291016 := by
    simpa [prefixWord, tailWord_3291016, baseEnd_3291016] using wordTrace_append hprefix tailTrace_3291016
  have hstable : (prefixWord ++ tailWord_3291016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291016).length < 2 ^ (prefixWord ++ tailWord_3291016).sum := by decide
  have hdescent : baseEnd_3291016 < baseStart_3291016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291057 : List Nat := [1, 2, 2, 4, 2, 2, 2, 3, 4]
def baseStart_3291057 : Nat := 118140960795 + 3291057 * 2 ^ 59
def prefixEnd_3291057 : Nat := 4983230072969 + 3 ^ 40 * 3291057 * 2
def baseEnd_3291057 : Nat := 375532022743118990678269

theorem tailTrace_3291057 : CollatzResearch.WordTrace tailWord_3291057 prefixEnd_3291057 375532022743118990678269 := by
  unfold tailWord_3291057
  simp only [CollatzResearch.WordTrace]
  refine ⟨120034710038070031632207425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80023140025380021088138283 120034710038070031632207425)
  ·
    refine ⟨90026032528552523724155569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120034710038070031632207425 90026032528552523724155569)
    ·
      refine ⟨67519524396414392793116677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90026032528552523724155569 67519524396414392793116677)
      ·
        refine ⟨12659910824327698648709377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67519524396414392793116677 12659910824327698648709377)
        ·
          refine ⟨9494933118245773986532033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12659910824327698648709377 9494933118245773986532033)
          ·
            refine ⟨7121199838684330489899025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9494933118245773986532033 7121199838684330489899025)
            ·
              refine ⟨5340899879013247867424269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7121199838684330489899025 5340899879013247867424269)
              ·
                refine ⟨2002837454629967950284101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5340899879013247867424269 2002837454629967950284101)
                ·
                  refine ⟨375532022743118990678269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002837454629967950284101 375532022743118990678269)
                  ·
                    rfl

theorem cell22_3291057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_3291057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291057 prefixEnd_3291057 := by exact prefixLift 3291057
  have htrace : WordTrace (prefixWord ++ tailWord_3291057) baseStart_3291057 baseEnd_3291057 := by
    simpa [prefixWord, tailWord_3291057, baseEnd_3291057] using wordTrace_append hprefix tailTrace_3291057
  have hstable : (prefixWord ++ tailWord_3291057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291057).length < 2 ^ (prefixWord ++ tailWord_3291057).sum := by decide
  have hdescent : baseEnd_3291057 < baseStart_3291057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291128 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_3291128 : Nat := 118140960795 + 3291128 * 2 ^ 59
def prefixEnd_3291128 : Nat := 4983230072969 + 3 ^ 40 * 3291128 * 2
def baseEnd_3291128 : Nat := 1126620372980336453509589

theorem tailTrace_3291128 : CollatzResearch.WordTrace tailWord_3291128 prefixEnd_3291128 1126620372980336453509589 := by
  unfold tailWord_3291128
  simp only [CollatzResearch.WordTrace]
  refine ⟨60018649810406405379021019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80024866413875207172028025 60018649810406405379021019)
  ·
    refine ⟨90027974715609608068531529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60018649810406405379021019 90027974715609608068531529)
    ·
      refine ⟨67520981036707206051398647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90027974715609608068531529 67520981036707206051398647)
      ·
        refine ⟨101281471555060809077097971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67520981036707206051398647 101281471555060809077097971)
        ·
          refine ⟨151922207332591213615646957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101281471555060809077097971 151922207332591213615646957)
          ·
            refine ⟨56970827749721705105867609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151922207332591213615646957 56970827749721705105867609)
            ·
              refine ⟨42728120812291278829400707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56970827749721705105867609 42728120812291278829400707)
              ·
                refine ⟨64092181218436918244101061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42728120812291278829400707 64092181218436918244101061)
                ·
                  refine ⟨12017283978456922170768949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64092181218436918244101061 12017283978456922170768949)
                  ·
                    refine ⟨1126620372980336453509589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12017283978456922170768949 1126620372980336453509589)
                    ·
                      rfl

theorem cell22_3291128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_3291128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291128 prefixEnd_3291128 := by exact prefixLift 3291128
  have htrace : WordTrace (prefixWord ++ tailWord_3291128) baseStart_3291128 baseEnd_3291128 := by
    simpa [prefixWord, tailWord_3291128, baseEnd_3291128] using wordTrace_append hprefix tailTrace_3291128
  have hstable : (prefixWord ++ tailWord_3291128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291128).length < 2 ^ (prefixWord ++ tailWord_3291128).sum := by decide
  have hdescent : baseEnd_3291128 < baseStart_3291128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291134 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3291134 : Nat := 118140960795 + 3291134 * 2 ^ 59
def prefixEnd_3291134 : Nat := 4983230072969 + 3 ^ 40 * 3291134 * 2
def baseEnd_3291134 : Nat := 1126622426902954437859571

theorem tailTrace_3291134 : CollatzResearch.WordTrace tailWord_3291134 prefixEnd_3291134 1126622426902954437859571 := by
  unfold tailWord_3291134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004689807348884222845057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80025012305860715855173637 15004689807348884222845057)
  ·
    refine ⟨11253517355511663167133793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15004689807348884222845057 11253517355511663167133793)
    ·
      refine ⟨8440138016633747375350345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11253517355511663167133793 8440138016633747375350345)
      ·
        refine ⟨6330103512475310531512759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8440138016633747375350345 6330103512475310531512759)
        ·
          refine ⟨9495155268712965797269139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330103512475310531512759 9495155268712965797269139)
          ·
            refine ⟨14242732903069448695903709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495155268712965797269139 14242732903069448695903709)
            ·
              refine ⟨5341024838651043260963891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14242732903069448695903709 5341024838651043260963891)
              ·
                refine ⟨8011537257976564891445837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341024838651043260963891 8011537257976564891445837)
                ·
                  refine ⟨3004326471741211834292189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8011537257976564891445837 3004326471741211834292189)
                  ·
                    refine ⟨1126622426902954437859571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3004326471741211834292189 1126622426902954437859571)
                    ·
                      rfl

theorem cell22_3291134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3291134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291134 prefixEnd_3291134 := by exact prefixLift 3291134
  have htrace : WordTrace (prefixWord ++ tailWord_3291134) baseStart_3291134 baseEnd_3291134 := by
    simpa [prefixWord, tailWord_3291134, baseEnd_3291134] using wordTrace_append hprefix tailTrace_3291134
  have hstable : (prefixWord ++ tailWord_3291134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291134).length < 2 ^ (prefixWord ++ tailWord_3291134).sum := by decide
  have hdescent : baseEnd_3291134 < baseStart_3291134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291160 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_3291160 : Nat := 118140960795 + 3291160 * 2 ^ 59
def prefixEnd_3291160 : Nat := 4983230072969 + 3 ^ 40 * 3291160 * 2
def baseEnd_3291160 : Nat := 1126631327234299036709491

theorem tailTrace_3291160 : CollatzResearch.WordTrace tailWord_3291160 prefixEnd_3291160 1126631327234299036709491 := by
  unfold tailWord_3291160
  simp only [CollatzResearch.WordTrace]
  refine ⟨60019233378348440111603467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80025644504464586815471289 60019233378348440111603467)
  ·
    refine ⟨90028850067522660167405201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60019233378348440111603467 90028850067522660167405201)
    ·
      refine ⟨67521637550641995125553901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90028850067522660167405201 67521637550641995125553901)
      ·
        refine ⟨25320614081490748172082713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67521637550641995125553901 25320614081490748172082713)
        ·
          refine ⟨18990460561118061129062035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25320614081490748172082713 18990460561118061129062035)
          ·
            refine ⟨28485690841677091693593053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18990460561118061129062035 28485690841677091693593053)
            ·
              refine ⟨10682134065628909385097395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28485690841677091693593053 10682134065628909385097395)
              ·
                refine ⟨16023201098443364077646093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10682134065628909385097395 16023201098443364077646093)
                ·
                  refine ⟨6008700411916261529117285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16023201098443364077646093 6008700411916261529117285)
                  ·
                    refine ⟨1126631327234299036709491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6008700411916261529117285 1126631327234299036709491)
                    ·
                      rfl

theorem cell22_3291160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_3291160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291160 prefixEnd_3291160 := by exact prefixLift 3291160
  have htrace : WordTrace (prefixWord ++ tailWord_3291160) baseStart_3291160 baseEnd_3291160 := by
    simpa [prefixWord, tailWord_3291160, baseEnd_3291160] using wordTrace_append hprefix tailTrace_3291160
  have hstable : (prefixWord ++ tailWord_3291160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291160).length < 2 ^ (prefixWord ++ tailWord_3291160).sum := by decide
  have hdescent : baseEnd_3291160 < baseStart_3291160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291203 : List Nat := [1, 1, 1, 3, 1, 2, 2, 11]
def baseStart_3291203 : Nat := 118140960795 + 3291203 * 2 ^ 59
def prefixEnd_3291203 : Nat := 4983230072969 + 3 ^ 40 * 3291203 * 2
def baseEnd_3291203 : Nat := 125182894112562361987151

theorem tailTrace_3291203 : CollatzResearch.WordTrace tailWord_3291203 prefixEnd_3291203 125182894112562361987151 := by
  unfold tailWord_3291203
  simp only [CollatzResearch.WordTrace]
  refine ⟨120040035095541098567022263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80026690063694065711348175 120040035095541098567022263)
  ·
    refine ⟨180060052643311647850533395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120040035095541098567022263 180060052643311647850533395)
    ·
      refine ⟨270090078964967471775800093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180060052643311647850533395 270090078964967471775800093)
      ·
        refine ⟨101283779611862801915925035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270090078964967471775800093 101283779611862801915925035)
        ·
          refine ⟨151925669417794202873887553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101283779611862801915925035 151925669417794202873887553)
          ·
            refine ⟨113944252063345652155415665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151925669417794202873887553 113944252063345652155415665)
            ·
              refine ⟨85458189047509239116561749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113944252063345652155415665 85458189047509239116561749)
              ·
                refine ⟨125182894112562361987151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 85458189047509239116561749 125182894112562361987151)
                ·
                  rfl

theorem cell22_3291203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 11].length) (baseStart_3291203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291203 prefixEnd_3291203 := by exact prefixLift 3291203
  have htrace : WordTrace (prefixWord ++ tailWord_3291203) baseStart_3291203 baseEnd_3291203 := by
    simpa [prefixWord, tailWord_3291203, baseEnd_3291203] using wordTrace_append hprefix tailTrace_3291203
  have hstable : (prefixWord ++ tailWord_3291203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291203).length < 2 ^ (prefixWord ++ tailWord_3291203).sum := by decide
  have hdescent : baseEnd_3291203 < baseStart_3291203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291207 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 2, 3]
def baseStart_3291207 : Nat := 118140960795 + 3291207 * 2 ^ 59
def prefixEnd_3291207 : Nat := 4983230072969 + 3 ^ 40 * 3291207 * 2
def baseEnd_3291207 : Nat := 1126647416294806580784347

theorem tailTrace_3291207 : CollatzResearch.WordTrace tailWord_3291207 prefixEnd_3291207 1126647416294806580784347 := by
  unfold tailWord_3291207
  simp only [CollatzResearch.WordTrace]
  refine ⟨120040180987526607250167875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80026787325017738166778583 120040180987526607250167875)
  ·
    refine ⟨180060271481289910875251813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120040180987526607250167875 180060271481289910875251813)
    ·
      refine ⟨33761300902741858289109715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180060271481289910875251813 33761300902741858289109715)
      ·
        refine ⟨50641951354112787433664573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33761300902741858289109715 50641951354112787433664573)
        ·
          refine ⟨18990731757792295287624215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50641951354112787433664573 18990731757792295287624215)
          ·
            refine ⟨28486097636688442931436323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18990731757792295287624215 28486097636688442931436323)
            ·
              refine ⟨42729146455032664397154485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28486097636688442931436323 42729146455032664397154485)
              ·
                refine ⟨4005857480159312287233233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42729146455032664397154485 4005857480159312287233233)
                ·
                  refine ⟨3004393110119484215424925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4005857480159312287233233 3004393110119484215424925)
                  ·
                    refine ⟨1126647416294806580784347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3004393110119484215424925 1126647416294806580784347)
                    ·
                      rfl

theorem cell22_3291207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_3291207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291207 prefixEnd_3291207 := by exact prefixLift 3291207
  have htrace : WordTrace (prefixWord ++ tailWord_3291207) baseStart_3291207 baseEnd_3291207 := by
    simpa [prefixWord, tailWord_3291207, baseEnd_3291207] using wordTrace_append hprefix tailTrace_3291207
  have hstable : (prefixWord ++ tailWord_3291207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291207).length < 2 ^ (prefixWord ++ tailWord_3291207).sum := by decide
  have hdescent : baseEnd_3291207 < baseStart_3291207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291303 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3291303 : Nat := 118140960795 + 3291303 * 2 ^ 59
def prefixEnd_3291303 : Nat := 4983230072969 + 3 ^ 40 * 3291303 * 2
def baseEnd_3291303 : Nat := 1126680279056694330384053

theorem tailTrace_3291303 : CollatzResearch.WordTrace tailWord_3291303 prefixEnd_3291303 1126680279056694330384053 := by
  unfold tailWord_3291303
  simp only [CollatzResearch.WordTrace]
  refine ⟨120043682395178815645662563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80029121596785877097108375 120043682395178815645662563)
  ·
    refine ⟨180065523592768223468493845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120043682395178815645662563 180065523592768223468493845)
    ·
      refine ⟨8440571418411010475085649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180065523592768223468493845 8440571418411010475085649)
      ·
        refine ⟨6330428563808257856314237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8440571418411010475085649 6330428563808257856314237)
        ·
          refine ⟨2373910711428096696117839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6330428563808257856314237 2373910711428096696117839)
          ·
            refine ⟨3560866067142145044176759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373910711428096696117839 3560866067142145044176759)
            ·
              refine ⟨5341299100713217566265139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560866067142145044176759 5341299100713217566265139)
              ·
                refine ⟨8011948651069826349397709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5341299100713217566265139 8011948651069826349397709)
                ·
                  refine ⟨3004480744151184881024141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8011948651069826349397709 3004480744151184881024141)
                  ·
                    refine ⟨1126680279056694330384053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3004480744151184881024141 1126680279056694330384053)
                    ·
                      rfl

theorem cell22_3291303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3291303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291303 prefixEnd_3291303 := by exact prefixLift 3291303
  have htrace : WordTrace (prefixWord ++ tailWord_3291303) baseStart_3291303 baseEnd_3291303 := by
    simpa [prefixWord, tailWord_3291303, baseEnd_3291303] using wordTrace_append hprefix tailTrace_3291303
  have hstable : (prefixWord ++ tailWord_3291303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291303).length < 2 ^ (prefixWord ++ tailWord_3291303).sum := by decide
  have hdescent : baseEnd_3291303 < baseStart_3291303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291342 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3291342 : Nat := 118140960795 + 3291342 * 2 ^ 59
def prefixEnd_3291342 : Nat := 4983230072969 + 3 ^ 40 * 3291342 * 2
def baseEnd_3291342 : Nat := 1126693629553711228658933

theorem tailTrace_3291342 : CollatzResearch.WordTrace tailWord_3291342 prefixEnd_3291342 1126693629553711228658933 := by
  unfold tailWord_3291342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15005638105254690663291535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80030069894691683537554853 15005638105254690663291535)
  ·
    refine ⟨22508457157882035994937303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15005638105254690663291535 22508457157882035994937303)
    ·
      refine ⟨33762685736823053992405955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22508457157882035994937303 33762685736823053992405955)
      ·
        refine ⟨50644028605234580988608933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33762685736823053992405955 50644028605234580988608933)
        ·
          refine ⟨9495755363481483935364175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50644028605234580988608933 9495755363481483935364175)
          ·
            refine ⟨14243633045222225903046263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495755363481483935364175 14243633045222225903046263)
            ·
              refine ⟨21365449567833338854569395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243633045222225903046263 21365449567833338854569395)
              ·
                refine ⟨32048174351750008281854093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21365449567833338854569395 32048174351750008281854093)
                ·
                  refine ⟨12018065381906253105695285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32048174351750008281854093 12018065381906253105695285)
                  ·
                    refine ⟨1126693629553711228658933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12018065381906253105695285 1126693629553711228658933)
                    ·
                      rfl

theorem cell22_3291342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3291342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291342 prefixEnd_3291342 := by exact prefixLift 3291342
  have htrace : WordTrace (prefixWord ++ tailWord_3291342) baseStart_3291342 baseEnd_3291342 := by
    simpa [prefixWord, tailWord_3291342, baseEnd_3291342] using wordTrace_append hprefix tailTrace_3291342
  have hstable : (prefixWord ++ tailWord_3291342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291342).length < 2 ^ (prefixWord ++ tailWord_3291342).sum := by decide
  have hdescent : baseEnd_3291342 < baseStart_3291342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291346 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_3291346 : Nat := 118140960795 + 3291346 * 2 ^ 59
def prefixEnd_3291346 : Nat := 4983230072969 + 3 ^ 40 * 3291346 * 2
def baseEnd_3291346 : Nat := 1126694998835456551558921

theorem tailTrace_3291346 : CollatzResearch.WordTrace tailWord_3291346 prefixEnd_3291346 1126694998835456551558921 := by
  unfold tailWord_3291346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30011312683505758497369473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80030167156015355992985261 30011312683505758497369473)
  ·
    refine ⟨22508484512629318873027105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30011312683505758497369473 22508484512629318873027105)
    ·
      refine ⟨16881363384471989154770329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22508484512629318873027105 16881363384471989154770329)
      ·
        refine ⟨12661022538353991866077747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16881363384471989154770329 12661022538353991866077747)
        ·
          refine ⟨18991533807530987799116621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12661022538353991866077747 18991533807530987799116621)
          ·
            refine ⟨7121825177824120424668733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18991533807530987799116621 7121825177824120424668733)
            ·
              refine ⟨2670684441684045159250775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7121825177824120424668733 2670684441684045159250775)
              ·
                refine ⟨4006026662526067738876163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670684441684045159250775 4006026662526067738876163)
                ·
                  refine ⟨6009039993789101608314245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006026662526067738876163 6009039993789101608314245)
                  ·
                    refine ⟨1126694998835456551558921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009039993789101608314245 1126694998835456551558921)
                    ·
                      rfl

theorem cell22_3291346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_3291346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291346 prefixEnd_3291346 := by exact prefixLift 3291346
  have htrace : WordTrace (prefixWord ++ tailWord_3291346) baseStart_3291346 baseEnd_3291346 := by
    simpa [prefixWord, tailWord_3291346, baseEnd_3291346] using wordTrace_append hprefix tailTrace_3291346
  have hstable : (prefixWord ++ tailWord_3291346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291346).length < 2 ^ (prefixWord ++ tailWord_3291346).sum := by decide
  have hdescent : baseEnd_3291346 < baseStart_3291346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291447 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 3, 4]
def baseStart_3291447 : Nat := 118140960795 + 3291447 * 2 ^ 59
def prefixEnd_3291447 : Nat := 4983230072969 + 3 ^ 40 * 3291447 * 2
def baseEnd_3291447 : Nat := 1126729573199525954783611

theorem tailTrace_3291447 : CollatzResearch.WordTrace tailWord_3291447 prefixEnd_3291447 1126729573199525954783611 := by
  unfold tailWord_3291447
  simp only [CollatzResearch.WordTrace]
  refine ⟨120048934506657128238904595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80032623004438085492603063 120048934506657128238904595)
  ·
    refine ⟨180073401759985692358356893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120048934506657128238904595 180073401759985692358356893)
    ·
      refine ⟨67527525659994634634383835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180073401759985692358356893 67527525659994634634383835)
      ·
        refine ⟨101291288489991951951575753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67527525659994634634383835 101291288489991951951575753)
        ·
          refine ⟨75968466367493963963681815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101291288489991951951575753 75968466367493963963681815)
          ·
            refine ⟨113952699551240945945522723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75968466367493963963681815 113952699551240945945522723)
            ·
              refine ⟨170929049326861418918284085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113952699551240945945522723 170929049326861418918284085)
              ·
                refine ⟨16024598374393258023589133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170929049326861418918284085 16024598374393258023589133)
                ·
                  refine ⟨6009224390397471758845925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16024598374393258023589133 6009224390397471758845925)
                  ·
                    refine ⟨1126729573199525954783611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009224390397471758845925 1126729573199525954783611)
                    ·
                      rfl

theorem cell22_3291447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_3291447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291447 prefixEnd_3291447 := by exact prefixLift 3291447
  have htrace : WordTrace (prefixWord ++ tailWord_3291447) baseStart_3291447 baseEnd_3291447 := by
    simpa [prefixWord, tailWord_3291447, baseEnd_3291447] using wordTrace_append hprefix tailTrace_3291447
  have hstable : (prefixWord ++ tailWord_3291447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291447).length < 2 ^ (prefixWord ++ tailWord_3291447).sum := by decide
  have hdescent : baseEnd_3291447 < baseStart_3291447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291464 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_3291464 : Nat := 118140960795 + 3291464 * 2 ^ 59
def prefixEnd_3291464 : Nat := 4983230072969 + 3 ^ 40 * 3291464 * 2
def baseEnd_3291464 : Nat := 1126735392646943577108559

theorem tailTrace_3291464 : CollatzResearch.WordTrace tailWord_3291464 prefixEnd_3291464 1126735392646943577108559 := by
  unfold tailWord_3291464
  simp only [CollatzResearch.WordTrace]
  refine ⟨60024777273797770071136723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80033036365063693428182297 60024777273797770071136723)
  ·
    refine ⟨90037165910696655106705085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60024777273797770071136723 90037165910696655106705085)
    ·
      refine ⟨33763937216511245665014407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90037165910696655106705085 33763937216511245665014407)
      ·
        refine ⟨50645905824766868497521611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33763937216511245665014407 50645905824766868497521611)
        ·
          refine ⟨75968858737150302746282417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50645905824766868497521611 75968858737150302746282417)
          ·
            refine ⟨56976644052862727059711813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75968858737150302746282417 56976644052862727059711813)
            ·
              refine ⟨10683120759911761323695965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56976644052862727059711813 10683120759911761323695965)
              ·
                refine ⟨4006170284966910496385987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10683120759911761323695965 4006170284966910496385987)
                ·
                  refine ⟨6009255427450365744578981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006170284966910496385987 6009255427450365744578981)
                  ·
                    refine ⟨1126735392646943577108559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009255427450365744578981 1126735392646943577108559)
                    ·
                      rfl

theorem cell22_3291464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_3291464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291464 prefixEnd_3291464 := by exact prefixLift 3291464
  have htrace : WordTrace (prefixWord ++ tailWord_3291464) baseStart_3291464 baseEnd_3291464 := by
    simpa [prefixWord, tailWord_3291464, baseEnd_3291464] using wordTrace_append hprefix tailTrace_3291464
  have hstable : (prefixWord ++ tailWord_3291464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291464).length < 2 ^ (prefixWord ++ tailWord_3291464).sum := by decide
  have hdescent : baseEnd_3291464 < baseStart_3291464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291498 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_3291498 : Nat := 118140960795 + 3291498 * 2 ^ 59
def prefixEnd_3291498 : Nat := 4983230072969 + 3 ^ 40 * 3291498 * 2
def baseEnd_3291498 : Nat := 1126747031541778821758455

theorem tailTrace_3291498 : CollatzResearch.WordTrace tailWord_3291498 prefixEnd_3291498 1126747031541778821758455 := by
  unfold tailWord_3291498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30012698657368090987252787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80033863086314909299340765 30012698657368090987252787)
  ·
    refine ⟨45019047986052136480879181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30012698657368090987252787 45019047986052136480879181)
    ·
      refine ⟨16882142994769551180329693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45019047986052136480879181 16882142994769551180329693)
      ·
        refine ⟨6330803623038581692623635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16882142994769551180329693 6330803623038581692623635)
        ·
          refine ⟨9496205434557872538935453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330803623038581692623635 9496205434557872538935453)
          ·
            refine ⟨3561077037959202202100795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9496205434557872538935453 3561077037959202202100795)
            ·
              refine ⟨5341615556938803303151193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561077037959202202100795 5341615556938803303151193)
              ·
                refine ⟨4006211667704102477363395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5341615556938803303151193 4006211667704102477363395)
                ·
                  refine ⟨6009317501556153716045093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006211667704102477363395 6009317501556153716045093)
                  ·
                    refine ⟨1126747031541778821758455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009317501556153716045093 1126747031541778821758455)
                    ·
                      rfl

theorem cell22_3291498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_3291498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291498 prefixEnd_3291498 := by exact prefixLift 3291498
  have htrace : WordTrace (prefixWord ++ tailWord_3291498) baseStart_3291498 baseEnd_3291498 := by
    simpa [prefixWord, tailWord_3291498, baseEnd_3291498] using wordTrace_append hprefix tailTrace_3291498
  have hstable : (prefixWord ++ tailWord_3291498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291498).length < 2 ^ (prefixWord ++ tailWord_3291498).sum := by decide
  have hdescent : baseEnd_3291498 < baseStart_3291498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291554 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3291554 : Nat := 118140960795 + 3291554 * 2 ^ 59
def prefixEnd_3291554 : Nat := 4983230072969 + 3 ^ 40 * 3291554 * 2
def baseEnd_3291554 : Nat := 1126766201486213342358283

theorem tailTrace_3291554 : CollatzResearch.WordTrace tailWord_3291554 prefixEnd_3291554 1126766201486213342358283 := by
  unfold tailWord_3291554
  simp only [CollatzResearch.WordTrace]
  refine ⟨30013209279317371378262429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80035224744846323675366477 30013209279317371378262429)
  ·
    refine ⟨11254953479744014266848411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30013209279317371378262429 11254953479744014266848411)
    ·
      refine ⟨16882430219616021400272617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11254953479744014266848411 16882430219616021400272617)
      ·
        refine ⟨12661822664712016050204463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16882430219616021400272617 12661822664712016050204463)
        ·
          refine ⟨18992733997068024075306695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12661822664712016050204463 18992733997068024075306695)
          ·
            refine ⟨28489100995602036112960043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18992733997068024075306695 28489100995602036112960043)
            ·
              refine ⟨42733651493403054169440065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28489100995602036112960043 42733651493403054169440065)
              ·
                refine ⟨32050238620052290627080049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42733651493403054169440065 32050238620052290627080049)
                ·
                  refine ⟨24037678965039217970310037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32050238620052290627080049 24037678965039217970310037)
                  ·
                    refine ⟨1126766201486213342358283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24037678965039217970310037 1126766201486213342358283)
                    ·
                      rfl

theorem cell22_3291554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3291554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291554 prefixEnd_3291554 := by exact prefixLift 3291554
  have htrace : WordTrace (prefixWord ++ tailWord_3291554) baseStart_3291554 baseEnd_3291554 := by
    simpa [prefixWord, tailWord_3291554, baseEnd_3291554] using wordTrace_append hprefix tailTrace_3291554
  have hstable : (prefixWord ++ tailWord_3291554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291554).length < 2 ^ (prefixWord ++ tailWord_3291554).sum := by decide
  have hdescent : baseEnd_3291554 < baseStart_3291554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291616 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_3291616 : Nat := 118140960795 + 3291616 * 2 ^ 59
def prefixEnd_3291616 : Nat := 4983230072969 + 3 ^ 40 * 3291616 * 2
def baseEnd_3291616 : Nat := 1126787425353265847308093

theorem tailTrace_3291616 : CollatzResearch.WordTrace tailWord_3291616 prefixEnd_3291616 1126787425353265847308093 := by
  unfold tailWord_3291616
  simp only [CollatzResearch.WordTrace]
  refine ⟨60027549221522435050903351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80036732295363246734537801 60027549221522435050903351)
  ·
    refine ⟨90041323832283652576355027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60027549221522435050903351 90041323832283652576355027)
    ·
      refine ⟨135061985748425478864532541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90041323832283652576355027 135061985748425478864532541)
      ·
        refine ⟨50648244655659554574199703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135061985748425478864532541 50648244655659554574199703)
        ·
          refine ⟨75972366983489331861299555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50648244655659554574199703 75972366983489331861299555)
          ·
            refine ⟨113958550475233997791949333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75972366983489331861299555 113958550475233997791949333)
            ·
              refine ⟨5341807053526593646497625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113958550475233997791949333 5341807053526593646497625)
              ·
                refine ⟨4006355290144945234873219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5341807053526593646497625 4006355290144945234873219)
                ·
                  refine ⟨6009532935217417852309829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006355290144945234873219 6009532935217417852309829)
                  ·
                    refine ⟨1126787425353265847308093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6009532935217417852309829 1126787425353265847308093)
                    ·
                      rfl

theorem cell22_3291616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_3291616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291616 prefixEnd_3291616 := by exact prefixLift 3291616
  have htrace : WordTrace (prefixWord ++ tailWord_3291616) baseStart_3291616 baseEnd_3291616 := by
    simpa [prefixWord, tailWord_3291616, baseEnd_3291616] using wordTrace_append hprefix tailTrace_3291616
  have hstable : (prefixWord ++ tailWord_3291616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291616).length < 2 ^ (prefixWord ++ tailWord_3291616).sum := by decide
  have hdescent : baseEnd_3291616 < baseStart_3291616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
