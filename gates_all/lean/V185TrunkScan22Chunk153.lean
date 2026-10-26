import V185TrunkScan22Chunk152

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1367238 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1367238 : Nat := 118140960795 + 1367238 * 2 ^ 59
def prefixEnd_1367238 : Nat := 4983230072969 + 3 ^ 40 * 1367238 * 2
def baseEnd_1367238 : Nat := 468033508728017939158129

theorem tailTrace_1367238 : CollatzResearch.WordTrace tailWord_1367238 prefixEnd_1367238 468033508728017939158129 := by
  unfold tailWord_1367238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558352081898053328286699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33244844413825137670116245 1558352081898053328286699)
  ·
    refine ⟨2337528122847079992430049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1558352081898053328286699 2337528122847079992430049)
    ·
      refine ⟨1753146092135309994322537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2337528122847079992430049 1753146092135309994322537)
      ·
        refine ⟨1314859569101482495741903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1753146092135309994322537 1314859569101482495741903)
        ·
          refine ⟨1972289353652223743612855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314859569101482495741903 1972289353652223743612855)
          ·
            refine ⟨2958434030478335615419283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972289353652223743612855 2958434030478335615419283)
            ·
              refine ⟨4437651045717503423128925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958434030478335615419283 4437651045717503423128925)
              ·
                refine ⟨1664119142144063783673347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4437651045717503423128925 1664119142144063783673347)
                ·
                  refine ⟨2496178713216095675510021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664119142144063783673347 2496178713216095675510021)
                  ·
                    refine ⟨468033508728017939158129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496178713216095675510021 468033508728017939158129)
                    ·
                      rfl

theorem cell22_1367238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1367238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367238 prefixEnd_1367238 := by exact prefixLift 1367238
  have htrace : WordTrace (prefixWord ++ tailWord_1367238) baseStart_1367238 baseEnd_1367238 := by
    simpa [prefixWord, tailWord_1367238, baseEnd_1367238] using wordTrace_append hprefix tailTrace_1367238
  have hstable : (prefixWord ++ tailWord_1367238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367238).length < 2 ^ (prefixWord ++ tailWord_1367238).sum := by decide
  have hdescent : baseEnd_1367238 < baseStart_1367238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367243 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 8]
def baseStart_1367243 : Nat := 118140960795 + 1367243 * 2 ^ 59
def prefixEnd_1367243 : Nat := 4983230072969 + 3 ^ 40 * 1367243 * 2
def baseEnd_1367243 : Nat := 468035220330199592783113

theorem tailTrace_1367243 : CollatzResearch.WordTrace tailWord_1367243 prefixEnd_1367243 468035220330199592783113 := by
  unfold tailWord_1367243
  simp only [CollatzResearch.WordTrace]
  refine ⟨49867448985719592359106383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33244965990479728239404255 49867448985719592359106383)
  ·
    refine ⟨74801173478579388538659575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49867448985719592359106383 74801173478579388538659575)
    ·
      refine ⟨112201760217869082807989363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74801173478579388538659575 112201760217869082807989363)
      ·
        refine ⟨168302640326803624211984045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112201760217869082807989363 168302640326803624211984045)
        ·
          refine ⟨63113490122551359079494017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168302640326803624211984045 63113490122551359079494017)
          ·
            refine ⟨47335117591913519309620513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63113490122551359079494017 47335117591913519309620513)
            ·
              refine ⟨35501338193935139482215385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47335117591913519309620513 35501338193935139482215385)
              ·
                refine ⟨26626003645451354611661539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35501338193935139482215385 26626003645451354611661539)
                ·
                  refine ⟨39939005468177031917492309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26626003645451354611661539 39939005468177031917492309)
                  ·
                    refine ⟨468035220330199592783113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39939005468177031917492309 468035220330199592783113)
                    ·
                      rfl

theorem cell22_1367243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_1367243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367243 prefixEnd_1367243 := by exact prefixLift 1367243
  have htrace : WordTrace (prefixWord ++ tailWord_1367243) baseStart_1367243 baseEnd_1367243 := by
    simpa [prefixWord, tailWord_1367243, baseEnd_1367243] using wordTrace_append hprefix tailTrace_1367243
  have hstable : (prefixWord ++ tailWord_1367243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367243).length < 2 ^ (prefixWord ++ tailWord_1367243).sum := by decide
  have hdescent : baseEnd_1367243 < baseStart_1367243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367326 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1367326 : Nat := 118140960795 + 1367326 * 2 ^ 59
def prefixEnd_1367326 : Nat := 4983230072969 + 3 ^ 40 * 1367326 * 2
def baseEnd_1367326 : Nat := 156021210975471680985953

theorem tailTrace_1367326 : CollatzResearch.WordTrace tailWord_1367326 prefixEnd_1367326 156021210975471680985953 := by
  unfold tailWord_1367326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233809530552362191797229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33246984162945931689585221 6233809530552362191797229)
  ·
    refine ⟨2337678573957135821923961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6233809530552362191797229 2337678573957135821923961)
    ·
      refine ⟨1753258930467851866442971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2337678573957135821923961 1753258930467851866442971)
      ·
        refine ⟨2629888395701777799664457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753258930467851866442971 2629888395701777799664457)
        ·
          refine ⟨1972416296776333349748343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2629888395701777799664457 1972416296776333349748343)
          ·
            refine ⟨2958624445164500024622515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972416296776333349748343 2958624445164500024622515)
            ·
              refine ⟨4437936667746750036933773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958624445164500024622515 4437936667746750036933773)
              ·
                refine ⟨1664226250405031263850165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4437936667746750036933773 1664226250405031263850165)
                ·
                  refine ⟨156021210975471680985953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664226250405031263850165 156021210975471680985953)
                  ·
                    rfl

theorem cell22_1367326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1367326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367326 prefixEnd_1367326 := by exact prefixLift 1367326
  have htrace : WordTrace (prefixWord ++ tailWord_1367326) baseStart_1367326 baseEnd_1367326 := by
    simpa [prefixWord, tailWord_1367326, baseEnd_1367326] using wordTrace_append hprefix tailTrace_1367326
  have hstable : (prefixWord ++ tailWord_1367326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367326).length < 2 ^ (prefixWord ++ tailWord_1367326).sum := by decide
  have hdescent : baseEnd_1367326 < baseStart_1367326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367367 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1367367 : Nat := 118140960795 + 1367367 * 2 ^ 59
def prefixEnd_1367367 : Nat := 4983230072969 + 3 ^ 40 * 1367367 * 2
def baseEnd_1367367 : Nat := 468077668064304602682733

theorem tailTrace_1367367 : CollatzResearch.WordTrace tailWord_1367367 prefixEnd_1367367 468077668064304602682733 := by
  unfold tailWord_1367367
  simp only [CollatzResearch.WordTrace]
  refine ⟨49871971637270361536620355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33247981091513574357746903 49871971637270361536620355)
  ·
    refine ⟨74807957455905542304930533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49871971637270361536620355 74807957455905542304930533)
    ·
      refine ⟨14026492022982289182174475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74807957455905542304930533 14026492022982289182174475)
      ·
        refine ⟨21039738034473433773261713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14026492022982289182174475 21039738034473433773261713)
        ·
          refine ⟨15779803525855075329946285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21039738034473433773261713 15779803525855075329946285)
          ·
            refine ⟨5917426322195653248729857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15779803525855075329946285 5917426322195653248729857)
            ·
              refine ⟨4438069741646739936547393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5917426322195653248729857 4438069741646739936547393)
              ·
                refine ⟨3328552306235054952410545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438069741646739936547393 3328552306235054952410545)
                ·
                  refine ⟨2496414229676291214307909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328552306235054952410545 2496414229676291214307909)
                  ·
                    refine ⟨468077668064304602682733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496414229676291214307909 468077668064304602682733)
                    ·
                      rfl

theorem cell22_1367367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1367367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367367 prefixEnd_1367367 := by exact prefixLift 1367367
  have htrace : WordTrace (prefixWord ++ tailWord_1367367) baseStart_1367367 baseEnd_1367367 := by
    simpa [prefixWord, tailWord_1367367, baseEnd_1367367] using wordTrace_append hprefix tailTrace_1367367
  have hstable : (prefixWord ++ tailWord_1367367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367367).length < 2 ^ (prefixWord ++ tailWord_1367367).sum := by decide
  have hdescent : baseEnd_1367367 < baseStart_1367367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367399 : List Nat := [1, 1, 5, 1, 4, 1, 3, 6]
def baseStart_1367399 : Nat := 118140960795 + 1367399 * 2 ^ 59
def prefixEnd_1367399 : Nat := 4983230072969 + 3 ^ 40 * 1367399 * 2
def baseEnd_1367399 : Nat := 52009846924251909542515

theorem tailTrace_1367399 : CollatzResearch.WordTrace tailWord_1367399 prefixEnd_1367399 52009846924251909542515 := by
  unfold tailWord_1367399
  simp only [CollatzResearch.WordTrace]
  refine ⟨49873138773154431001785251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33248759182102954001190167 49873138773154431001785251)
  ·
    refine ⟨74809708159731646502677877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49873138773154431001785251 74809708159731646502677877)
    ·
      refine ⟨7013410139974841859626051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74809708159731646502677877 7013410139974841859626051)
      ·
        refine ⟨10520115209962262789439077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7013410139974841859626051 10520115209962262789439077)
        ·
          refine ⟨1972521601867924273019827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10520115209962262789439077 1972521601867924273019827)
          ·
            refine ⟨2958782402801886409529741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972521601867924273019827 2958782402801886409529741)
            ·
              refine ⟨1109543401050707403573653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2958782402801886409529741 1109543401050707403573653)
              ·
                refine ⟨52009846924251909542515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1109543401050707403573653 52009846924251909542515)
                ·
                  rfl

theorem cell22_1367399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 6].length) (baseStart_1367399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367399 prefixEnd_1367399 := by exact prefixLift 1367399
  have htrace : WordTrace (prefixWord ++ tailWord_1367399) baseStart_1367399 baseEnd_1367399 := by
    simpa [prefixWord, tailWord_1367399, baseEnd_1367399] using wordTrace_append hprefix tailTrace_1367399
  have hstable : (prefixWord ++ tailWord_1367399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367399).length < 2 ^ (prefixWord ++ tailWord_1367399).sum := by decide
  have hdescent : baseEnd_1367399 < baseStart_1367399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367427 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 7]
def baseStart_1367427 : Nat := 118140960795 + 1367427 * 2 ^ 59
def prefixEnd_1367427 : Nat := 4983230072969 + 3 ^ 40 * 1367427 * 2
def baseEnd_1367427 : Nat := 156032735763494815394183

theorem tailTrace_1367427 : CollatzResearch.WordTrace tailWord_1367427 prefixEnd_1367427 156032735763494815394183 := by
  unfold tailWord_1367427
  simp only [CollatzResearch.WordTrace]
  refine ⟨49874160017052991783804535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33249440011368661189203023 49874160017052991783804535)
  ·
    refine ⟨74811240025579487675706803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49874160017052991783804535 74811240025579487675706803)
    ·
      refine ⟨112216860038369231513560205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74811240025579487675706803 112216860038369231513560205)
      ·
        refine ⟨42081322514388461817585077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112216860038369231513560205 42081322514388461817585077)
        ·
          refine ⟨3945123985723918295398601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42081322514388461817585077 3945123985723918295398601)
          ·
            refine ⟨2958842989292938721548951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3945123985723918295398601 2958842989292938721548951)
            ·
              refine ⟨4438264483939408082323427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958842989292938721548951 4438264483939408082323427)
              ·
                refine ⟨6657396725909112123485141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4438264483939408082323427 6657396725909112123485141)
                ·
                  refine ⟨156032735763494815394183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6657396725909112123485141 156032735763494815394183)
                  ·
                    rfl

theorem cell22_1367427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 7].length) (baseStart_1367427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367427 prefixEnd_1367427 := by exact prefixLift 1367427
  have htrace : WordTrace (prefixWord ++ tailWord_1367427) baseStart_1367427 baseEnd_1367427 := by
    simpa [prefixWord, tailWord_1367427, baseEnd_1367427] using wordTrace_append hprefix tailTrace_1367427
  have hstable : (prefixWord ++ tailWord_1367427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367427).length < 2 ^ (prefixWord ++ tailWord_1367427).sum := by decide
  have hdescent : baseEnd_1367427 < baseStart_1367427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367431 : List Nat := [1, 1, 4, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1367431 : Nat := 118140960795 + 1367431 * 2 ^ 59
def prefixEnd_1367431 : Nat := 4983230072969 + 3 ^ 40 * 1367431 * 2
def baseEnd_1367431 : Nat := 468099576572229769082537

theorem tailTrace_1367431 : CollatzResearch.WordTrace tailWord_1367431 prefixEnd_1367431 468099576572229769082537 := by
  unfold tailWord_1367431
  simp only [CollatzResearch.WordTrace]
  refine ⟨49874305909038500466950147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33249537272692333644633431 49874305909038500466950147)
  ·
    refine ⟨74811458863557750700425221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49874305909038500466950147 74811458863557750700425221)
    ·
      refine ⟨14027148536917078256329729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74811458863557750700425221 14027148536917078256329729)
      ·
        refine ⟨10520361402687808692247297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14027148536917078256329729 10520361402687808692247297)
        ·
          refine ⟨7890271052015856519185473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10520361402687808692247297 7890271052015856519185473)
          ·
            refine ⟨5917703289011892389389105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7890271052015856519185473 5917703289011892389389105)
            ·
              refine ⟨4438277466758919292041829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5917703289011892389389105 4438277466758919292041829)
              ·
                refine ⟨832177025017297367257843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4438277466758919292041829 832177025017297367257843)
                ·
                  refine ⟨1248265537525946050886765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832177025017297367257843 1248265537525946050886765)
                  ·
                    refine ⟨468099576572229769082537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1248265537525946050886765 468099576572229769082537)
                    ·
                      rfl

theorem cell22_1367431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1367431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367431 prefixEnd_1367431 := by exact prefixLift 1367431
  have htrace : WordTrace (prefixWord ++ tailWord_1367431) baseStart_1367431 baseEnd_1367431 := by
    simpa [prefixWord, tailWord_1367431, baseEnd_1367431] using wordTrace_append hprefix tailTrace_1367431
  have hstable : (prefixWord ++ tailWord_1367431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367431).length < 2 ^ (prefixWord ++ tailWord_1367431).sum := by decide
  have hdescent : baseEnd_1367431 < baseStart_1367431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367502 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1367502 : Nat := 118140960795 + 1367502 * 2 ^ 59
def prefixEnd_1367502 : Nat := 4983230072969 + 3 ^ 40 * 1367502 * 2
def baseEnd_1367502 : Nat := 468123881323209250557319

theorem tailTrace_1367502 : CollatzResearch.WordTrace tailWord_1367502 prefixEnd_1367502 468123881323209250557319 := by
  unfold tailWord_1367502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234611936472659949098095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33251263661187519728523173 6234611936472659949098095)
  ·
    refine ⟨9351917904708989923647143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6234611936472659949098095 9351917904708989923647143)
    ·
      refine ⟨14027876857063484885470715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351917904708989923647143 14027876857063484885470715)
      ·
        refine ⟨21041815285595227328206073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14027876857063484885470715 21041815285595227328206073)
        ·
          refine ⟨15781361464196420496154555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21041815285595227328206073 15781361464196420496154555)
          ·
            refine ⟨23672042196294630744231833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15781361464196420496154555 23672042196294630744231833)
            ·
              refine ⟨17754031647220973058173875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23672042196294630744231833 17754031647220973058173875)
              ·
                refine ⟨26631047470831459587260813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17754031647220973058173875 26631047470831459587260813)
                ·
                  refine ⟨9986642801561797345222805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26631047470831459587260813 9986642801561797345222805)
                  ·
                    refine ⟨468123881323209250557319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9986642801561797345222805 468123881323209250557319)
                    ·
                      rfl

theorem cell22_1367502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1367502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367502 prefixEnd_1367502 := by exact prefixLift 1367502
  have htrace : WordTrace (prefixWord ++ tailWord_1367502) baseStart_1367502 baseEnd_1367502 := by
    simpa [prefixWord, tailWord_1367502, baseEnd_1367502] using wordTrace_append hprefix tailTrace_1367502
  have hstable : (prefixWord ++ tailWord_1367502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367502).length < 2 ^ (prefixWord ++ tailWord_1367502).sum := by decide
  have hdescent : baseEnd_1367502 < baseStart_1367502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367504 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 2, 3]
def baseStart_1367504 : Nat := 118140960795 + 1367504 * 2 ^ 59
def prefixEnd_1367504 : Nat := 4983230072969 + 3 ^ 40 * 1367504 * 2
def baseEnd_1367504 : Nat := 468124565964081912007313

theorem tailTrace_1367504 : CollatzResearch.WordTrace tailWord_1367504 prefixEnd_1367504 468124565964081912007313 := by
  unfold tailWord_1367504
  simp only [CollatzResearch.WordTrace]
  refine ⟨24938484218887016967178783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33251312291849355956238377 24938484218887016967178783)
  ·
    refine ⟨37407726328330525450768175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24938484218887016967178783 37407726328330525450768175)
    ·
      refine ⟨56111589492495788176152263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37407726328330525450768175 56111589492495788176152263)
      ·
        refine ⟨84167384238743682264228395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56111589492495788176152263 84167384238743682264228395)
        ·
          refine ⟨126251076358115523396342593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84167384238743682264228395 126251076358115523396342593)
          ·
            refine ⟨94688307268586642547256945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126251076358115523396342593 94688307268586642547256945)
            ·
              refine ⟨71016230451439981910442709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94688307268586642547256945 71016230451439981910442709)
              ·
                refine ⟨1664442901205624576026001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71016230451439981910442709 1664442901205624576026001)
                ·
                  refine ⟨1248332175904218432019501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664442901205624576026001 1248332175904218432019501)
                  ·
                    refine ⟨468124565964081912007313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1248332175904218432019501 468124565964081912007313)
                    ·
                      rfl

theorem cell22_1367504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_1367504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367504 prefixEnd_1367504 := by exact prefixLift 1367504
  have htrace : WordTrace (prefixWord ++ tailWord_1367504) baseStart_1367504 baseEnd_1367504 := by
    simpa [prefixWord, tailWord_1367504, baseEnd_1367504] using wordTrace_append hprefix tailTrace_1367504
  have hstable : (prefixWord ++ tailWord_1367504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367504).length < 2 ^ (prefixWord ++ tailWord_1367504).sum := by decide
  have hdescent : baseEnd_1367504 < baseStart_1367504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367508 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1367508 : Nat := 118140960795 + 1367508 * 2 ^ 59
def prefixEnd_1367508 : Nat := 4983230072969 + 3 ^ 40 * 1367508 * 2
def baseEnd_1367508 : Nat := 468125935245827234907301

theorem tailTrace_1367508 : CollatzResearch.WordTrace tailWord_1367508 prefixEnd_1367508 468125935245827234907301 := by
  unfold tailWord_1367508
  simp only [CollatzResearch.WordTrace]
  refine ⟨24938557164879771308751589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33251409553173028411668785 24938557164879771308751589)
  ·
    refine ⟨4675979468414957120390923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24938557164879771308751589 4675979468414957120390923)
    ·
      refine ⟨7013969202622435680586385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4675979468414957120390923 7013969202622435680586385)
      ·
        refine ⟨5260476901966826760439789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7013969202622435680586385 5260476901966826760439789)
        ·
          refine ⟨1972678838237560035164921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5260476901966826760439789 1972678838237560035164921)
          ·
            refine ⟨1479509128678170026373691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1972678838237560035164921 1479509128678170026373691)
            ·
              refine ⟨2219263693017255039560537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479509128678170026373691 2219263693017255039560537)
              ·
                refine ⟨1664447769762941279670403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219263693017255039560537 1664447769762941279670403)
                ·
                  refine ⟨2496671654644411919505605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664447769762941279670403 2496671654644411919505605)
                  ·
                    refine ⟨468125935245827234907301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496671654644411919505605 468125935245827234907301)
                    ·
                      rfl

theorem cell22_1367508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1367508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367508 prefixEnd_1367508 := by exact prefixLift 1367508
  have htrace : WordTrace (prefixWord ++ tailWord_1367508) baseStart_1367508 baseEnd_1367508 := by
    simpa [prefixWord, tailWord_1367508, baseEnd_1367508] using wordTrace_append hprefix tailTrace_1367508
  have hstable : (prefixWord ++ tailWord_1367508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367508).length < 2 ^ (prefixWord ++ tailWord_1367508).sum := by decide
  have hdescent : baseEnd_1367508 < baseStart_1367508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367519 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 2, 4]
def baseStart_1367519 : Nat := 118140960795 + 1367519 * 2 ^ 59
def prefixEnd_1367519 : Nat := 4983230072969 + 3 ^ 40 * 1367519 * 2
def baseEnd_1367519 : Nat := 468129700770626872882267

theorem tailTrace_1367519 : CollatzResearch.WordTrace tailWord_1367519 prefixEnd_1367519 468129700770626872882267 := by
  unfold tailWord_1367519
  simp only [CollatzResearch.WordTrace]
  refine ⟨49877515532719691496153611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33251677021813127664102407 49877515532719691496153611)
  ·
    refine ⟨74816273299079537244230417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49877515532719691496153611 74816273299079537244230417)
    ·
      refine ⟨56112204974309652933172813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74816273299079537244230417 56112204974309652933172813)
      ·
        refine ⟨21042076865366119849939805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56112204974309652933172813 21042076865366119849939805)
        ·
          refine ⟨7890778824512294943727427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21042076865366119849939805 7890778824512294943727427)
          ·
            refine ⟨11836168236768442415591141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7890778824512294943727427 11836168236768442415591141)
            ·
              refine ⟨2219281544394082952923339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11836168236768442415591141 2219281544394082952923339)
              ·
                refine ⟨3328922316591124429385009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219281544394082952923339 3328922316591124429385009)
                ·
                  refine ⟨2496691737443343322038757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328922316591124429385009 2496691737443343322038757)
                  ·
                    refine ⟨468129700770626872882267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496691737443343322038757 468129700770626872882267)
                    ·
                      rfl

theorem cell22_1367519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_1367519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367519 prefixEnd_1367519 := by exact prefixLift 1367519
  have htrace : WordTrace (prefixWord ++ tailWord_1367519) baseStart_1367519 baseEnd_1367519 := by
    simpa [prefixWord, tailWord_1367519, baseEnd_1367519] using wordTrace_append hprefix tailTrace_1367519
  have hstable : (prefixWord ++ tailWord_1367519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367519).length < 2 ^ (prefixWord ++ tailWord_1367519).sum := by decide
  have hdescent : baseEnd_1367519 < baseStart_1367519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367538 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_1367538 : Nat := 118140960795 + 1367538 * 2 ^ 59
def prefixEnd_1367538 : Nat := 4983230072969 + 3 ^ 40 * 1367538 * 2
def baseEnd_1367538 : Nat := 468136204858917156657209

theorem tailTrace_1367538 : CollatzResearch.WordTrace tailWord_1367538 prefixEnd_1367538 468136204858917156657209 := by
  unfold tailWord_1367538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12469552129912714435273817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33252139013100571827396845 12469552129912714435273817)
  ·
    refine ⟨9352164097434535826455363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12469552129912714435273817 9352164097434535826455363)
    ·
      refine ⟨14028246146151803739683045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9352164097434535826455363 14028246146151803739683045)
      ·
        refine ⟨2630296152403463201190571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14028246146151803739683045 2630296152403463201190571)
        ·
          refine ⟨3945444228605194801785857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630296152403463201190571 3945444228605194801785857)
          ·
            refine ⟨2959083171453896101339393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3945444228605194801785857 2959083171453896101339393)
            ·
              refine ⟨2219312378590422076004545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959083171453896101339393 2219312378590422076004545)
              ·
                refine ⟨1664484283942816557003409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219312378590422076004545 1664484283942816557003409)
                ·
                  refine ⟨1248363212957112417752557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664484283942816557003409 1248363212957112417752557)
                  ·
                    refine ⟨468136204858917156657209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1248363212957112417752557 468136204858917156657209)
                    ·
                      rfl

theorem cell22_1367538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_1367538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367538 prefixEnd_1367538 := by exact prefixLift 1367538
  have htrace : WordTrace (prefixWord ++ tailWord_1367538) baseStart_1367538 baseEnd_1367538 := by
    simpa [prefixWord, tailWord_1367538, baseEnd_1367538] using wordTrace_append hprefix tailTrace_1367538
  have hstable : (prefixWord ++ tailWord_1367538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367538).length < 2 ^ (prefixWord ++ tailWord_1367538).sum := by decide
  have hdescent : baseEnd_1367538 < baseStart_1367538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367577 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_1367577 : Nat := 118140960795 + 1367577 * 2 ^ 59
def prefixEnd_1367577 : Nat := 4983230072969 + 3 ^ 40 * 1367577 * 2
def baseEnd_1367577 : Nat := 468149555355934054932089

theorem tailTrace_1367577 : CollatzResearch.WordTrace tailWord_1367577 prefixEnd_1367577 468149555355934054932089 := by
  unfold tailWord_1367577
  simp only [CollatzResearch.WordTrace]
  refine ⟨49879630966509567401764985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33253087311006378267843323 49879630966509567401764985)
  ·
    refine ⟨37409723224882175551323739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49879630966509567401764985 37409723224882175551323739)
    ·
      refine ⟨56114584837323263326985609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37409723224882175551323739 56114584837323263326985609)
      ·
        refine ⟨42085938627992447495239207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56114584837323263326985609 42085938627992447495239207)
        ·
          refine ⟨63128907941988671242858811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42085938627992447495239207 63128907941988671242858811)
          ·
            refine ⟨94693361912983006864288217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63128907941988671242858811 94693361912983006864288217)
            ·
              refine ⟨71020021434737255148216163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94693361912983006864288217 71020021434737255148216163)
              ·
                refine ⟨106530032152105882722324245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71020021434737255148216163 106530032152105882722324245)
                ·
                  refine ⟨4993595257129963252608949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106530032152105882722324245 4993595257129963252608949)
                  ·
                    refine ⟨468149555355934054932089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4993595257129963252608949 468149555355934054932089)
                    ·
                      rfl

theorem cell22_1367577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_1367577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367577 prefixEnd_1367577 := by exact prefixLift 1367577
  have htrace : WordTrace (prefixWord ++ tailWord_1367577) baseStart_1367577 baseEnd_1367577 := by
    simpa [prefixWord, tailWord_1367577, baseEnd_1367577] using wordTrace_append hprefix tailTrace_1367577
  have hstable : (prefixWord ++ tailWord_1367577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367577).length < 2 ^ (prefixWord ++ tailWord_1367577).sum := by decide
  have hdescent : baseEnd_1367577 < baseStart_1367577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367594 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1367594 : Nat := 118140960795 + 1367594 * 2 ^ 59
def prefixEnd_1367594 : Nat := 4983230072969 + 3 ^ 40 * 1367594 * 2
def baseEnd_1367594 : Nat := 468155374803351677257037

theorem tailTrace_1367594 : CollatzResearch.WordTrace tailWord_1367594 prefixEnd_1367594 468155374803351677257037 := by
  unfold tailWord_1367594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470062751861994826283459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33253500671631986203422557 12470062751861994826283459)
  ·
    refine ⟨18705094127792992239425189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12470062751861994826283459 18705094127792992239425189)
    ·
      refine ⟨3507205148961186044892223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18705094127792992239425189 3507205148961186044892223)
      ·
        refine ⟨5260807723441779067338335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507205148961186044892223 5260807723441779067338335)
        ·
          refine ⟨7891211585162668601007503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260807723441779067338335 7891211585162668601007503)
          ·
            refine ⟨11836817377744002901511255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7891211585162668601007503 11836817377744002901511255)
            ·
              refine ⟨17755226066616004352266883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11836817377744002901511255 17755226066616004352266883)
              ·
                refine ⟨26632839099924006528400325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17755226066616004352266883 26632839099924006528400325)
                ·
                  refine ⟨4993657331235751224075061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26632839099924006528400325 4993657331235751224075061)
                  ·
                    refine ⟨468155374803351677257037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4993657331235751224075061 468155374803351677257037)
                    ·
                      rfl

theorem cell22_1367594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1367594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367594 prefixEnd_1367594 := by exact prefixLift 1367594
  have htrace : WordTrace (prefixWord ++ tailWord_1367594) baseStart_1367594 baseEnd_1367594 := by
    simpa [prefixWord, tailWord_1367594, baseEnd_1367594] using wordTrace_append hprefix tailTrace_1367594
  have hstable : (prefixWord ++ tailWord_1367594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367594).length < 2 ^ (prefixWord ++ tailWord_1367594).sum := by decide
  have hdescent : baseEnd_1367594 < baseStart_1367594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367613 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 5]
def baseStart_1367613 : Nat := 118140960795 + 1367613 * 2 ^ 59
def prefixEnd_1367613 : Nat := 4983230072969 + 3 ^ 40 * 1367613 * 2
def baseEnd_1367613 : Nat := 156053959630547320343993

theorem tailTrace_1367613 : CollatzResearch.WordTrace tailWord_1367613 prefixEnd_1367613 156053959630547320343993 := by
  unfold tailWord_1367613
  simp only [CollatzResearch.WordTrace]
  refine ⟨49880943994379145550075493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33253962662919430366716995 49880943994379145550075493)
  ·
    refine ⟨9352676998946089790639155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49880943994379145550075493 9352676998946089790639155)
    ·
      refine ⟨14029015498419134685958733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9352676998946089790639155 14029015498419134685958733)
      ·
        refine ⟨5260880811907175507234525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14029015498419134685958733 5260880811907175507234525)
        ·
          refine ⟨1972830304465190815212947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5260880811907175507234525 1972830304465190815212947)
          ·
            refine ⟨2959245456697786222819421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972830304465190815212947 2959245456697786222819421)
            ·
              refine ⟨1109717046261669833557283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2959245456697786222819421 1109717046261669833557283)
              ·
                refine ⟨1664575569392504750335925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109717046261669833557283 1664575569392504750335925)
                ·
                  refine ⟨156053959630547320343993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664575569392504750335925 156053959630547320343993)
                  ·
                    rfl

theorem cell22_1367613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_1367613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367613 prefixEnd_1367613 := by exact prefixLift 1367613
  have htrace : WordTrace (prefixWord ++ tailWord_1367613) baseStart_1367613 baseEnd_1367613 := by
    simpa [prefixWord, tailWord_1367613, baseEnd_1367613] using wordTrace_append hprefix tailTrace_1367613
  have hstable : (prefixWord ++ tailWord_1367613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367613).length < 2 ^ (prefixWord ++ tailWord_1367613).sum := by decide
  have hdescent : baseEnd_1367613 < baseStart_1367613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367626 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1367626 : Nat := 118140960795 + 1367626 * 2 ^ 59
def prefixEnd_1367626 : Nat := 4983230072969 + 3 ^ 40 * 1367626 * 2
def baseEnd_1367626 : Nat := 468166329057314260456939

theorem tailTrace_1367626 : CollatzResearch.WordTrace tailWord_1367626 prefixEnd_1367626 468166329057314260456939 := by
  unfold tailWord_1367626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470354535833012192574683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33254278762221365846865821 12470354535833012192574683)
  ·
    refine ⟨18705531803749518288862025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12470354535833012192574683 18705531803749518288862025)
    ·
      refine ⟨14029148852812138716646519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18705531803749518288862025 14029148852812138716646519)
      ·
        refine ⟨21043723279218208074969779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14029148852812138716646519 21043723279218208074969779)
        ·
          refine ⟨31565584918827312112454669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21043723279218208074969779 31565584918827312112454669)
          ·
            refine ⟨11837094344560242042170501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31565584918827312112454669 11837094344560242042170501)
            ·
              refine ⟨2219455189605045382906969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11837094344560242042170501 2219455189605045382906969)
              ·
                refine ⟨1664591392203784037180227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219455189605045382906969 1664591392203784037180227)
                ·
                  refine ⟨2496887088305676055770341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664591392203784037180227 2496887088305676055770341)
                  ·
                    refine ⟨468166329057314260456939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496887088305676055770341 468166329057314260456939)
                    ·
                      rfl

theorem cell22_1367626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1367626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367626 prefixEnd_1367626 := by exact prefixLift 1367626
  have htrace : WordTrace (prefixWord ++ tailWord_1367626) baseStart_1367626 baseEnd_1367626 := by
    simpa [prefixWord, tailWord_1367626, baseEnd_1367626] using wordTrace_append hprefix tailTrace_1367626
  have hstable : (prefixWord ++ tailWord_1367626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367626).length < 2 ^ (prefixWord ++ tailWord_1367626).sum := by decide
  have hdescent : baseEnd_1367626 < baseStart_1367626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367881 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_1367881 : Nat := 118140960795 + 1367881 * 2 ^ 59
def prefixEnd_1367881 : Nat := 4983230072969 + 3 ^ 40 * 1367881 * 2
def baseEnd_1367881 : Nat := 468253620768578595331157

theorem tailTrace_1367881 : CollatzResearch.WordTrace tailWord_1367881 prefixEnd_1367881 468253620768578595331157 := by
  unfold tailWord_1367881
  simp only [CollatzResearch.WordTrace]
  refine ⟨49890718757408227320831497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33260479171605484880554331 49890718757408227320831497)
  ·
    refine ⟨37418039068056170490623623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49890718757408227320831497 37418039068056170490623623)
    ·
      refine ⟨56127058602084255735935435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37418039068056170490623623 56127058602084255735935435)
      ·
        refine ⟨84190587903126383603903153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56127058602084255735935435 84190587903126383603903153)
        ·
          refine ⟨63142940927344787702927365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84190587903126383603903153 63142940927344787702927365)
          ·
            refine ⟨11839301423877147694298881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63142940927344787702927365 11839301423877147694298881)
            ·
              refine ⟨8879476067907860770724161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11839301423877147694298881 8879476067907860770724161)
              ·
                refine ⟨6659607050930895578043121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8879476067907860770724161 6659607050930895578043121)
                ·
                  refine ⟨4994705288198171683532341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659607050930895578043121 4994705288198171683532341)
                  ·
                    refine ⟨468253620768578595331157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4994705288198171683532341 468253620768578595331157)
                    ·
                      rfl

theorem cell22_1367881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_1367881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367881 prefixEnd_1367881 := by exact prefixLift 1367881
  have htrace : WordTrace (prefixWord ++ tailWord_1367881) baseStart_1367881 baseEnd_1367881 := by
    simpa [prefixWord, tailWord_1367881, baseEnd_1367881] using wordTrace_append hprefix tailTrace_1367881
  have hstable : (prefixWord ++ tailWord_1367881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367881).length < 2 ^ (prefixWord ++ tailWord_1367881).sum := by decide
  have hdescent : baseEnd_1367881 < baseStart_1367881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367930 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_1367930 : Nat := 118140960795 + 1367930 * 2 ^ 59
def prefixEnd_1367930 : Nat := 4983230072969 + 3 ^ 40 * 1367930 * 2
def baseEnd_1367930 : Nat := 468270394469958800856007

theorem tailTrace_1367930 : CollatzResearch.WordTrace tailWord_1367930 prefixEnd_1367930 468270394469958800856007 := by
  unfold tailWord_1367930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12473126483557677172341311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33261670622820472459576829 12473126483557677172341311)
  ·
    refine ⟨18709689725336515758511967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12473126483557677172341311 18709689725336515758511967)
    ·
      refine ⟨28064534588004773637767951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18709689725336515758511967 28064534588004773637767951)
      ·
        refine ⟨42096801882007160456651927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28064534588004773637767951 42096801882007160456651927)
        ·
          refine ⟨63145202823010740684977891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42096801882007160456651927 63145202823010740684977891)
          ·
            refine ⟨94717804234516111027466837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63145202823010740684977891 94717804234516111027466837)
            ·
              refine ⟨1109974268373235676103127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 94717804234516111027466837 1109974268373235676103127)
              ·
                refine ⟨1664961402559853514154691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109974268373235676103127 1664961402559853514154691)
                ·
                  refine ⟨2497442103839780271232037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664961402559853514154691 2497442103839780271232037)
                  ·
                    refine ⟨468270394469958800856007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2497442103839780271232037 468270394469958800856007)
                    ·
                      rfl

theorem cell22_1367930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_1367930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367930 prefixEnd_1367930 := by exact prefixLift 1367930
  have htrace : WordTrace (prefixWord ++ tailWord_1367930) baseStart_1367930 baseEnd_1367930 := by
    simpa [prefixWord, tailWord_1367930, baseEnd_1367930] using wordTrace_append hprefix tailTrace_1367930
  have hstable : (prefixWord ++ tailWord_1367930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367930).length < 2 ^ (prefixWord ++ tailWord_1367930).sum := by decide
  have hdescent : baseEnd_1367930 < baseStart_1367930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367971 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 9]
def baseStart_1367971 : Nat := 118140960795 + 1367971 * 2 ^ 59
def prefixEnd_1367971 : Nat := 4983230072969 + 3 ^ 40 * 1367971 * 2
def baseEnd_1367971 : Nat := 468284429607848360580881

theorem tailTrace_1367971 : CollatzResearch.WordTrace tailWord_1367971 prefixEnd_1367971 468284429607848360580881 := by
  unfold tailWord_1367971
  simp only [CollatzResearch.WordTrace]
  refine ⟨49894001327082172691607767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33262667551388115127738511 49894001327082172691607767)
  ·
    refine ⟨74841001990623259037411651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49894001327082172691607767 74841001990623259037411651)
    ·
      refine ⟨112261502985934888556117477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74841001990623259037411651 112261502985934888556117477)
      ·
        refine ⟨21049031809862791604272027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112261502985934888556117477 21049031809862791604272027)
        ·
          refine ⟨31573547714794187406408041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21049031809862791604272027 31573547714794187406408041)
          ·
            refine ⟨23680160786095640554806031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31573547714794187406408041 23680160786095640554806031)
            ·
              refine ⟨35520241179143460832209047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23680160786095640554806031 35520241179143460832209047)
              ·
                refine ⟨53280361768715191248313571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35520241179143460832209047 53280361768715191248313571)
                ·
                  refine ⟨79920542653072786872470357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53280361768715191248313571 79920542653072786872470357)
                  ·
                    refine ⟨468284429607848360580881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79920542653072786872470357 468284429607848360580881)
                    ·
                      rfl

theorem cell22_1367971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_1367971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367971 prefixEnd_1367971 := by exact prefixLift 1367971
  have htrace : WordTrace (prefixWord ++ tailWord_1367971) baseStart_1367971 baseEnd_1367971 := by
    simpa [prefixWord, tailWord_1367971, baseEnd_1367971] using wordTrace_append hprefix tailTrace_1367971
  have hstable : (prefixWord ++ tailWord_1367971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367971).length < 2 ^ (prefixWord ++ tailWord_1367971).sum := by decide
  have hdescent : baseEnd_1367971 < baseStart_1367971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368095 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 4, 3]
def baseStart_1368095 : Nat := 118140960795 + 1368095 * 2 ^ 59
def prefixEnd_1368095 : Nat := 4983230072969 + 3 ^ 40 * 1368095 * 2
def baseEnd_1368095 : Nat := 468326877341953370480501

theorem tailTrace_1368095 : CollatzResearch.WordTrace tailWord_1368095 prefixEnd_1368095 468326877341953370480501 := by
  unfold tailWord_1368095
  simp only [CollatzResearch.WordTrace]
  refine ⟨49898523978632941869121739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33265682652421961246081159 49898523978632941869121739)
  ·
    refine ⟨74847785967949412803682609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49898523978632941869121739 74847785967949412803682609)
    ·
      refine ⟨56135839475962059602761957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74847785967949412803682609 56135839475962059602761957)
      ·
        refine ⟨10525469901742886175517867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56135839475962059602761957 10525469901742886175517867)
        ·
          refine ⟨15788204852614329263276801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10525469901742886175517867 15788204852614329263276801)
          ·
            refine ⟨11841153639460746947457601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15788204852614329263276801 11841153639460746947457601)
            ·
              refine ⟨8880865229595560210593201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11841153639460746947457601 8880865229595560210593201)
              ·
                refine ⟨6660648922196670157944901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8880865229595560210593201 6660648922196670157944901)
                ·
                  refine ⟨1248871672911875654614669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6660648922196670157944901 1248871672911875654614669)
                  ·
                    refine ⟨468326877341953370480501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1248871672911875654614669 468326877341953370480501)
                    ·
                      rfl

theorem cell22_1368095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_1368095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368095 prefixEnd_1368095 := by exact prefixLift 1368095
  have htrace : WordTrace (prefixWord ++ tailWord_1368095) baseStart_1368095 baseEnd_1368095 := by
    simpa [prefixWord, tailWord_1368095, baseEnd_1368095] using wordTrace_append hprefix tailTrace_1368095
  have hstable : (prefixWord ++ tailWord_1368095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368095).length < 2 ^ (prefixWord ++ tailWord_1368095).sum := by decide
  have hdescent : baseEnd_1368095 < baseStart_1368095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368112 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 2, 3]
def baseStart_1368112 : Nat := 118140960795 + 1368112 * 2 ^ 59
def prefixEnd_1368112 : Nat := 4983230072969 + 3 ^ 40 * 1368112 * 2
def baseEnd_1368112 : Nat := 468332696789370992805449

theorem tailTrace_1368112 : CollatzResearch.WordTrace tailWord_1368112 prefixEnd_1368112 468332696789370992805449 := by
  unfold tailWord_1368112
  simp only [CollatzResearch.WordTrace]
  refine ⟨24949572009785676886245295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33266096013047569181660393 24949572009785676886245295)
  ·
    refine ⟨37424358014678515329367943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24949572009785676886245295 37424358014678515329367943)
    ·
      refine ⟨56136537022017772994051915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37424358014678515329367943 56136537022017772994051915)
      ·
        refine ⟨84204805533026659491077873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56136537022017772994051915 84204805533026659491077873)
        ·
          refine ⟨63153604149769994618308405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84204805533026659491077873 63153604149769994618308405)
          ·
            refine ⟨5920650389040936995466413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63153604149769994618308405 5920650389040936995466413)
            ·
              refine ⟨2220243895890351373299905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5920650389040936995466413 2220243895890351373299905)
              ·
                refine ⟨1665182921917763529974929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2220243895890351373299905 1665182921917763529974929)
                ·
                  refine ⟨1248887191438322647481197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1665182921917763529974929 1248887191438322647481197)
                  ·
                    refine ⟨468332696789370992805449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1248887191438322647481197 468332696789370992805449)
                    ·
                      rfl

theorem cell22_1368112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_1368112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368112 prefixEnd_1368112 := by exact prefixLift 1368112
  have htrace : WordTrace (prefixWord ++ tailWord_1368112) baseStart_1368112 baseEnd_1368112 := by
    simpa [prefixWord, tailWord_1368112, baseEnd_1368112] using wordTrace_append hprefix tailTrace_1368112
  have hstable : (prefixWord ++ tailWord_1368112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368112).length < 2 ^ (prefixWord ++ tailWord_1368112).sum := by decide
  have hdescent : baseEnd_1368112 < baseStart_1368112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368142 : List Nat := [4, 1, 1, 1, 1, 6, 2, 6]
def baseStart_1368142 : Nat := 118140960795 + 1368142 * 2 ^ 59
def prefixEnd_1368142 : Nat := 4983230072969 + 3 ^ 40 * 1368142 * 2
def baseEnd_1368142 : Nat := 52038107378051212728373

theorem tailTrace_1368142 : CollatzResearch.WordTrace tailWord_1368142 prefixEnd_1368142 52038107378051212728373 := by
  unfold tailWord_1368142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6237529776182833612010335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33266825472975112597388453 6237529776182833612010335)
  ·
    refine ⟨9356294664274250418015503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6237529776182833612010335 9356294664274250418015503)
    ·
      refine ⟨14034441996411375627023255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9356294664274250418015503 14034441996411375627023255)
      ·
        refine ⟨21051662994617063440534883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14034441996411375627023255 21051662994617063440534883)
        ·
          refine ⟨31577494491925595160802325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21051662994617063440534883 31577494491925595160802325)
          ·
            refine ⟨1480195054309012273162609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31577494491925595160802325 1480195054309012273162609)
            ·
              refine ⟨1110146290731759204871957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480195054309012273162609 1110146290731759204871957)
              ·
                refine ⟨52038107378051212728373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1110146290731759204871957 52038107378051212728373)
                ·
                  rfl

theorem cell22_1368142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_1368142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368142 prefixEnd_1368142 := by exact prefixLift 1368142
  have htrace : WordTrace (prefixWord ++ tailWord_1368142) baseStart_1368142 baseEnd_1368142 := by
    simpa [prefixWord, tailWord_1368142, baseEnd_1368142] using wordTrace_append hprefix tailTrace_1368142
  have hstable : (prefixWord ++ tailWord_1368142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368142).length < 2 ^ (prefixWord ++ tailWord_1368142).sum := by decide
  have hdescent : baseEnd_1368142 < baseStart_1368142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368153 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 9]
def baseStart_1368153 : Nat := 118140960795 + 1368153 * 2 ^ 59
def prefixEnd_1368153 : Nat := 4983230072969 + 3 ^ 40 * 1368153 * 2
def baseEnd_1368153 : Nat := 156115577309086850843441

theorem tailTrace_1368153 : CollatzResearch.WordTrace tailWord_1368153 prefixEnd_1368153 156115577309086850843441 := by
  unfold tailWord_1368153
  simp only [CollatzResearch.WordTrace]
  refine ⟨49900639412422817774733113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33267092941615211849822075 49900639412422817774733113)
  ·
    refine ⟨37425479559317113331049835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49900639412422817774733113 37425479559317113331049835)
    ·
      refine ⟨56138219338975669996574753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37425479559317113331049835 56138219338975669996574753)
      ·
        refine ⟨42103664504231752497431065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56138219338975669996574753 42103664504231752497431065)
        ·
          refine ⟨31577748378173814373073299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42103664504231752497431065 31577748378173814373073299)
          ·
            refine ⟨47366622567260721559609949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31577748378173814373073299 47366622567260721559609949)
            ·
              refine ⟨17762483462722770584853731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47366622567260721559609949 17762483462722770584853731)
              ·
                refine ⟨26643725194084155877280597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17762483462722770584853731 26643725194084155877280597)
                ·
                  refine ⟨156115577309086850843441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26643725194084155877280597 156115577309086850843441)
                  ·
                    rfl

theorem cell22_1368153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_1368153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368153 prefixEnd_1368153 := by exact prefixLift 1368153
  have htrace : WordTrace (prefixWord ++ tailWord_1368153) baseStart_1368153 baseEnd_1368153 := by
    simpa [prefixWord, tailWord_1368153, baseEnd_1368153] using wordTrace_append hprefix tailTrace_1368153
  have hstable : (prefixWord ++ tailWord_1368153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368153).length < 2 ^ (prefixWord ++ tailWord_1368153).sum := by decide
  have hdescent : baseEnd_1368153 < baseStart_1368153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368247 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 1, 5]
def baseStart_1368247 : Nat := 118140960795 + 1368247 * 2 ^ 59
def prefixEnd_1368247 : Nat := 4983230072969 + 3 ^ 40 * 1368247 * 2
def baseEnd_1368247 : Nat := 468378910048275640680035

theorem tailTrace_1368247 : CollatzResearch.WordTrace tailWord_1368247 prefixEnd_1368247 468378910048275640680035 := by
  unfold tailWord_1368247
  simp only [CollatzResearch.WordTrace]
  refine ⟨49904067874082271828654995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33269378582721514552436663 49904067874082271828654995)
  ·
    refine ⟨74856101811123407742982493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49904067874082271828654995 74856101811123407742982493)
    ·
      refine ⟨28071038179171277903618435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74856101811123407742982493 28071038179171277903618435)
      ·
        refine ⟨42106557268756916855427653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28071038179171277903618435 42106557268756916855427653)
        ·
          refine ⟨7894979487891921910392685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42106557268756916855427653 7894979487891921910392685)
          ·
            refine ⟨2960617307959470716397257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7894979487891921910392685 2960617307959470716397257)
            ·
              refine ⟨2220462980969603037297943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2960617307959470716397257 2220462980969603037297943)
              ·
                refine ⟨3330694471454404555946915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220462980969603037297943 3330694471454404555946915)
                ·
                  refine ⟨4996041707181606833920373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330694471454404555946915 4996041707181606833920373)
                  ·
                    refine ⟨468378910048275640680035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4996041707181606833920373 468378910048275640680035)
                    ·
                      rfl

theorem cell22_1368247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_1368247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368247 prefixEnd_1368247 := by exact prefixLift 1368247
  have htrace : WordTrace (prefixWord ++ tailWord_1368247) baseStart_1368247 baseEnd_1368247 := by
    simpa [prefixWord, tailWord_1368247, baseEnd_1368247] using wordTrace_append hprefix tailTrace_1368247
  have hstable : (prefixWord ++ tailWord_1368247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368247).length < 2 ^ (prefixWord ++ tailWord_1368247).sum := by decide
  have hdescent : baseEnd_1368247 < baseStart_1368247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368268 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_1368268 : Nat := 118140960795 + 1368268 * 2 ^ 59
def prefixEnd_1368268 : Nat := 4983230072969 + 3 ^ 40 * 1368268 * 2
def baseEnd_1368268 : Nat := 468386098777438585904971

theorem tailTrace_1368268 : CollatzResearch.WordTrace tailWord_1368268 prefixEnd_1368268 468386098777438585904971 := by
  unfold tailWord_1368268
  simp only [CollatzResearch.WordTrace]
  refine ⟨24952416903503096207584729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33269889204670794943446305 24952416903503096207584729)
  ·
    refine ⟨18714312677627322155688547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24952416903503096207584729 18714312677627322155688547)
    ·
      refine ⟨28071469016440983233532821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18714312677627322155688547 28071469016440983233532821)
      ·
        refine ⟨1315850110145671089071851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28071469016440983233532821 1315850110145671089071851)
        ·
          refine ⟨1973775165218506633607777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315850110145671089071851 1973775165218506633607777)
          ·
            refine ⟨1480331373913879975205833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1973775165218506633607777 1480331373913879975205833)
            ·
              refine ⟨1110248530435409981404375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480331373913879975205833 1110248530435409981404375)
              ·
                refine ⟨1665372795653114972106563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110248530435409981404375 1665372795653114972106563)
                ·
                  refine ⟨2498059193479672458159845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665372795653114972106563 2498059193479672458159845)
                  ·
                    refine ⟨468386098777438585904971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498059193479672458159845 468386098777438585904971)
                    ·
                      rfl

theorem cell22_1368268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_1368268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368268 prefixEnd_1368268 := by exact prefixLift 1368268
  have htrace : WordTrace (prefixWord ++ tailWord_1368268) baseStart_1368268 baseEnd_1368268 := by
    simpa [prefixWord, tailWord_1368268, baseEnd_1368268] using wordTrace_append hprefix tailTrace_1368268
  have hstable : (prefixWord ++ tailWord_1368268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368268).length < 2 ^ (prefixWord ++ tailWord_1368268).sum := by decide
  have hdescent : baseEnd_1368268 < baseStart_1368268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368277 : List Nat := [1, 3, 2, 4, 2, 1, 9]
def baseStart_1368277 : Nat := 118140960795 + 1368277 * 2 ^ 59
def prefixEnd_1368277 : Nat := 4983230072969 + 3 ^ 40 * 1368277 * 2
def baseEnd_1368277 : Nat := 17347747394865391201109

theorem tailTrace_1368277 : CollatzResearch.WordTrace tailWord_1368277 prefixEnd_1368277 17347747394865391201109 := by
  unfold tailWord_1368277
  simp only [CollatzResearch.WordTrace]
  refine ⟨49905162063973586952247085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33270108042649057968164723 49905162063973586952247085)
  ·
    refine ⟨18714435773990095107092657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49905162063973586952247085 18714435773990095107092657)
    ·
      refine ⟨14035826830492571330319493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18714435773990095107092657 14035826830492571330319493)
      ·
        refine ⟨2631717530717357124434905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14035826830492571330319493 2631717530717357124434905)
        ·
          refine ⟨1973788148038017843326179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631717530717357124434905 1973788148038017843326179)
          ·
            refine ⟨2960682222057026764989269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973788148038017843326179 2960682222057026764989269)
            ·
              refine ⟨17347747394865391201109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2960682222057026764989269 17347747394865391201109)
              ·
                rfl

theorem cell22_1368277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 9].length) (baseStart_1368277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368277 prefixEnd_1368277 := by exact prefixLift 1368277
  have htrace : WordTrace (prefixWord ++ tailWord_1368277) baseStart_1368277 baseEnd_1368277 := by
    simpa [prefixWord, tailWord_1368277, baseEnd_1368277] using wordTrace_append hprefix tailTrace_1368277
  have hstable : (prefixWord ++ tailWord_1368277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368277).length < 2 ^ (prefixWord ++ tailWord_1368277).sum := by decide
  have hdescent : baseEnd_1368277 < baseStart_1368277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368320 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_1368320 : Nat := 118140960795 + 1368320 * 2 ^ 59
def prefixEnd_1368320 : Nat := 4983230072969 + 3 ^ 40 * 1368320 * 2
def baseEnd_1368320 : Nat := 468403899440127783604811

theorem tailTrace_1368320 : CollatzResearch.WordTrace tailWord_1368320 prefixEnd_1368320 468403899440127783604811 := by
  unfold tailWord_1368320
  simp only [CollatzResearch.WordTrace]
  refine ⟨24953365201408902648031207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33271153601878536864041609 24953365201408902648031207)
  ·
    refine ⟨37430047802113353972046811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24953365201408902648031207 37430047802113353972046811)
    ·
      refine ⟨56145071703170030958070217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37430047802113353972046811 56145071703170030958070217)
      ·
        refine ⟨42108803777377523218552663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56145071703170030958070217 42108803777377523218552663)
        ·
          refine ⟨63163205666066284827828995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42108803777377523218552663 63163205666066284827828995)
          ·
            refine ⟨94744808499099427241743493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63163205666066284827828995 94744808499099427241743493)
            ·
              refine ⟨17764651593581142607826905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94744808499099427241743493 17764651593581142607826905)
              ·
                refine ⟨13323488695185856955870179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17764651593581142607826905 13323488695185856955870179)
                ·
                  refine ⟨19985233042778785433805269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13323488695185856955870179 19985233042778785433805269)
                  ·
                    refine ⟨468403899440127783604811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19985233042778785433805269 468403899440127783604811)
                    ·
                      rfl

theorem cell22_1368320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_1368320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368320 prefixEnd_1368320 := by exact prefixLift 1368320
  have htrace : WordTrace (prefixWord ++ tailWord_1368320) baseStart_1368320 baseEnd_1368320 := by
    simpa [prefixWord, tailWord_1368320, baseEnd_1368320] using wordTrace_append hprefix tailTrace_1368320
  have hstable : (prefixWord ++ tailWord_1368320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368320).length < 2 ^ (prefixWord ++ tailWord_1368320).sum := by decide
  have hdescent : baseEnd_1368320 < baseStart_1368320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368343 : List Nat := [1, 1, 3, 4, 1, 3, 3, 2, 1, 3]
def baseStart_1368343 : Nat := 118140960795 + 1368343 * 2 ^ 59
def prefixEnd_1368343 : Nat := 4983230072969 + 3 ^ 40 * 1368343 * 2
def baseEnd_1368343 : Nat := 468411772810163390279741

theorem tailTrace_1368343 : CollatzResearch.WordTrace tailWord_1368343 prefixEnd_1368343 468411772810163390279741 := by
  unfold tailWord_1368343
  simp only [CollatzResearch.WordTrace]
  refine ⟨49907569281734480224149683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33271712854489653482766455 49907569281734480224149683)
  ·
    refine ⟨74861353922601720336224525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49907569281734480224149683 74861353922601720336224525)
    ·
      refine ⟨28073007720975645126084197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74861353922601720336224525 28073007720975645126084197)
      ·
        refine ⟨5263688947682933461140787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28073007720975645126084197 5263688947682933461140787)
        ·
          refine ⟨7895533421524400191711181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5263688947682933461140787 7895533421524400191711181)
          ·
            refine ⟨2960825033071650071891693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7895533421524400191711181 2960825033071650071891693)
            ·
              refine ⟨1110309387401868776959385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2960825033071650071891693 1110309387401868776959385)
              ·
                refine ⟨832732040551401582719539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110309387401868776959385 832732040551401582719539)
                ·
                  refine ⟨1249098060827102374079309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832732040551401582719539 1249098060827102374079309)
                  ·
                    refine ⟨468411772810163390279741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249098060827102374079309 468411772810163390279741)
                    ·
                      rfl

theorem cell22_1368343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_1368343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368343 prefixEnd_1368343 := by exact prefixLift 1368343
  have htrace : WordTrace (prefixWord ++ tailWord_1368343) baseStart_1368343 baseEnd_1368343 := by
    simpa [prefixWord, tailWord_1368343, baseEnd_1368343] using wordTrace_append hprefix tailTrace_1368343
  have hstable : (prefixWord ++ tailWord_1368343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368343).length < 2 ^ (prefixWord ++ tailWord_1368343).sum := by decide
  have hdescent : baseEnd_1368343 < baseStart_1368343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368356 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1368356 : Nat := 118140960795 + 1368356 * 2 ^ 59
def prefixEnd_1368356 : Nat := 4983230072969 + 3 ^ 40 * 1368356 * 2
def baseEnd_1368356 : Nat := 156138740991945229901567

theorem tailTrace_1368356 : CollatzResearch.WordTrace tailWord_1368356 prefixEnd_1368356 156138740991945229901567 := by
  unfold tailWord_1368356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24954021715343691722186461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33272028953791588962915281 24954021715343691722186461)
  ·
    refine ⟨9357758143253884395819923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24954021715343691722186461 9357758143253884395819923)
    ·
      refine ⟨14036637214880826593729885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9357758143253884395819923 14036637214880826593729885)
      ·
        refine ⟨5263738955580309972648707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14036637214880826593729885 5263738955580309972648707)
        ·
          refine ⟨7895608433370464958973061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5263738955580309972648707 7895608433370464958973061)
          ·
            refine ⟨1480426581256962179807449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7895608433370464958973061 1480426581256962179807449)
            ·
              refine ⟨1110319935942721634855587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480426581256962179807449 1110319935942721634855587)
              ·
                refine ⟨1665479903914082452283381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110319935942721634855587 1665479903914082452283381)
                ·
                  refine ⟨156138740991945229901567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1665479903914082452283381 156138740991945229901567)
                  ·
                    rfl

theorem cell22_1368356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1368356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368356 prefixEnd_1368356 := by exact prefixLift 1368356
  have htrace : WordTrace (prefixWord ++ tailWord_1368356) baseStart_1368356 baseEnd_1368356 := by
    simpa [prefixWord, tailWord_1368356, baseEnd_1368356] using wordTrace_append hprefix tailTrace_1368356
  have hstable : (prefixWord ++ tailWord_1368356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368356).length < 2 ^ (prefixWord ++ tailWord_1368356).sum := by decide
  have hdescent : baseEnd_1368356 < baseStart_1368356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368369 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_1368369 : Nat := 118140960795 + 1368369 * 2 ^ 59
def prefixEnd_1368369 : Nat := 4983230072969 + 3 ^ 40 * 1368369 * 2
def baseEnd_1368369 : Nat := 468420673141507989129661

theorem tailTrace_1368369 : CollatzResearch.WordTrace tailWord_1368369 prefixEnd_1368369 468420673141507989129661 := by
  unfold tailWord_1368369
  simp only [CollatzResearch.WordTrace]
  refine ⟨49908517579640286664596161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33272345053093524443064107 49908517579640286664596161)
  ·
    refine ⟨37431388184730214998447121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49908517579640286664596161 37431388184730214998447121)
    ·
      refine ⟨28073541138547661248835341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37431388184730214998447121 28073541138547661248835341)
      ·
        refine ⟨10527577926955372968313253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28073541138547661248835341 10527577926955372968313253)
        ·
          refine ⟨1973920861304132431558735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10527577926955372968313253 1973920861304132431558735)
          ·
            refine ⟨2960881291956198647338103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973920861304132431558735 2960881291956198647338103)
            ·
              refine ⟨4441321937934297971007155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960881291956198647338103 4441321937934297971007155)
              ·
                refine ⟨6661982906901446956510733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441321937934297971007155 6661982906901446956510733)
                ·
                  refine ⟨2498243590088042608691525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6661982906901446956510733 2498243590088042608691525)
                  ·
                    refine ⟨468420673141507989129661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498243590088042608691525 468420673141507989129661)
                    ·
                      rfl

theorem cell22_1368369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_1368369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368369 prefixEnd_1368369 := by exact prefixLift 1368369
  have htrace : WordTrace (prefixWord ++ tailWord_1368369) baseStart_1368369 baseEnd_1368369 := by
    simpa [prefixWord, tailWord_1368369, baseEnd_1368369] using wordTrace_append hprefix tailTrace_1368369
  have hstable : (prefixWord ++ tailWord_1368369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368369).length < 2 ^ (prefixWord ++ tailWord_1368369).sum := by decide
  have hdescent : baseEnd_1368369 < baseStart_1368369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368401 : List Nat := [1, 2, 2, 1, 4, 2, 4, 2, 4]
def baseStart_1368401 : Nat := 118140960795 + 1368401 * 2 ^ 59
def prefixEnd_1368401 : Nat := 4983230072969 + 3 ^ 40 * 1368401 * 2
def baseEnd_1368401 : Nat := 156143875798490190776521

theorem tailTrace_1368401 : CollatzResearch.WordTrace tailWord_1368401 prefixEnd_1368401 156143875798490190776521 := by
  unfold tailWord_1368401
  simp only [CollatzResearch.WordTrace]
  refine ⟨49909684715524356129761057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33273123143682904086507371 49909684715524356129761057)
  ·
    refine ⟨37432263536643267097320793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49909684715524356129761057 37432263536643267097320793)
    ·
      refine ⟨28074197652482450322990595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37432263536643267097320793 28074197652482450322990595)
      ·
        refine ⟨42111296478723675484485893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28074197652482450322990595 42111296478723675484485893)
        ·
          refine ⟨7895868089760689153341105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42111296478723675484485893 7895868089760689153341105)
          ·
            refine ⟨5921901067320516865005829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7895868089760689153341105 5921901067320516865005829)
            ·
              refine ⟨1110356450122596912188593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5921901067320516865005829 1110356450122596912188593)
              ·
                refine ⟨832767337591947684141445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110356450122596912188593 832767337591947684141445)
                ·
                  refine ⟨156143875798490190776521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832767337591947684141445 156143875798490190776521)
                  ·
                    rfl

theorem cell22_1368401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_1368401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368401 prefixEnd_1368401 := by exact prefixLift 1368401
  have htrace : WordTrace (prefixWord ++ tailWord_1368401) baseStart_1368401 baseEnd_1368401 := by
    simpa [prefixWord, tailWord_1368401, baseEnd_1368401] using wordTrace_append hprefix tailTrace_1368401
  have hstable : (prefixWord ++ tailWord_1368401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368401).length < 2 ^ (prefixWord ++ tailWord_1368401).sum := by decide
  have hdescent : baseEnd_1368401 < baseStart_1368401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368429 : List Nat := [1, 5, 1, 1, 1, 2, 5, 6]
def baseStart_1368429 : Nat := 118140960795 + 1368429 * 2 ^ 59
def prefixEnd_1368429 : Nat := 4983230072969 + 3 ^ 40 * 1368429 * 2
def baseEnd_1368429 : Nat := 52049023596409759181053

theorem tailTrace_1368429 : CollatzResearch.WordTrace tailWord_1368429 prefixEnd_1368429 52049023596409759181053 := by
  unfold tailWord_1368429
  simp only [CollatzResearch.WordTrace]
  refine ⟨49910705959422916911780341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33273803972948611274520227 49910705959422916911780341)
  ·
    refine ⟨4679128683695898460479407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49910705959422916911780341 4679128683695898460479407)
    ·
      refine ⟨7018693025543847690719111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4679128683695898460479407 7018693025543847690719111)
      ·
        refine ⟨10528039538315771536078667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7018693025543847690719111 10528039538315771536078667)
        ·
          refine ⟨15792059307473657304118001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10528039538315771536078667 15792059307473657304118001)
          ·
            refine ⟨11844044480605242978088501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15792059307473657304118001 11844044480605242978088501)
            ·
              refine ⟨1110379170056741529195797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11844044480605242978088501 1110379170056741529195797)
              ·
                refine ⟨52049023596409759181053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1110379170056741529195797 52049023596409759181053)
                ·
                  rfl

theorem cell22_1368429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 6].length) (baseStart_1368429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368429 prefixEnd_1368429 := by exact prefixLift 1368429
  have htrace : WordTrace (prefixWord ++ tailWord_1368429) baseStart_1368429 baseEnd_1368429 := by
    simpa [prefixWord, tailWord_1368429, baseEnd_1368429] using wordTrace_append hprefix tailTrace_1368429
  have hstable : (prefixWord ++ tailWord_1368429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368429).length < 2 ^ (prefixWord ++ tailWord_1368429).sum := by decide
  have hdescent : baseEnd_1368429 < baseStart_1368429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368478 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1368478 : Nat := 118140960795 + 1368478 * 2 ^ 59
def prefixEnd_1368478 : Nat := 4983230072969 + 3 ^ 40 * 1368478 * 2
def baseEnd_1368478 : Nat := 468457986069068038154327

theorem tailTrace_1368478 : CollatzResearch.WordTrace tailWord_1368478 prefixEnd_1368478 468457986069068038154327 := by
  unfold tailWord_1368478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239061642030674785039261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33274995424163598853542725 6239061642030674785039261)
  ·
    refine ⟨2339648115761503044389723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6239061642030674785039261 2339648115761503044389723)
    ·
      refine ⟨3509472173642254566584585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339648115761503044389723 3509472173642254566584585)
      ·
        refine ⟨2632104130231690924938439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3509472173642254566584585 2632104130231690924938439)
        ·
          refine ⟨3948156195347536387407659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632104130231690924938439 3948156195347536387407659)
          ·
            refine ⟨5922234293021304581111489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948156195347536387407659 5922234293021304581111489)
            ·
              refine ⟨4441675719765978435833617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922234293021304581111489 4441675719765978435833617)
              ·
                refine ⟨3331256789824483826875213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4441675719765978435833617 3331256789824483826875213)
                ·
                  refine ⟨1249221296184181435078205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3331256789824483826875213 1249221296184181435078205)
                  ·
                    refine ⟨468457986069068038154327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249221296184181435078205 468457986069068038154327)
                    ·
                      rfl

theorem cell22_1368478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1368478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368478 prefixEnd_1368478 := by exact prefixLift 1368478
  have htrace : WordTrace (prefixWord ++ tailWord_1368478) baseStart_1368478 baseEnd_1368478 := by
    simpa [prefixWord, tailWord_1368478, baseEnd_1368478] using wordTrace_append hprefix tailTrace_1368478
  have hstable : (prefixWord ++ tailWord_1368478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368478).length < 2 ^ (prefixWord ++ tailWord_1368478).sum := by decide
  have hdescent : baseEnd_1368478 < baseStart_1368478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368519 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 6]
def baseStart_1368519 : Nat := 118140960795 + 1368519 * 2 ^ 59
def prefixEnd_1368519 : Nat := 4983230072969 + 3 ^ 40 * 1368519 * 2
def baseEnd_1368519 : Nat := 156157340402319199293067

theorem tailTrace_1368519 : CollatzResearch.WordTrace tailWord_1368519 prefixEnd_1368519 156157340402319199293067 := by
  unfold tailWord_1368519
  simp only [CollatzResearch.WordTrace]
  refine ⟨49913988529096862282556611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33275992352731241521704407 49913988529096862282556611)
  ·
    refine ⟨74870982793645293423834917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49913988529096862282556611 74870982793645293423834917)
    ·
      refine ⟨14038309273808492516969047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74870982793645293423834917 14038309273808492516969047)
      ·
        refine ⟨21057463910712738775453571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14038309273808492516969047 21057463910712738775453571)
        ·
          refine ⟨31586195866069108163180357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21057463910712738775453571 31586195866069108163180357)
          ·
            refine ⟨5922411724887957780596317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31586195866069108163180357 5922411724887957780596317)
            ·
              refine ⟨2220904396832984167723619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5922411724887957780596317 2220904396832984167723619)
              ·
                refine ⟨3331356595249476251585429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220904396832984167723619 3331356595249476251585429)
                ·
                  refine ⟨156157340402319199293067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3331356595249476251585429 156157340402319199293067)
                  ·
                    rfl

theorem cell22_1368519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 6].length) (baseStart_1368519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368519 prefixEnd_1368519 := by exact prefixLift 1368519
  have htrace : WordTrace (prefixWord ++ tailWord_1368519) baseStart_1368519 baseEnd_1368519 := by
    simpa [prefixWord, tailWord_1368519, baseEnd_1368519] using wordTrace_append hprefix tailTrace_1368519
  have hstable : (prefixWord ++ tailWord_1368519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368519).length < 2 ^ (prefixWord ++ tailWord_1368519).sum := by decide
  have hdescent : baseEnd_1368519 < baseStart_1368519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368564 : List Nat := [2, 6, 14]
def baseStart_1368564 : Nat := 118140960795 + 1368564 * 2 ^ 59
def prefixEnd_1368564 : Nat := 4983230072969 + 3 ^ 40 * 1368564 * 2
def baseEnd_1368564 : Nat := 214214643633558518749

theorem tailTrace_1368564 : CollatzResearch.WordTrace tailWord_1368564 prefixEnd_1368564 214214643633558518749 := by
  unfold tailWord_1368564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24957814906966917483972373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33277086542622556645296497 24957814906966917483972373)
  ·
    refine ⟨1169897573764074257061205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24957814906966917483972373 1169897573764074257061205)
    ·
      refine ⟨214214643633558518749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 1169897573764074257061205 214214643633558518749)
      ·
        rfl

theorem cell22_1368564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 14].length) (baseStart_1368564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368564 prefixEnd_1368564 := by exact prefixLift 1368564
  have htrace : WordTrace (prefixWord ++ tailWord_1368564) baseStart_1368564 baseEnd_1368564 := by
    simpa [prefixWord, tailWord_1368564, baseEnd_1368564] using wordTrace_append hprefix tailTrace_1368564
  have hstable : (prefixWord ++ tailWord_1368564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368564).length < 2 ^ (prefixWord ++ tailWord_1368564).sum := by decide
  have hdescent : baseEnd_1368564 < baseStart_1368564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368566 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1368566 : Nat := 118140960795 + 1368566 * 2 ^ 59
def prefixEnd_1368566 : Nat := 4983230072969 + 3 ^ 40 * 1368566 * 2
def baseEnd_1368566 : Nat := 468488110267465141954057

theorem tailTrace_1368566 : CollatzResearch.WordTrace tailWord_1368566 prefixEnd_1368566 468488110267465141954057 := by
  unfold tailWord_1368566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119731422495411831844847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33277135173284392873011701 3119731422495411831844847)
  ·
    refine ⟨4679597133743117747767271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3119731422495411831844847 4679597133743117747767271)
    ·
      refine ⟨7019395700614676621650907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4679597133743117747767271 7019395700614676621650907)
      ·
        refine ⟨10529093550922014932476361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7019395700614676621650907 10529093550922014932476361)
        ·
          refine ⟨7896820163191511199357271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10529093550922014932476361 7896820163191511199357271)
          ·
            refine ⟨11845230244787266799035907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7896820163191511199357271 11845230244787266799035907)
            ·
              refine ⟨17767845367180900198553861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11845230244787266799035907 17767845367180900198553861)
              ·
                refine ⟨3331471006346418787228849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17767845367180900198553861 3331471006346418787228849)
                ·
                  refine ⟨2498603254759814090421637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331471006346418787228849 2498603254759814090421637)
                  ·
                    refine ⟨468488110267465141954057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498603254759814090421637 468488110267465141954057)
                    ·
                      rfl

theorem cell22_1368566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1368566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368566 prefixEnd_1368566 := by exact prefixLift 1368566
  have htrace : WordTrace (prefixWord ++ tailWord_1368566) baseStart_1368566 baseEnd_1368566 := by
    simpa [prefixWord, tailWord_1368566, baseEnd_1368566] using wordTrace_append hprefix tailTrace_1368566
  have hstable : (prefixWord ++ tailWord_1368566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368566).length < 2 ^ (prefixWord ++ tailWord_1368566).sum := by decide
  have hdescent : baseEnd_1368566 < baseStart_1368566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368609 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 7]
def baseStart_1368609 : Nat := 118140960795 + 1368609 * 2 ^ 59
def prefixEnd_1368609 : Nat := 4983230072969 + 3 ^ 40 * 1368609 * 2
def baseEnd_1368609 : Nat := 156167610015409121042975

theorem tailTrace_1368609 : CollatzResearch.WordTrace tailWord_1368609 prefixEnd_1368609 156167610015409121042975 := by
  unfold tailWord_1368609
  simp only [CollatzResearch.WordTrace]
  refine ⟨49917271098770807653332881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33278180732513871768888587 49917271098770807653332881)
  ·
    refine ⟨37437953324078105739999661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49917271098770807653332881 37437953324078105739999661)
    ·
      refine ⟨14039232496529289652499873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37437953324078105739999661 14039232496529289652499873)
      ·
        refine ⟨10529424372396967239374905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14039232496529289652499873 10529424372396967239374905)
        ·
          refine ⟨7897068279297725429531179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10529424372396967239374905 7897068279297725429531179)
          ·
            refine ⟨11845602418946588144296769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897068279297725429531179 11845602418946588144296769)
            ·
              refine ⟨8884201814209941108222577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11845602418946588144296769 8884201814209941108222577)
              ·
                refine ⟨6663151360657455831166933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8884201814209941108222577 6663151360657455831166933)
                ·
                  refine ⟨156167610015409121042975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6663151360657455831166933 156167610015409121042975)
                  ·
                    rfl

theorem cell22_1368609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_1368609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368609 prefixEnd_1368609 := by exact prefixLift 1368609
  have htrace : WordTrace (prefixWord ++ tailWord_1368609) baseStart_1368609 baseEnd_1368609 := by
    simpa [prefixWord, tailWord_1368609, baseEnd_1368609] using wordTrace_append hprefix tailTrace_1368609
  have hstable : (prefixWord ++ tailWord_1368609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368609).length < 2 ^ (prefixWord ++ tailWord_1368609).sum := by decide
  have hdescent : baseEnd_1368609 < baseStart_1368609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368613 : List Nat := [1, 3, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_1368613 : Nat := 118140960795 + 1368613 * 2 ^ 59
def prefixEnd_1368613 : Nat := 4983230072969 + 3 ^ 40 * 1368613 * 2
def baseEnd_1368613 : Nat := 468504199327972686028913

theorem tailTrace_1368613 : CollatzResearch.WordTrace tailWord_1368613 prefixEnd_1368613 468504199327972686028913 := by
  unfold tailWord_1368613
  simp only [CollatzResearch.WordTrace]
  refine ⟨49917416990756316336478493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33278277993837544224318995 49917416990756316336478493)
  ·
    refine ⟨18719031371533618626179435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49917416990756316336478493 18719031371533618626179435)
    ·
      refine ⟨28078547057300427939269153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18719031371533618626179435 28078547057300427939269153)
      ·
        refine ⟨21058910292975320954451865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28078547057300427939269153 21058910292975320954451865)
        ·
          refine ⟨15794182719731490715838899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21058910292975320954451865 15794182719731490715838899)
          ·
            refine ⟨23691274079597236073758349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15794182719731490715838899 23691274079597236073758349)
            ·
              refine ⟨8884227779848963527659381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23691274079597236073758349 8884227779848963527659381)
              ·
                refine ⟨832896354360840330718067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8884227779848963527659381 832896354360840330718067)
                ·
                  refine ⟨1249344531541260496077101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832896354360840330718067 1249344531541260496077101)
                  ·
                    refine ⟨468504199327972686028913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249344531541260496077101 468504199327972686028913)
                    ·
                      rfl

theorem cell22_1368613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_1368613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368613 prefixEnd_1368613 := by exact prefixLift 1368613
  have htrace : WordTrace (prefixWord ++ tailWord_1368613) baseStart_1368613 baseEnd_1368613 := by
    simpa [prefixWord, tailWord_1368613, baseEnd_1368613] using wordTrace_append hprefix tailTrace_1368613
  have hstable : (prefixWord ++ tailWord_1368613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368613).length < 2 ^ (prefixWord ++ tailWord_1368613).sum := by decide
  have hdescent : baseEnd_1368613 < baseStart_1368613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368624 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_1368624 : Nat := 118140960795 + 1368624 * 2 ^ 59
def prefixEnd_1368624 : Nat := 4983230072969 + 3 ^ 40 * 1368624 * 2
def baseEnd_1368624 : Nat := 468507964852772324003879

theorem tailTrace_1368624 : CollatzResearch.WordTrace tailWord_1368624 prefixEnd_1368624 468507964852772324003879 := by
  unfold tailWord_1368624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24958909096858232607564463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33278545462477643476752617 24958909096858232607564463)
  ·
    refine ⟨37438363645287348911346695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24958909096858232607564463 37438363645287348911346695)
    ·
      refine ⟨56157545467931023367020043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37438363645287348911346695 56157545467931023367020043)
      ·
        refine ⟨84236318201896535050530065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56157545467931023367020043 84236318201896535050530065)
        ·
          refine ⟨63177238651422401287897549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84236318201896535050530065 63177238651422401287897549)
          ·
            refine ⟨23691464494283400482961581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63177238651422401287897549 23691464494283400482961581)
            ·
              refine ⟨8884299185356275181110593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23691464494283400482961581 8884299185356275181110593)
              ·
                refine ⟨6663224389017206385832945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8884299185356275181110593 6663224389017206385832945)
                ·
                  refine ⟨4997418291762904789374709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6663224389017206385832945 4997418291762904789374709)
                  ·
                    refine ⟨468507964852772324003879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4997418291762904789374709 468507964852772324003879)
                    ·
                      rfl

theorem cell22_1368624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_1368624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368624 prefixEnd_1368624 := by exact prefixLift 1368624
  have htrace : WordTrace (prefixWord ++ tailWord_1368624) baseStart_1368624 baseEnd_1368624 := by
    simpa [prefixWord, tailWord_1368624, baseEnd_1368624] using wordTrace_append hprefix tailTrace_1368624
  have hstable : (prefixWord ++ tailWord_1368624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368624).length < 2 ^ (prefixWord ++ tailWord_1368624).sum := by decide
  have hdescent : baseEnd_1368624 < baseStart_1368624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368626 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_1368626 : Nat := 118140960795 + 1368626 * 2 ^ 59
def prefixEnd_1368626 : Nat := 4983230072969 + 3 ^ 40 * 1368626 * 2
def baseEnd_1368626 : Nat := 156169549831214995151291

theorem tailTrace_1368626 : CollatzResearch.WordTrace tailWord_1368626 prefixEnd_1368626 156169549831214995151291 := by
  unfold tailWord_1368626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479472784927304889175433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33278594093139479704467821 12479472784927304889175433)
  ·
    refine ⟨9359604588695478666881575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12479472784927304889175433 9359604588695478666881575)
    ·
      refine ⟨14039406883043218000322363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9359604588695478666881575 14039406883043218000322363)
      ·
        refine ⟨21059110324564827000483545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14039406883043218000322363 21059110324564827000483545)
        ·
          refine ⟨15794332743423620250362659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21059110324564827000483545 15794332743423620250362659)
          ·
            refine ⟨23691499115135430375543989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15794332743423620250362659 23691499115135430375543989)
            ·
              refine ⟨2221078042043946597707249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23691499115135430375543989 2221078042043946597707249)
              ·
                refine ⟨1665808531532959948280437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2221078042043946597707249 1665808531532959948280437)
                ·
                  refine ⟨156169549831214995151291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1665808531532959948280437 156169549831214995151291)
                  ·
                    rfl

theorem cell22_1368626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_1368626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368626 prefixEnd_1368626 := by exact prefixLift 1368626
  have htrace : WordTrace (prefixWord ++ tailWord_1368626) baseStart_1368626 baseEnd_1368626 := by
    simpa [prefixWord, tailWord_1368626, baseEnd_1368626] using wordTrace_append hprefix tailTrace_1368626
  have hstable : (prefixWord ++ tailWord_1368626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368626).length < 2 ^ (prefixWord ++ tailWord_1368626).sum := by decide
  have hdescent : baseEnd_1368626 < baseStart_1368626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368630 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1368630 : Nat := 118140960795 + 1368630 * 2 ^ 59
def prefixEnd_1368630 : Nat := 4983230072969 + 3 ^ 40 * 1368630 * 2
def baseEnd_1368630 : Nat := 468510018775390308353861

theorem tailTrace_1368630 : CollatzResearch.WordTrace tailWord_1368630 prefixEnd_1368630 468510018775390308353861 := by
  unfold tailWord_1368630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119877314480920514990459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33278691354463152159898229 3119877314480920514990459)
  ·
    refine ⟨4679815971721380772485689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3119877314480920514990459 4679815971721380772485689)
    ·
      refine ⟨3509861978791035579364267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4679815971721380772485689 3509861978791035579364267)
      ·
        refine ⟨5264792968186553369046401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509861978791035579364267 5264792968186553369046401)
        ·
          refine ⟨3948594726139915026784801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5264792968186553369046401 3948594726139915026784801)
          ·
            refine ⟨2961446044604936270088601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3948594726139915026784801 2961446044604936270088601)
            ·
              refine ⟨2221084533453702202566451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961446044604936270088601 2221084533453702202566451)
              ·
                refine ⟨3331626800180553303849677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221084533453702202566451 3331626800180553303849677)
                ·
                  refine ⟨1249360050067707488943629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3331626800180553303849677 1249360050067707488943629)
                  ·
                    refine ⟨468510018775390308353861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249360050067707488943629 468510018775390308353861)
                    ·
                      rfl

theorem cell22_1368630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1368630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368630 prefixEnd_1368630 := by exact prefixLift 1368630
  have htrace : WordTrace (prefixWord ++ tailWord_1368630) baseStart_1368630 baseEnd_1368630 := by
    simpa [prefixWord, tailWord_1368630, baseEnd_1368630] using wordTrace_append hprefix tailTrace_1368630
  have hstable : (prefixWord ++ tailWord_1368630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368630).length < 2 ^ (prefixWord ++ tailWord_1368630).sum := by decide
  have hdescent : baseEnd_1368630 < baseStart_1368630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368641 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1368641 : Nat := 118140960795 + 1368641 * 2 ^ 59
def prefixEnd_1368641 : Nat := 4983230072969 + 3 ^ 40 * 1368641 * 2
def baseEnd_1368641 : Nat := 468513784300189946328827

theorem tailTrace_1368641 : CollatzResearch.WordTrace tailWord_1368641 prefixEnd_1368641 468513784300189946328827 := by
  unfold tailWord_1368641
  simp only [CollatzResearch.WordTrace]
  refine ⟨49918438234654877118497777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33278958823103251412331851 49918438234654877118497777)
  ·
    refine ⟨37438828675991157838873333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49918438234654877118497777 37438828675991157838873333)
    ·
      refine ⟨3509890188374171047394375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37438828675991157838873333 3509890188374171047394375)
      ·
        refine ⟨5264835282561256571091563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509890188374171047394375 5264835282561256571091563)
        ·
          refine ⟨7897252923841884856637345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264835282561256571091563 7897252923841884856637345)
          ·
            refine ⟨5922939692881413642478009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7897252923841884856637345 5922939692881413642478009)
            ·
              refine ⟨4442204769661060231858507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922939692881413642478009 4442204769661060231858507)
              ·
                refine ⟨6663307154491590347787761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442204769661060231858507 6663307154491590347787761)
                ·
                  refine ⟨4997480365868692760840821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6663307154491590347787761 4997480365868692760840821)
                  ·
                    refine ⟨468513784300189946328827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4997480365868692760840821 468513784300189946328827)
                    ·
                      rfl

theorem cell22_1368641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1368641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368641 prefixEnd_1368641 := by exact prefixLift 1368641
  have htrace : WordTrace (prefixWord ++ tailWord_1368641) baseStart_1368641 baseEnd_1368641 := by
    simpa [prefixWord, tailWord_1368641, baseEnd_1368641] using wordTrace_append hprefix tailTrace_1368641
  have hstable : (prefixWord ++ tailWord_1368641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368641).length < 2 ^ (prefixWord ++ tailWord_1368641).sum := by decide
  have hdescent : baseEnd_1368641 < baseStart_1368641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368688 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 6]
def baseStart_1368688 : Nat := 118140960795 + 1368688 * 2 ^ 59
def prefixEnd_1368688 : Nat := 4983230072969 + 3 ^ 40 * 1368688 * 2
def baseEnd_1368688 : Nat := 156176624453565830134561

theorem tailTrace_1368688 : CollatzResearch.WordTrace tailWord_1368688 prefixEnd_1368688 156176624453565830134561 := by
  unfold tailWord_1368688
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960076232742302072729359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33280101643656402763639145 24960076232742302072729359)
  ·
    refine ⟨37440114349113453109094039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24960076232742302072729359 37440114349113453109094039)
    ·
      refine ⟨56160171523670179663641059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37440114349113453109094039 56160171523670179663641059)
      ·
        refine ⟨84240257285505269495461589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56160171523670179663641059 84240257285505269495461589)
        ·
          refine ⟨1974381030129029753799881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 84240257285505269495461589 1974381030129029753799881)
          ·
            refine ⟨1480785772596772315349911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974381030129029753799881 1480785772596772315349911)
            ·
              refine ⟨2221178658895158473024867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480785772596772315349911 2221178658895158473024867)
              ·
                refine ⟨3331767988342737709537301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221178658895158473024867 3331767988342737709537301)
                ·
                  refine ⟨156176624453565830134561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3331767988342737709537301 156176624453565830134561)
                  ·
                    rfl

theorem cell22_1368688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_1368688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368688 prefixEnd_1368688 := by exact prefixLift 1368688
  have htrace : WordTrace (prefixWord ++ tailWord_1368688) baseStart_1368688 baseEnd_1368688 := by
    simpa [prefixWord, tailWord_1368688, baseEnd_1368688] using wordTrace_append hprefix tailTrace_1368688
  have hstable : (prefixWord ++ tailWord_1368688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368688).length < 2 ^ (prefixWord ++ tailWord_1368688).sum := by decide
  have hdescent : baseEnd_1368688 < baseStart_1368688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368718 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1368718 : Nat := 118140960795 + 1368718 * 2 ^ 59
def prefixEnd_1368718 : Nat := 4983230072969 + 3 ^ 40 * 1368718 * 2
def baseEnd_1368718 : Nat := 468540142973787412153591

theorem tailTrace_1368718 : CollatzResearch.WordTrace tailWord_1368718 prefixEnd_1368718 468540142973787412153591 := by
  unfold tailWord_1368718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240155831921989908631351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33280831103583946179367205 6240155831921989908631351)
  ·
    refine ⟨9360233747882984862947027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6240155831921989908631351 9360233747882984862947027)
    ·
      refine ⟨14040350621824477294420541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9360233747882984862947027 14040350621824477294420541)
      ·
        refine ⟨5265131483184178985407703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14040350621824477294420541 5265131483184178985407703)
        ·
          refine ⟨7897697224776268478111555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5265131483184178985407703 7897697224776268478111555)
          ·
            refine ⟨11846545837164402717167333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897697224776268478111555 11846545837164402717167333)
            ·
              refine ⟨2221227344468325509468875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11846545837164402717167333 2221227344468325509468875)
              ·
                refine ⟨3331841016702488264203313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221227344468325509468875 3331841016702488264203313)
                ·
                  refine ⟨2498880762526866198152485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331841016702488264203313 2498880762526866198152485)
                  ·
                    refine ⟨468540142973787412153591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498880762526866198152485 468540142973787412153591)
                    ·
                      rfl

theorem cell22_1368718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1368718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368718 prefixEnd_1368718 := by exact prefixLift 1368718
  have htrace : WordTrace (prefixWord ++ tailWord_1368718) baseStart_1368718 baseEnd_1368718 := by
    simpa [prefixWord, tailWord_1368718, baseEnd_1368718] using wordTrace_append hprefix tailTrace_1368718
  have hstable : (prefixWord ++ tailWord_1368718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368718).length < 2 ^ (prefixWord ++ tailWord_1368718).sum := by decide
  have hdescent : baseEnd_1368718 < baseStart_1368718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368750 : List Nat := [4, 1, 4, 1, 1, 3, 1, 7]
def baseStart_1368750 : Nat := 118140960795 + 1368750 * 2 ^ 59
def prefixEnd_1368750 : Nat := 4983230072969 + 3 ^ 40 * 1368750 * 2
def baseEnd_1368750 : Nat := 52061233025305555039277

theorem tailTrace_1368750 : CollatzResearch.WordTrace tailWord_1368750 prefixEnd_1368750 52061233025305555039277 := by
  unfold tailWord_1368750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240301723907498591776963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33281609194173325822810469 6240301723907498591776963)
  ·
    refine ⟨9360452585861247887665445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6240301723907498591776963 9360452585861247887665445)
    ·
      refine ⟨1755084859848983978937271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9360452585861247887665445 1755084859848983978937271)
      ·
        refine ⟨2632627289773475968405907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755084859848983978937271 2632627289773475968405907)
        ·
          refine ⟨3948940934660213952608861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632627289773475968405907 3948940934660213952608861)
          ·
            refine ⟨1480852850497580232228323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3948940934660213952608861 1480852850497580232228323)
            ·
              refine ⟨2221279275746370348342485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480852850497580232228323 2221279275746370348342485)
              ·
                refine ⟨52061233025305555039277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2221279275746370348342485 52061233025305555039277)
                ·
                  rfl

theorem cell22_1368750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_1368750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368750 prefixEnd_1368750 := by exact prefixLift 1368750
  have htrace : WordTrace (prefixWord ++ tailWord_1368750) baseStart_1368750 baseEnd_1368750 := by
    simpa [prefixWord, tailWord_1368750, baseEnd_1368750] using wordTrace_append hprefix tailTrace_1368750
  have hstable : (prefixWord ++ tailWord_1368750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368750).length < 2 ^ (prefixWord ++ tailWord_1368750).sum := by decide
  have hdescent : baseEnd_1368750 < baseStart_1368750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368769 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1368769 : Nat := 118140960795 + 1368769 * 2 ^ 59
def prefixEnd_1368769 : Nat := 4983230072969 + 3 ^ 40 * 1368769 * 2
def baseEnd_1368769 : Nat := 468557601316040279128435

theorem tailTrace_1368769 : CollatzResearch.WordTrace tailWord_1368769 prefixEnd_1368769 468557601316040279128435 := by
  unfold tailWord_1368769
  simp only [CollatzResearch.WordTrace]
  refine ⟨49923106778191154979157361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33282071185460769986104907 49923106778191154979157361)
  ·
    refine ⟨37442330083643366234368021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49923106778191154979157361 37442330083643366234368021)
    ·
      refine ⟨1755109222670782792236001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37442330083643366234368021 1755109222670782792236001)
      ·
        refine ⟨1316331917003087094177001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1755109222670782792236001 1316331917003087094177001)
        ·
          refine ⟨987248937752315320632751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316331917003087094177001 987248937752315320632751)
          ·
            refine ⟨1480873406628472980949127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987248937752315320632751 1480873406628472980949127)
            ·
              refine ⟨2221310109942709471423691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480873406628472980949127 2221310109942709471423691)
              ·
                refine ⟨3331965164914064207135537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221310109942709471423691 3331965164914064207135537)
                ·
                  refine ⟨2498973873685548155351653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331965164914064207135537 2498973873685548155351653)
                  ·
                    refine ⟨468557601316040279128435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498973873685548155351653 468557601316040279128435)
                    ·
                      rfl

theorem cell22_1368769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1368769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368769 prefixEnd_1368769 := by exact prefixLift 1368769
  have htrace : WordTrace (prefixWord ++ tailWord_1368769) baseStart_1368769 baseEnd_1368769 := by
    simpa [prefixWord, tailWord_1368769, baseEnd_1368769] using wordTrace_append hprefix tailTrace_1368769
  have hstable : (prefixWord ++ tailWord_1368769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368769).length < 2 ^ (prefixWord ++ tailWord_1368769).sum := by decide
  have hdescent : baseEnd_1368769 < baseStart_1368769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368782 : List Nat := [4, 1, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_1368782 : Nat := 118140960795 + 1368782 * 2 ^ 59
def prefixEnd_1368782 : Nat := 4983230072969 + 3 ^ 40 * 1368782 * 2
def baseEnd_1368782 : Nat := 468562051481712578553395

theorem tailTrace_1368782 : CollatzResearch.WordTrace tailWord_1368782 prefixEnd_1368782 468562051481712578553395 := by
  unfold tailWord_1368782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240447615893007274922575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33282387284762705466253733 6240447615893007274922575)
  ·
    refine ⟨9360671423839510912383863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6240447615893007274922575 9360671423839510912383863)
    ·
      refine ⟨14041007135759266368575795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9360671423839510912383863 14041007135759266368575795)
      ·
        refine ⟨21061510703638899552863693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14041007135759266368575795 21061510703638899552863693)
        ·
          refine ⟨7898066513864587332323885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21061510703638899552863693 7898066513864587332323885)
          ·
            refine ⟨2961774942699220249621457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7898066513864587332323885 2961774942699220249621457)
            ·
              refine ⟨2221331207024415187216093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961774942699220249621457 2221331207024415187216093)
              ·
                refine ⟨832999202634155695206035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2221331207024415187216093 832999202634155695206035)
                ·
                  refine ⟨1249498803951233542809053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832999202634155695206035 1249498803951233542809053)
                  ·
                    refine ⟨468562051481712578553395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249498803951233542809053 468562051481712578553395)
                    ·
                      rfl

theorem cell22_1368782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_1368782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368782 prefixEnd_1368782 := by exact prefixLift 1368782
  have htrace : WordTrace (prefixWord ++ tailWord_1368782) baseStart_1368782 baseEnd_1368782 := by
    simpa [prefixWord, tailWord_1368782, baseEnd_1368782] using wordTrace_append hprefix tailTrace_1368782
  have hstable : (prefixWord ++ tailWord_1368782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368782).length < 2 ^ (prefixWord ++ tailWord_1368782).sum := by decide
  have hdescent : baseEnd_1368782 < baseStart_1368782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368840 : List Nat := [2, 1, 3, 2, 2, 2, 3, 3, 4]
def baseStart_1368840 : Nat := 118140960795 + 1368840 * 2 ^ 59
def prefixEnd_1368840 : Nat := 4983230072969 + 3 ^ 40 * 1368840 * 2
def baseEnd_1368840 : Nat := 156193968689006586867739

theorem tailTrace_1368840 : CollatzResearch.WordTrace tailWord_1368840 prefixEnd_1368840 156193968689006586867739 := by
  unfold tailWord_1368840
  simp only [CollatzResearch.WordTrace]
  refine ⟨24962848180466967052495987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33283797573955956069994649 24962848180466967052495987)
  ·
    refine ⟨37444272270700450578743981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24962848180466967052495987 37444272270700450578743981)
    ·
      refine ⟨14041602101512668967028993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37444272270700450578743981 14041602101512668967028993)
      ·
        refine ⟨10531201576134501725271745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14041602101512668967028993 10531201576134501725271745)
        ·
          refine ⟨7898401182100876293953809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10531201576134501725271745 7898401182100876293953809)
          ·
            refine ⟨5923800886575657220465357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7898401182100876293953809 5923800886575657220465357)
            ·
              refine ⟨2221425332465871457674509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5923800886575657220465357 2221425332465871457674509)
              ·
                refine ⟨833034499674701796627941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2221425332465871457674509 833034499674701796627941)
                ·
                  refine ⟨156193968689006586867739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833034499674701796627941 156193968689006586867739)
                  ·
                    rfl

theorem cell22_1368840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_1368840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368840 prefixEnd_1368840 := by exact prefixLift 1368840
  have htrace : WordTrace (prefixWord ++ tailWord_1368840) baseStart_1368840 baseEnd_1368840 := by
    simpa [prefixWord, tailWord_1368840, baseEnd_1368840] using wordTrace_append hprefix tailTrace_1368840
  have hstable : (prefixWord ++ tailWord_1368840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368840).length < 2 ^ (prefixWord ++ tailWord_1368840).sum := by decide
  have hdescent : baseEnd_1368840 < baseStart_1368840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368853 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1368853 : Nat := 118140960795 + 1368853 * 2 ^ 59
def prefixEnd_1368853 : Nat := 4983230072969 + 3 ^ 40 * 1368853 * 2
def baseEnd_1368853 : Nat := 468586356232692060028177

theorem tailTrace_1368853 : CollatzResearch.WordTrace tailWord_1368853 prefixEnd_1368853 468586356232692060028177 := by
  unfold tailWord_1368853
  simp only [CollatzResearch.WordTrace]
  refine ⟨49926170509886837325215213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33284113673257891550143475 49926170509886837325215213)
  ·
    refine ⟨18722313941207563996955705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49926170509886837325215213 18722313941207563996955705)
    ·
      refine ⟨14041735455905672997716779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18722313941207563996955705 14041735455905672997716779)
      ·
        refine ⟨21062603183858509496575169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14041735455905672997716779 21062603183858509496575169)
        ·
          refine ⟨15796952387893882122431377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21062603183858509496575169 15796952387893882122431377)
          ·
            refine ⟨11847714290920411591823533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15796952387893882122431377 11847714290920411591823533)
            ·
              refine ⟨4442892859095154346933825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11847714290920411591823533 4442892859095154346933825)
              ·
                refine ⟨3332169644321365760200369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4442892859095154346933825 3332169644321365760200369)
                ·
                  refine ⟨2499127233241024320150277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3332169644321365760200369 2499127233241024320150277)
                  ·
                    refine ⟨468586356232692060028177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2499127233241024320150277 468586356232692060028177)
                    ·
                      rfl

theorem cell22_1368853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1368853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368853 prefixEnd_1368853 := by exact prefixLift 1368853
  have htrace : WordTrace (prefixWord ++ tailWord_1368853) baseStart_1368853 baseEnd_1368853 := by
    simpa [prefixWord, tailWord_1368853, baseEnd_1368853] using wordTrace_append hprefix tailTrace_1368853
  have hstable : (prefixWord ++ tailWord_1368853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368853).length < 2 ^ (prefixWord ++ tailWord_1368853).sum := by decide
  have hdescent : baseEnd_1368853 < baseStart_1368853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368896 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 9]
def baseStart_1368896 : Nat := 118140960795 + 1368896 * 2 ^ 59
def prefixEnd_1368896 : Nat := 4983230072969 + 3 ^ 40 * 1368896 * 2
def baseEnd_1368896 : Nat := 156200358670484760401015

theorem tailTrace_1368896 : CollatzResearch.WordTrace tailWord_1368896 prefixEnd_1368896 156200358670484760401015 := by
  unfold tailWord_1368896
  simp only [CollatzResearch.WordTrace]
  refine ⟨24963869424365527834515271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33285159232487370446020361 24963869424365527834515271)
  ·
    refine ⟨37445804136548291751772907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24963869424365527834515271 37445804136548291751772907)
    ·
      refine ⟨56168706204822437627659361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37445804136548291751772907 56168706204822437627659361)
      ·
        refine ⟨42126529653616828220744521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56168706204822437627659361 42126529653616828220744521)
        ·
          refine ⟨31594897240212621165558391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42126529653616828220744521 31594897240212621165558391)
          ·
            refine ⟨47392345860318931748337587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31594897240212621165558391 47392345860318931748337587)
            ·
              refine ⟨71088518790478397622506381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47392345860318931748337587 71088518790478397622506381)
              ·
                refine ⟨26658194546429399108439893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71088518790478397622506381 26658194546429399108439893)
                ·
                  refine ⟨156200358670484760401015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26658194546429399108439893 156200358670484760401015)
                  ·
                    rfl

theorem cell22_1368896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_1368896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368896 prefixEnd_1368896 := by exact prefixLift 1368896
  have htrace : WordTrace (prefixWord ++ tailWord_1368896) baseStart_1368896 baseEnd_1368896 := by
    simpa [prefixWord, tailWord_1368896, baseEnd_1368896] using wordTrace_append hprefix tailTrace_1368896
  have hstable : (prefixWord ++ tailWord_1368896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368896).length < 2 ^ (prefixWord ++ tailWord_1368896).sum := by decide
  have hdescent : baseEnd_1368896 < baseStart_1368896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368902 : List Nat := [6, 1, 1, 2, 3, 9]
def baseStart_1368902 : Nat := 118140960795 + 1368902 * 2 ^ 59
def prefixEnd_1368902 : Nat := 4983230072969 + 3 ^ 40 * 1368902 * 2
def baseEnd_1368902 : Nat := 5785223826346571179667

theorem tailTrace_1368902 : CollatzResearch.WordTrace tailWord_1368902 prefixEnd_1368902 5785223826346571179667 := by
  unfold tailWord_1368902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560248677709666209179655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33285305124472879129165973 1560248677709666209179655)
  ·
    refine ⟨2340373016564499313769483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560248677709666209179655 2340373016564499313769483)
    ·
      refine ⟨3510559524846748970654225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340373016564499313769483 3510559524846748970654225)
      ·
        refine ⟨2632919643635061727990669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3510559524846748970654225 2632919643635061727990669)
        ·
          refine ⟨987344866363148147996501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2632919643635061727990669 987344866363148147996501)
          ·
            refine ⟨5785223826346571179667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 987344866363148147996501 5785223826346571179667)
            ·
              rfl

theorem cell22_1368902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 9].length) (baseStart_1368902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368902 prefixEnd_1368902 := by exact prefixLift 1368902
  have htrace : WordTrace (prefixWord ++ tailWord_1368902) baseStart_1368902 baseEnd_1368902 := by
    simpa [prefixWord, tailWord_1368902, baseEnd_1368902] using wordTrace_append hprefix tailTrace_1368902
  have hstable : (prefixWord ++ tailWord_1368902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368902).length < 2 ^ (prefixWord ++ tailWord_1368902).sum := by decide
  have hdescent : baseEnd_1368902 < baseStart_1368902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368911 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 5, 7]
def baseStart_1368911 : Nat := 118140960795 + 1368911 * 2 ^ 59
def prefixEnd_1368911 : Nat := 4983230072969 + 3 ^ 40 * 1368911 * 2
def baseEnd_1368911 : Nat := 468606210817999242077999

theorem tailTrace_1368911 : CollatzResearch.WordTrace tailWord_1368911 prefixEnd_1368911 468606210817999242077999 := by
  unfold tailWord_1368911
  simp only [CollatzResearch.WordTrace]
  refine ⟨49928285943676713230826587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33285523962451142153884391 49928285943676713230826587)
  ·
    refine ⟨74892428915515069846239881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49928285943676713230826587 74892428915515069846239881)
    ·
      refine ⟨56169321686636302384679911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74892428915515069846239881 56169321686636302384679911)
      ·
        refine ⟨84253982529954453577019867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56169321686636302384679911 84253982529954453577019867)
        ·
          refine ⟨126380973794931680365529801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84253982529954453577019867 126380973794931680365529801)
          ·
            refine ⟨94785730346198760274147351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126380973794931680365529801 94785730346198760274147351)
            ·
              refine ⟨142178595519298140411221027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94785730346198760274147351 142178595519298140411221027)
              ·
                refine ⟨213267893278947210616831541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142178595519298140411221027 213267893278947210616831541)
                ·
                  refine ⟨19993864994901300995327957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213267893278947210616831541 19993864994901300995327957)
                  ·
                    refine ⟨468606210817999242077999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19993864994901300995327957 468606210817999242077999)
                    ·
                      rfl

theorem cell22_1368911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_1368911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368911 prefixEnd_1368911 := by exact prefixLift 1368911
  have htrace : WordTrace (prefixWord ++ tailWord_1368911) baseStart_1368911 baseEnd_1368911 := by
    simpa [prefixWord, tailWord_1368911, baseEnd_1368911] using wordTrace_append hprefix tailTrace_1368911
  have hstable : (prefixWord ++ tailWord_1368911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368911).length < 2 ^ (prefixWord ++ tailWord_1368911).sum := by decide
  have hdescent : baseEnd_1368911 < baseStart_1368911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368917 : List Nat := [1, 3, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_1368917 : Nat := 118140960795 + 1368917 * 2 ^ 59
def prefixEnd_1368917 : Nat := 4983230072969 + 3 ^ 40 * 1368917 * 2
def baseEnd_1368917 : Nat := 468608264740617226427981

theorem tailTrace_1368917 : CollatzResearch.WordTrace tailWord_1368917 prefixEnd_1368917 468608264740617226427981 := by
  unfold tailWord_1368917
  simp only [CollatzResearch.WordTrace]
  refine ⟨49928504781654976255545005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33285669854436650837030003 49928504781654976255545005)
  ·
    refine ⟨18723189293120616095829377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49928504781654976255545005 18723189293120616095829377)
    ·
      refine ⟨14042391969840462071872033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18723189293120616095829377 14042391969840462071872033)
      ·
        refine ⟨10531793977380346553904025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14042391969840462071872033 10531793977380346553904025)
        ·
          refine ⟨7898845483035259915428019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10531793977380346553904025 7898845483035259915428019)
          ·
            refine ⟨11848268224552889873142029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7898845483035259915428019 11848268224552889873142029)
            ·
              refine ⟨4443100584207333702428261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11848268224552889873142029 4443100584207333702428261)
              ·
                refine ⟨833081359538875069205299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4443100584207333702428261 833081359538875069205299)
                ·
                  refine ⟨1249622039308312603807949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833081359538875069205299 1249622039308312603807949)
                  ·
                    refine ⟨468608264740617226427981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249622039308312603807949 468608264740617226427981)
                    ·
                      rfl

theorem cell22_1368917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_1368917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368917 prefixEnd_1368917 := by exact prefixLift 1368917
  have htrace : WordTrace (prefixWord ++ tailWord_1368917) baseStart_1368917 baseEnd_1368917 := by
    simpa [prefixWord, tailWord_1368917, baseEnd_1368917] using wordTrace_append hprefix tailTrace_1368917
  have hstable : (prefixWord ++ tailWord_1368917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368917).length < 2 ^ (prefixWord ++ tailWord_1368917).sum := by decide
  have hdescent : baseEnd_1368917 < baseStart_1368917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368928 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_1368928 : Nat := 118140960795 + 1368928 * 2 ^ 59
def prefixEnd_1368928 : Nat := 4983230072969 + 3 ^ 40 * 1368928 * 2
def baseEnd_1368928 : Nat := 468612030265416864402947

theorem tailTrace_1368928 : CollatzResearch.WordTrace tailWord_1368928 prefixEnd_1368928 468612030265416864402947 := by
  unfold tailWord_1368928
  simp only [CollatzResearch.WordTrace]
  refine ⟨24964452992307562567097719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33285937323076750089463625 24964452992307562567097719)
  ·
    refine ⟨37446679488461343850646579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24964452992307562567097719 37446679488461343850646579)
    ·
      refine ⟨56170019232692015775969869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37446679488461343850646579 56170019232692015775969869)
      ·
        refine ⟨21063757212259505915988701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56170019232692015775969869 21063757212259505915988701)
        ·
          refine ⟨7898908954597314718495763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21063757212259505915988701 7898908954597314718495763)
          ·
            refine ⟨11848363431895972077743645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7898908954597314718495763 11848363431895972077743645)
            ·
              refine ⟨4443136286960989529153867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11848363431895972077743645 4443136286960989529153867)
              ·
                refine ⟨6664704430441484293730801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4443136286960989529153867 6664704430441484293730801)
                ·
                  refine ⟨4998528322831113220298101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6664704430441484293730801 4998528322831113220298101)
                  ·
                    refine ⟨468612030265416864402947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4998528322831113220298101 468612030265416864402947)
                    ·
                      rfl

theorem cell22_1368928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_1368928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1368928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1368928 prefixEnd_1368928 := by exact prefixLift 1368928
  have htrace : WordTrace (prefixWord ++ tailWord_1368928) baseStart_1368928 baseEnd_1368928 := by
    simpa [prefixWord, tailWord_1368928, baseEnd_1368928] using wordTrace_append hprefix tailTrace_1368928
  have hstable : (prefixWord ++ tailWord_1368928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368928).length < 2 ^ (prefixWord ++ tailWord_1368928).sum := by decide
  have hdescent : baseEnd_1368928 < baseStart_1368928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369009 : List Nat := [1, 2, 2, 4, 3, 2, 1, 3, 4]
def baseStart_1369009 : Nat := 118140960795 + 1369009 * 2 ^ 59
def prefixEnd_1369009 : Nat := 4983230072969 + 3 ^ 40 * 1369009 * 2
def baseEnd_1369009 : Nat := 156213252740253217709233

theorem tailTrace_1369009 : CollatzResearch.WordTrace tailWord_1369009 prefixEnd_1369009 156213252740253217709233 := by
  unfold tailWord_1369009
  simp only [CollatzResearch.WordTrace]
  refine ⟨49931860297321675967894081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33287906864881117311929387 49931860297321675967894081)
  ·
    refine ⟨37448895222991256975920561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49931860297321675967894081 37448895222991256975920561)
    ·
      refine ⟨28086671417243442731940421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37448895222991256975920561 28086671417243442731940421)
      ·
        refine ⟨5266250890733145512238829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28086671417243442731940421 5266250890733145512238829)
        ·
          refine ⟨1974844084024929567089561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5266250890733145512238829 1974844084024929567089561)
          ·
            refine ⟨1481133063018697175317171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974844084024929567089561 1481133063018697175317171)
            ·
              refine ⟨2221699594528045762975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481133063018697175317171 2221699594528045762975757)
              ·
                refine ⟨833137347948017161115909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2221699594528045762975757 833137347948017161115909)
                ·
                  refine ⟨156213252740253217709233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833137347948017161115909 156213252740253217709233)
                  ·
                    rfl

theorem cell22_1369009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_1369009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369009 prefixEnd_1369009 := by exact prefixLift 1369009
  have htrace : WordTrace (prefixWord ++ tailWord_1369009) baseStart_1369009 baseEnd_1369009 := by
    simpa [prefixWord, tailWord_1369009, baseEnd_1369009] using wordTrace_append hprefix tailTrace_1369009
  have hstable : (prefixWord ++ tailWord_1369009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369009).length < 2 ^ (prefixWord ++ tailWord_1369009).sum := by decide
  have hdescent : baseEnd_1369009 < baseStart_1369009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369095 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1369095 : Nat := 118140960795 + 1369095 * 2 ^ 59
def prefixEnd_1369095 : Nat := 4983230072969 + 3 ^ 40 * 1369095 * 2
def baseEnd_1369095 : Nat := 468669197778284095477435

theorem tailTrace_1369095 : CollatzResearch.WordTrace tailWord_1369095 prefixEnd_1369095 468669197778284095477435 := by
  unfold tailWord_1369095
  simp only [CollatzResearch.WordTrace]
  refine ⟨49934996975010112655524739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33289997983340075103683159 49934996975010112655524739)
  ·
    refine ⟨74902495462515168983287109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49934996975010112655524739 74902495462515168983287109)
    ·
      refine ⟨14044217899221594184366333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74902495462515168983287109 14044217899221594184366333)
      ·
        refine ⟨5266581712208097819137375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14044217899221594184366333 5266581712208097819137375)
        ·
          refine ⟨7899872568312146728706063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5266581712208097819137375 7899872568312146728706063)
          ·
            refine ⟨11849808852468220093059095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7899872568312146728706063 11849808852468220093059095)
            ·
              refine ⟨17774713278702330139588643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11849808852468220093059095 17774713278702330139588643)
              ·
                refine ⟨26662069918053495209382965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17774713278702330139588643 26662069918053495209382965)
                ·
                  refine ⟨2499569054817515175879653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26662069918053495209382965 2499569054817515175879653)
                  ·
                    refine ⟨468669197778284095477435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2499569054817515175879653 468669197778284095477435)
                    ·
                      rfl

theorem cell22_1369095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1369095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369095 prefixEnd_1369095 := by exact prefixLift 1369095
  have htrace : WordTrace (prefixWord ++ tailWord_1369095) baseStart_1369095 baseEnd_1369095 := by
    simpa [prefixWord, tailWord_1369095, baseEnd_1369095] using wordTrace_append hprefix tailTrace_1369095
  have hstable : (prefixWord ++ tailWord_1369095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369095).length < 2 ^ (prefixWord ++ tailWord_1369095).sum := by decide
  have hdescent : baseEnd_1369095 < baseStart_1369095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369125 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_1369125 : Nat := 118140960795 + 1369125 * 2 ^ 59
def prefixEnd_1369125 : Nat := 4983230072969 + 3 ^ 40 * 1369125 * 2
def baseEnd_1369125 : Nat := 468679467391374017227343

theorem tailTrace_1369125 : CollatzResearch.WordTrace tailWord_1369125 prefixEnd_1369125 468679467391374017227343 := by
  unfold tailWord_1369125
  simp only [CollatzResearch.WordTrace]
  refine ⟨49936091164901427779116829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33290727443267618519411219 49936091164901427779116829)
  ·
    refine ⟨18726034186838035417168811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49936091164901427779116829 18726034186838035417168811)
    ·
      refine ⟨28089051280257053125753217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18726034186838035417168811 28089051280257053125753217)
      ·
        refine ⟨21066788460192789844314913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28089051280257053125753217 21066788460192789844314913)
        ·
          refine ⟨15800091345144592383236185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21066788460192789844314913 15800091345144592383236185)
          ·
            refine ⟨11850068508858444287427139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15800091345144592383236185 11850068508858444287427139)
            ·
              refine ⟨17775102763287666431140709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11850068508858444287427139 17775102763287666431140709)
              ·
                refine ⟨3332831768116437455838883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17775102763287666431140709 3332831768116437455838883)
                ·
                  refine ⟨4999247652174656183758325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332831768116437455838883 4999247652174656183758325)
                  ·
                    refine ⟨468679467391374017227343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4999247652174656183758325 468679467391374017227343)
                    ·
                      rfl

theorem cell22_1369125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_1369125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369125 prefixEnd_1369125 := by exact prefixLift 1369125
  have htrace : WordTrace (prefixWord ++ tailWord_1369125) baseStart_1369125 baseEnd_1369125 := by
    simpa [prefixWord, tailWord_1369125, baseEnd_1369125] using wordTrace_append hprefix tailTrace_1369125
  have hstable : (prefixWord ++ tailWord_1369125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369125).length < 2 ^ (prefixWord ++ tailWord_1369125).sum := by decide
  have hdescent : baseEnd_1369125 < baseStart_1369125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369172 : List Nat := [2, 4, 1, 1, 1, 1, 6, 6]
def baseStart_1369172 : Nat := 118140960795 + 1369172 * 2 ^ 59
def prefixEnd_1369172 : Nat := 4983230072969 + 3 ^ 40 * 1369172 * 2
def baseEnd_1369172 : Nat := 52077284050209062366911

theorem tailTrace_1369172 : CollatzResearch.WordTrace tailWord_1369172 prefixEnd_1369172 52077284050209062366911 := by
  unfold tailWord_1369172
  simp only [CollatzResearch.WordTrace]
  refine ⟨24968902697865577403038885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33291870263820769870718513 24968902697865577403038885)
  ·
    refine ⟨4681669255849795763069791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24968902697865577403038885 4681669255849795763069791)
    ·
      refine ⟨7022503883774693644604687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4681669255849795763069791 7022503883774693644604687)
      ·
        refine ⟨10533755825662040466907031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7022503883774693644604687 10533755825662040466907031)
        ·
          refine ⟨15800633738493060700360547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10533755825662040466907031 15800633738493060700360547)
          ·
            refine ⟨23700950607739591050540821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15800633738493060700360547 23700950607739591050540821)
            ·
              refine ⟨1110982059737793330494101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23700950607739591050540821 1110982059737793330494101)
              ·
                refine ⟨52077284050209062366911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1110982059737793330494101 52077284050209062366911)
                ·
                  rfl

theorem cell22_1369172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 6].length) (baseStart_1369172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369172 prefixEnd_1369172 := by exact prefixLift 1369172
  have htrace : WordTrace (prefixWord ++ tailWord_1369172) baseStart_1369172 baseEnd_1369172 := by
    simpa [prefixWord, tailWord_1369172, baseEnd_1369172] using wordTrace_append hprefix tailTrace_1369172
  have hstable : (prefixWord ++ tailWord_1369172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369172).length < 2 ^ (prefixWord ++ tailWord_1369172).sum := by decide
  have hdescent : baseEnd_1369172 < baseStart_1369172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369200 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 7]
def baseStart_1369200 : Nat := 118140960795 + 1369200 * 2 ^ 59
def prefixEnd_1369200 : Nat := 4983230072969 + 3 ^ 40 * 1369200 * 2
def baseEnd_1369200 : Nat := 156235047141366273867371

theorem tailTrace_1369200 : CollatzResearch.WordTrace tailWord_1369200 prefixEnd_1369200 156235047141366273867371 := by
  unfold tailWord_1369200
  simp only [CollatzResearch.WordTrace]
  refine ⟨24969413319814857794048527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33292551093086477058731369 24969413319814857794048527)
  ·
    refine ⟨37454119979722286691072791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24969413319814857794048527 37454119979722286691072791)
    ·
      refine ⟨56181179969583430036609187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37454119979722286691072791 56181179969583430036609187)
      ·
        refine ⟨84271769954375145054913781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56181179969583430036609187 84271769954375145054913781)
        ·
          refine ⟨7900478433222669848898167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84271769954375145054913781 7900478433222669848898167)
          ·
            refine ⟨11850717649834004773347251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900478433222669848898167 11850717649834004773347251)
            ·
              refine ⟨17776076474751007160020877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11850717649834004773347251 17776076474751007160020877)
              ·
                refine ⟨6666028678031627685007829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17776076474751007160020877 6666028678031627685007829)
                ·
                  refine ⟨156235047141366273867371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6666028678031627685007829 156235047141366273867371)
                  ·
                    rfl

theorem cell22_1369200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_1369200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369200 prefixEnd_1369200 := by exact prefixLift 1369200
  have htrace : WordTrace (prefixWord ++ tailWord_1369200) baseStart_1369200 baseEnd_1369200 := by
    simpa [prefixWord, tailWord_1369200, baseEnd_1369200] using wordTrace_append hprefix tailTrace_1369200
  have hstable : (prefixWord ++ tailWord_1369200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369200).length < 2 ^ (prefixWord ++ tailWord_1369200).sum := by decide
  have hdescent : baseEnd_1369200 < baseStart_1369200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369255 : List Nat := [1, 1, 6, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1369255 : Nat := 118140960795 + 1369255 * 2 ^ 59
def prefixEnd_1369255 : Nat := 4983230072969 + 3 ^ 40 * 1369255 * 2
def baseEnd_1369255 : Nat := 468723969048097011476945

theorem tailTrace_1369255 : CollatzResearch.WordTrace tailWord_1369255 prefixEnd_1369255 468723969048097011476945 := by
  unfold tailWord_1369255
  simp only [CollatzResearch.WordTrace]
  refine ⟨49940832654430459981349219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33293888436286973320899479 49940832654430459981349219)
  ·
    refine ⟨74911248981645689972023829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49940832654430459981349219 74911248981645689972023829)
    ·
      refine ⟨3511464796014641717438617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74911248981645689972023829 3511464796014641717438617)
      ·
        refine ⟨2633598597010981288078963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3511464796014641717438617 2633598597010981288078963)
        ·
          refine ⟨3950397895516471932118445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633598597010981288078963 3950397895516471932118445)
          ·
            refine ⟨1481399210818676974544417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3950397895516471932118445 1481399210818676974544417)
            ·
              refine ⟨1111049408114007730908313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481399210818676974544417 1111049408114007730908313)
              ·
                refine ⟨833287056085505798181235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111049408114007730908313 833287056085505798181235)
                ·
                  refine ⟨1249930584128258697271853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833287056085505798181235 1249930584128258697271853)
                  ·
                    refine ⟨468723969048097011476945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249930584128258697271853 468723969048097011476945)
                    ·
                      rfl

theorem cell22_1369255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1369255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369255 prefixEnd_1369255 := by exact prefixLift 1369255
  have htrace : WordTrace (prefixWord ++ tailWord_1369255) baseStart_1369255 baseEnd_1369255 := by
    simpa [prefixWord, tailWord_1369255, baseEnd_1369255] using wordTrace_append hprefix tailTrace_1369255
  have hstable : (prefixWord ++ tailWord_1369255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369255).length < 2 ^ (prefixWord ++ tailWord_1369255).sum := by decide
  have hdescent : baseEnd_1369255 < baseStart_1369255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369277 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_1369277 : Nat := 118140960795 + 1369277 * 2 ^ 59
def prefixEnd_1369277 : Nat := 4983230072969 + 3 ^ 40 * 1369277 * 2
def baseEnd_1369277 : Nat := 468731500097696287426877

theorem tailTrace_1369277 : CollatzResearch.WordTrace tailWord_1369277 prefixEnd_1369277 468731500097696287426877 := by
  unfold tailWord_1369277
  simp only [CollatzResearch.WordTrace]
  refine ⟨49941635060350757738650085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33294423373567171825766723 49941635060350757738650085)
  ·
    refine ⟨9364056573815767075996891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49941635060350757738650085 9364056573815767075996891)
    ·
      refine ⟨14046084860723650613995337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9364056573815767075996891 14046084860723650613995337)
      ·
        refine ⟨10534563645542737960496503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14046084860723650613995337 10534563645542737960496503)
        ·
          refine ⟨15801845468314106940744755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10534563645542737960496503 15801845468314106940744755)
          ·
            refine ⟨23702768202471160411117133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15801845468314106940744755 23702768202471160411117133)
            ·
              refine ⟨8888538075926685154168925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23702768202471160411117133 8888538075926685154168925)
              ·
                refine ⟨3333201778472506932813347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8888538075926685154168925 3333201778472506932813347)
                ·
                  refine ⟨4999802667708760399220021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333201778472506932813347 4999802667708760399220021)
                  ·
                    refine ⟨468731500097696287426877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4999802667708760399220021 468731500097696287426877)
                    ·
                      rfl

theorem cell22_1369277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_1369277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369277 prefixEnd_1369277 := by exact prefixLift 1369277
  have htrace : WordTrace (prefixWord ++ tailWord_1369277) baseStart_1369277 baseEnd_1369277 := by
    simpa [prefixWord, tailWord_1369277, baseEnd_1369277] using wordTrace_append hprefix tailTrace_1369277
  have hstable : (prefixWord ++ tailWord_1369277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369277).length < 2 ^ (prefixWord ++ tailWord_1369277).sum := by decide
  have hdescent : baseEnd_1369277 < baseStart_1369277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369373 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1369373 : Nat := 118140960795 + 1369373 * 2 ^ 59
def prefixEnd_1369373 : Nat := 4983230072969 + 3 ^ 40 * 1369373 * 2
def baseEnd_1369373 : Nat := 468764362859584037026583

theorem tailTrace_1369373 : CollatzResearch.WordTrace tailWord_1369373 prefixEnd_1369373 468764362859584037026583 := by
  unfold tailWord_1369373
  simp only [CollatzResearch.WordTrace]
  refine ⟨49945136468002966134144773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33296757645335310756096515 49945136468002966134144773)
  ·
    refine ⟨9364713087750556150152145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49945136468002966134144773 9364713087750556150152145)
    ·
      refine ⟨7023534815812917112614109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9364713087750556150152145 7023534815812917112614109)
      ·
        refine ⟨2633825555929843917230291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7023534815812917112614109 2633825555929843917230291)
        ·
          refine ⟨3950738333894765875845437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633825555929843917230291 3950738333894765875845437)
          ·
            refine ⟨1481526875210537203442039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3950738333894765875845437 1481526875210537203442039)
            ·
              refine ⟨2222290312815805805163059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481526875210537203442039 2222290312815805805163059)
              ·
                refine ⟨3333435469223708707744589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222290312815805805163059 3333435469223708707744589)
                ·
                  refine ⟨1250038300958890765404221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3333435469223708707744589 1250038300958890765404221)
                  ·
                    refine ⟨468764362859584037026583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250038300958890765404221 468764362859584037026583)
                    ·
                      rfl

theorem cell22_1369373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1369373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369373 prefixEnd_1369373 := by exact prefixLift 1369373
  have htrace : WordTrace (prefixWord ++ tailWord_1369373) baseStart_1369373 baseEnd_1369373 := by
    simpa [prefixWord, tailWord_1369373, baseEnd_1369373] using wordTrace_append hprefix tailTrace_1369373
  have hstable : (prefixWord ++ tailWord_1369373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369373).length < 2 ^ (prefixWord ++ tailWord_1369373).sum := by decide
  have hdescent : baseEnd_1369373 < baseStart_1369373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369386 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_1369386 : Nat := 118140960795 + 1369386 * 2 ^ 59
def prefixEnd_1369386 : Nat := 4983230072969 + 3 ^ 40 * 1369386 * 2
def baseEnd_1369386 : Nat := 156256271008418778817181

theorem tailTrace_1369386 : CollatzResearch.WordTrace tailWord_1369386 prefixEnd_1369386 156256271008418778817181 := by
  unfold tailWord_1369386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12486402654238967338592003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33297073744637246236245341 12486402654238967338592003)
  ·
    refine ⟨18729603981358451007888005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12486402654238967338592003 18729603981358451007888005)
    ·
      refine ⟨3511800746504709563979001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18729603981358451007888005 3511800746504709563979001)
      ·
        refine ⟨2633850559878532172984251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3511800746504709563979001 2633850559878532172984251)
        ·
          refine ⟨3950775839817798259476377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633850559878532172984251 3950775839817798259476377)
          ·
            refine ⟨2963081879863348694607283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3950775839817798259476377 2963081879863348694607283)
            ·
              refine ⟨4444622819795023041910925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963081879863348694607283 4444622819795023041910925)
              ·
                refine ⟨1666733557423133640716597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4444622819795023041910925 1666733557423133640716597)
                ·
                  refine ⟨156256271008418778817181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1666733557423133640716597 156256271008418778817181)
                  ·
                    rfl

theorem cell22_1369386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_1369386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369386 prefixEnd_1369386 := by exact prefixLift 1369386
  have htrace : WordTrace (prefixWord ++ tailWord_1369386) baseStart_1369386 baseEnd_1369386 := by
    simpa [prefixWord, tailWord_1369386, baseEnd_1369386] using wordTrace_append hprefix tailTrace_1369386
  have hstable : (prefixWord ++ tailWord_1369386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369386).length < 2 ^ (prefixWord ++ tailWord_1369386).sum := by decide
  have hdescent : baseEnd_1369386 < baseStart_1369386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369431 : List Nat := [1, 1, 3, 2, 3, 3, 1, 4, 4]
def baseStart_1369431 : Nat := 118140960795 + 1369431 * 2 ^ 59
def prefixEnd_1369431 : Nat := 4983230072969 + 3 ^ 40 * 1369431 * 2
def baseEnd_1369431 : Nat := 156261405814963739692135

theorem tailTrace_1369431 : CollatzResearch.WordTrace tailWord_1369431 prefixEnd_1369431 156261405814963739692135 := by
  unfold tailWord_1369431
  simp only [CollatzResearch.WordTrace]
  refine ⟨49947251901792842039756147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33298167934528561359837431 49947251901792842039756147)
  ·
    refine ⟨74920877852689263059634221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49947251901792842039756147 74920877852689263059634221)
    ·
      refine ⟨28095329194758473647362833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74920877852689263059634221 28095329194758473647362833)
      ·
        refine ⟨21071496896068855235522125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28095329194758473647362833 21071496896068855235522125)
        ·
          refine ⟨7901811336025820713320797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21071496896068855235522125 7901811336025820713320797)
          ·
            refine ⟨2963179251009682767495299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7901811336025820713320797 2963179251009682767495299)
            ·
              refine ⟨4444768876514524151242949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963179251009682767495299 4444768876514524151242949)
              ·
                refine ⟨833394164346473278358053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4444768876514524151242949 833394164346473278358053)
                ·
                  refine ⟨156261405814963739692135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833394164346473278358053 156261405814963739692135)
                  ·
                    rfl

theorem cell22_1369431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 4].length) (baseStart_1369431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369431 prefixEnd_1369431 := by exact prefixLift 1369431
  have htrace : WordTrace (prefixWord ++ tailWord_1369431) baseStart_1369431 baseEnd_1369431 := by
    simpa [prefixWord, tailWord_1369431, baseEnd_1369431] using wordTrace_append hprefix tailTrace_1369431
  have hstable : (prefixWord ++ tailWord_1369431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369431).length < 2 ^ (prefixWord ++ tailWord_1369431).sum := by decide
  have hdescent : baseEnd_1369431 < baseStart_1369431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369461 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1369461 : Nat := 118140960795 + 1369461 * 2 ^ 59
def prefixEnd_1369461 : Nat := 4983230072969 + 3 ^ 40 * 1369461 * 2
def baseEnd_1369461 : Nat := 468794487057981140826313

theorem tailTrace_1369461 : CollatzResearch.WordTrace tailWord_1369461 prefixEnd_1369461 468794487057981140826313 := by
  unfold tailWord_1369461
  simp only [CollatzResearch.WordTrace]
  refine ⟨49948346091684157163348237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33298897394456104775565491 49948346091684157163348237)
  ·
    refine ⟨18730629784381558936255589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49948346091684157163348237 18730629784381558936255589)
    ·
      refine ⟨3511993084571542300547923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18730629784381558936255589 3511993084571542300547923)
      ·
        refine ⟨5267989626857313450821885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511993084571542300547923 5267989626857313450821885)
        ·
          refine ⟨1975496110071492544058207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5267989626857313450821885 1975496110071492544058207)
          ·
            refine ⟨2963244165107238816087311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975496110071492544058207 2963244165107238816087311)
            ·
              refine ⟨4444866247660858224130967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963244165107238816087311 4444866247660858224130967)
              ·
                refine ⟨6667299371491287336196451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444866247660858224130967 6667299371491287336196451)
                ·
                  refine ⟨10000949057236931004294677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6667299371491287336196451 10000949057236931004294677)
                  ·
                    refine ⟨468794487057981140826313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10000949057236931004294677 468794487057981140826313)
                    ·
                      rfl

theorem cell22_1369461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1369461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369461 prefixEnd_1369461 := by exact prefixLift 1369461
  have htrace : WordTrace (prefixWord ++ tailWord_1369461) baseStart_1369461 baseEnd_1369461 := by
    simpa [prefixWord, tailWord_1369461, baseEnd_1369461] using wordTrace_append hprefix tailTrace_1369461
  have hstable : (prefixWord ++ tailWord_1369461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369461).length < 2 ^ (prefixWord ++ tailWord_1369461).sum := by decide
  have hdescent : baseEnd_1369461 < baseStart_1369461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369525 : List Nat := [1, 3, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1369525 : Nat := 118140960795 + 1369525 * 2 ^ 59
def prefixEnd_1369525 : Nat := 4983230072969 + 3 ^ 40 * 1369525 * 2
def baseEnd_1369525 : Nat := 468816395565906307226117

theorem tailTrace_1369525 : CollatzResearch.WordTrace tailWord_1369525 prefixEnd_1369525 468816395565906307226117 := by
  unfold tailWord_1369525
  simp only [CollatzResearch.WordTrace]
  refine ⟨49950680363452296093678029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33300453575634864062452019 49950680363452296093678029)
  ·
    refine ⟨18731505136294611035129261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49950680363452296093678029 18731505136294611035129261)
    ·
      refine ⟨7024314426110479138173473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18731505136294611035129261 7024314426110479138173473)
      ·
        refine ⟨5268235819582859353630105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7024314426110479138173473 5268235819582859353630105)
        ·
          refine ⟨3951176864687144515222579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5268235819582859353630105 3951176864687144515222579)
          ·
            refine ⟨5926765297030716772833869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3951176864687144515222579 5926765297030716772833869)
            ·
              refine ⟨2222536986386518789812701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5926765297030716772833869 2222536986386518789812701)
              ·
                refine ⟨833451369894944546179763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222536986386518789812701 833451369894944546179763)
                ·
                  refine ⟨1250177054842416819269645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833451369894944546179763 1250177054842416819269645)
                  ·
                    refine ⟨468816395565906307226117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250177054842416819269645 468816395565906307226117)
                    ·
                      rfl

theorem cell22_1369525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1369525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369525 prefixEnd_1369525 := by exact prefixLift 1369525
  have htrace : WordTrace (prefixWord ++ tailWord_1369525) baseStart_1369525 baseEnd_1369525 := by
    simpa [prefixWord, tailWord_1369525, baseEnd_1369525] using wordTrace_append hprefix tailTrace_1369525
  have hstable : (prefixWord ++ tailWord_1369525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369525).length < 2 ^ (prefixWord ++ tailWord_1369525).sum := by decide
  have hdescent : baseEnd_1369525 < baseStart_1369525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369596 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1369596 : Nat := 118140960795 + 1369596 * 2 ^ 59
def prefixEnd_1369596 : Nat := 4983230072969 + 3 ^ 40 * 1369596 * 2
def baseEnd_1369596 : Nat := 468840700316885788700899

theorem tailTrace_1369596 : CollatzResearch.WordTrace tailWord_1369596 prefixEnd_1369596 468840700316885788700899 := by
  unfold tailWord_1369596
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976634973097537609756321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33302179964130050146341761 24976634973097537609756321)
  ·
    refine ⟨18732476229823153207317241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24976634973097537609756321 18732476229823153207317241)
    ·
      refine ⟨14049357172367364905487931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18732476229823153207317241 14049357172367364905487931)
      ·
        refine ⟨21074035758551047358231897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14049357172367364905487931 21074035758551047358231897)
        ·
          refine ⟨15805526818913285518673923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21074035758551047358231897 15805526818913285518673923)
          ·
            refine ⟨23708290228369928278010885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15805526818913285518673923 23708290228369928278010885)
            ·
              refine ⟨4445304417819361552127041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23708290228369928278010885 4445304417819361552127041)
              ·
                refine ⟨3333978313364521164095281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4445304417819361552127041 3333978313364521164095281)
                ·
                  refine ⟨2500483735023390873071461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3333978313364521164095281 2500483735023390873071461)
                  ·
                    refine ⟨468840700316885788700899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2500483735023390873071461 468840700316885788700899)
                    ·
                      rfl

theorem cell22_1369596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1369596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369596 prefixEnd_1369596 := by exact prefixLift 1369596
  have htrace : WordTrace (prefixWord ++ tailWord_1369596) baseStart_1369596 baseEnd_1369596 := by
    simpa [prefixWord, tailWord_1369596, baseEnd_1369596] using wordTrace_append hprefix tailTrace_1369596
  have hstable : (prefixWord ++ tailWord_1369596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369596).length < 2 ^ (prefixWord ++ tailWord_1369596).sum := by decide
  have hdescent : baseEnd_1369596 < baseStart_1369596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369656 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 7]
def baseStart_1369656 : Nat := 118140960795 + 1369656 * 2 ^ 59
def prefixEnd_1369656 : Nat := 4983230072969 + 3 ^ 40 * 1369656 * 2
def baseEnd_1369656 : Nat := 156287079847688544066905

theorem tailTrace_1369656 : CollatzResearch.WordTrace tailWord_1369656 prefixEnd_1369656 156287079847688544066905 := by
  unfold tailWord_1369656
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977729162988852733348411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33303638883985136977797881 24977729162988852733348411)
  ·
    refine ⟨37466593744483279100022617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24977729162988852733348411 37466593744483279100022617)
    ·
      refine ⟨28099945308362459325016963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37466593744483279100022617 28099945308362459325016963)
      ·
        refine ⟨42149917962543688987525445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28099945308362459325016963 42149917962543688987525445)
        ·
          refine ⟨7903109617976941685161021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42149917962543688987525445 7903109617976941685161021)
          ·
            refine ⟨2963666106741353131935383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7903109617976941685161021 2963666106741353131935383)
            ·
              refine ⟨4445499160112029697903075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963666106741353131935383 4445499160112029697903075)
              ·
                refine ⟨6668248740168044546854613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445499160112029697903075 6668248740168044546854613)
                ·
                  refine ⟨156287079847688544066905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6668248740168044546854613 156287079847688544066905)
                  ·
                    rfl

theorem cell22_1369656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_1369656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369656 prefixEnd_1369656 := by exact prefixLift 1369656
  have htrace : WordTrace (prefixWord ++ tailWord_1369656) baseStart_1369656 baseEnd_1369656 := by
    simpa [prefixWord, tailWord_1369656, baseEnd_1369656] using wordTrace_append hprefix tailTrace_1369656
  have hstable : (prefixWord ++ tailWord_1369656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369656).length < 2 ^ (prefixWord ++ tailWord_1369656).sum := by decide
  have hdescent : baseEnd_1369656 < baseStart_1369656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369660 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_1369660 : Nat := 118140960795 + 1369660 * 2 ^ 59
def prefixEnd_1369660 : Nat := 4983230072969 + 3 ^ 40 * 1369660 * 2
def baseEnd_1369660 : Nat := 468862608824810955100703

theorem tailTrace_1369660 : CollatzResearch.WordTrace tailWord_1369660 prefixEnd_1369660 468862608824810955100703 := by
  unfold tailWord_1369660
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977802108981607074921217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33303736145308809433228289 24977802108981607074921217)
  ·
    refine ⟨18733351581736205306190913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24977802108981607074921217 18733351581736205306190913)
    ·
      refine ⟨14050013686302153979643185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18733351581736205306190913 14050013686302153979643185)
      ·
        refine ⟨10537510264726615484732389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14050013686302153979643185 10537510264726615484732389)
        ·
          refine ⟨1975783174636240403387323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10537510264726615484732389 1975783174636240403387323)
          ·
            refine ⟨2963674761954360605080985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975783174636240403387323 2963674761954360605080985)
            ·
              refine ⟨2222756071465770453810739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963674761954360605080985 2222756071465770453810739)
              ·
                refine ⟨3334134107198655680716109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222756071465770453810739 3334134107198655680716109)
                ·
                  refine ⟨1250300290199495880268541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3334134107198655680716109 1250300290199495880268541)
                  ·
                    refine ⟨468862608824810955100703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250300290199495880268541 468862608824810955100703)
                    ·
                      rfl

theorem cell22_1369660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_1369660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369660 prefixEnd_1369660 := by exact prefixLift 1369660
  have htrace : WordTrace (prefixWord ++ tailWord_1369660) baseStart_1369660 baseEnd_1369660 := by
    simpa [prefixWord, tailWord_1369660, baseEnd_1369660] using wordTrace_append hprefix tailTrace_1369660
  have hstable : (prefixWord ++ tailWord_1369660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369660).length < 2 ^ (prefixWord ++ tailWord_1369660).sum := by decide
  have hdescent : baseEnd_1369660 < baseStart_1369660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369703 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1369703 : Nat := 118140960795 + 1369703 * 2 ^ 59
def prefixEnd_1369703 : Nat := 4983230072969 + 3 ^ 40 * 1369703 * 2
def baseEnd_1369703 : Nat := 468877328603573176275571

theorem tailTrace_1369703 : CollatzResearch.WordTrace tailWord_1369703 prefixEnd_1369703 468877328603573176275571 := by
  unfold tailWord_1369703
  simp only [CollatzResearch.WordTrace]
  refine ⟨49957172556807432493657763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33304781704538288329105175 49957172556807432493657763)
  ·
    refine ⟨74935758835211148740486645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49957172556807432493657763 74935758835211148740486645)
    ·
      refine ⟨7025227390801045194420623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74935758835211148740486645 7025227390801045194420623)
      ·
        refine ⟨10537841086201567791630935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7025227390801045194420623 10537841086201567791630935)
        ·
          refine ⟨15806761629302351687446403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10537841086201567791630935 15806761629302351687446403)
          ·
            refine ⟨23710142443953527531169605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15806761629302351687446403 23710142443953527531169605)
            ·
              refine ⟨4445651708241286412094301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23710142443953527531169605 4445651708241286412094301)
              ·
                refine ⟨1667119390590482404535363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4445651708241286412094301 1667119390590482404535363)
                ·
                  refine ⟨2500679085885723606803045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667119390590482404535363 2500679085885723606803045)
                  ·
                    refine ⟨468877328603573176275571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2500679085885723606803045 468877328603573176275571)
                    ·
                      rfl

theorem cell22_1369703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1369703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369703 prefixEnd_1369703 := by exact prefixLift 1369703
  have htrace : WordTrace (prefixWord ++ tailWord_1369703) baseStart_1369703 baseEnd_1369703 := by
    simpa [prefixWord, tailWord_1369703, baseEnd_1369703] using wordTrace_append hprefix tailTrace_1369703
  have hstable : (prefixWord ++ tailWord_1369703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369703).length < 2 ^ (prefixWord ++ tailWord_1369703).sum := by decide
  have hdescent : baseEnd_1369703 < baseStart_1369703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369731 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 6, 4]
def baseStart_1369731 : Nat := 118140960795 + 1369731 * 2 ^ 59
def prefixEnd_1369731 : Nat := 4983230072969 + 3 ^ 40 * 1369731 * 2
def baseEnd_1369731 : Nat := 468886913575790436575485

theorem tailTrace_1369731 : CollatzResearch.WordTrace tailWord_1369731 prefixEnd_1369731 468886913575790436575485 := by
  unfold tailWord_1369731
  simp only [CollatzResearch.WordTrace]
  refine ⟨49958193800705993275677047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33305462533803995517118031 49958193800705993275677047)
  ·
    refine ⟨74937290701058989913515571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49958193800705993275677047 74937290701058989913515571)
    ·
      refine ⟨112405936051588484870273357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74937290701058989913515571 112405936051588484870273357)
      ·
        refine ⟨42152226019345681826352509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112405936051588484870273357 42152226019345681826352509)
        ·
          refine ⟨15807084757254630684882191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42152226019345681826352509 15807084757254630684882191)
          ·
            refine ⟨23710627135881946027323287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15807084757254630684882191 23710627135881946027323287)
            ·
              refine ⟨35565940703822919040984931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23710627135881946027323287 35565940703822919040984931)
              ·
                refine ⟨53348911055734378561477397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35565940703822919040984931 53348911055734378561477397)
                ·
                  refine ⟨2500730205737548995069253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53348911055734378561477397 2500730205737548995069253)
                  ·
                    refine ⟨468886913575790436575485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2500730205737548995069253 468886913575790436575485)
                    ·
                      rfl

theorem cell22_1369731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_1369731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369731 prefixEnd_1369731 := by exact prefixLift 1369731
  have htrace : WordTrace (prefixWord ++ tailWord_1369731) baseStart_1369731 baseEnd_1369731 := by
    simpa [prefixWord, tailWord_1369731, baseEnd_1369731] using wordTrace_append hprefix tailTrace_1369731
  have hstable : (prefixWord ++ tailWord_1369731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369731).length < 2 ^ (prefixWord ++ tailWord_1369731).sum := by decide
  have hdescent : baseEnd_1369731 < baseStart_1369731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369776 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_1369776 : Nat := 118140960795 + 1369776 * 2 ^ 59
def prefixEnd_1369776 : Nat := 4983230072969 + 3 ^ 40 * 1369776 * 2
def baseEnd_1369776 : Nat := 468902317995425319200347

theorem tailTrace_1369776 : CollatzResearch.WordTrace tailWord_1369776 prefixEnd_1369776 468902317995425319200347 := by
  unfold tailWord_1369776
  simp only [CollatzResearch.WordTrace]
  refine ⟨24979917542771482980532591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33306556723695310640710121 24979917542771482980532591)
  ·
    refine ⟨37469876314157224470798887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24979917542771482980532591 37469876314157224470798887)
    ·
      refine ⟨56204814471235836706198331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37469876314157224470798887 56204814471235836706198331)
      ·
        refine ⟨84307221706853755059297497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56204814471235836706198331 84307221706853755059297497)
        ·
          refine ⟨63230416280140316294473123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84307221706853755059297497 63230416280140316294473123)
          ·
            refine ⟨94845624420210474441709685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63230416280140316294473123 94845624420210474441709685)
            ·
              refine ⟨8891777289394731978910283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94845624420210474441709685 8891777289394731978910283)
              ·
                refine ⟨13337665934092097968365425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8891777289394731978910283 13337665934092097968365425)
                ·
                  refine ⟨10003249450569073476274069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13337665934092097968365425 10003249450569073476274069)
                  ·
                    refine ⟨468902317995425319200347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10003249450569073476274069 468902317995425319200347)
                    ·
                      rfl

theorem cell22_1369776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_1369776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369776 prefixEnd_1369776 := by exact prefixLift 1369776
  have htrace : WordTrace (prefixWord ++ tailWord_1369776) baseStart_1369776 baseEnd_1369776 := by
    simpa [prefixWord, tailWord_1369776, baseEnd_1369776] using wordTrace_append hprefix tailTrace_1369776
  have hstable : (prefixWord ++ tailWord_1369776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369776).length < 2 ^ (prefixWord ++ tailWord_1369776).sum := by decide
  have hdescent : baseEnd_1369776 < baseStart_1369776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369868 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_1369868 : Nat := 118140960795 + 1369868 * 2 ^ 59
def prefixEnd_1369868 : Nat := 4983230072969 + 3 ^ 40 * 1369868 * 2
def baseEnd_1369868 : Nat := 468933811475567745900065

theorem tailTrace_1369868 : CollatzResearch.WordTrace tailWord_1369868 prefixEnd_1369868 468933811475567745900065 := by
  unfold tailWord_1369868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24981595300604832836707129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33308793734139777115609505 24981595300604832836707129)
  ·
    refine ⟨18736196475453624627530347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24981595300604832836707129 18736196475453624627530347)
    ·
      refine ⟨28104294713180436941295521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18736196475453624627530347 28104294713180436941295521)
      ·
        refine ⟨21078221034885327705971641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28104294713180436941295521 21078221034885327705971641)
        ·
          refine ⟨15808665776163995779478731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21078221034885327705971641 15808665776163995779478731)
          ·
            refine ⟨23712998664245993669218097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15808665776163995779478731 23712998664245993669218097)
            ·
              refine ⟨17784748998184495251913573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23712998664245993669218097 17784748998184495251913573)
              ·
                refine ⟨3334640437159592859733795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17784748998184495251913573 3334640437159592859733795)
                ·
                  refine ⟨5001960655739389289600693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334640437159592859733795 5001960655739389289600693)
                  ·
                    refine ⟨468933811475567745900065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5001960655739389289600693 468933811475567745900065)
                    ·
                      rfl

theorem cell22_1369868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_1369868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369868 prefixEnd_1369868 := by exact prefixLift 1369868
  have htrace : WordTrace (prefixWord ++ tailWord_1369868) baseStart_1369868 baseEnd_1369868 := by
    simpa [prefixWord, tailWord_1369868, baseEnd_1369868] using wordTrace_append hprefix tailTrace_1369868
  have hstable : (prefixWord ++ tailWord_1369868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369868).length < 2 ^ (prefixWord ++ tailWord_1369868).sum := by decide
  have hdescent : baseEnd_1369868 < baseStart_1369868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369883 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 2, 4]
def baseStart_1369883 : Nat := 118140960795 + 1369883 * 2 ^ 59
def prefixEnd_1369883 : Nat := 4983230072969 + 3 ^ 40 * 1369883 * 2
def baseEnd_1369883 : Nat := 468938946282112706775019

theorem tailTrace_1369883 : CollatzResearch.WordTrace tailWord_1369883 prefixEnd_1369883 468938946282112706775019 := by
  unfold tailWord_1369883
  simp only [CollatzResearch.WordTrace]
  refine ⟨49963737696155323235210303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33309158464103548823473535 49963737696155323235210303)
  ·
    refine ⟨74945606544232984852815455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49963737696155323235210303 74945606544232984852815455)
    ·
      refine ⟨112418409816349477279223183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74945606544232984852815455 112418409816349477279223183)
      ·
        refine ⟨168627614724524215918834775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112418409816349477279223183 168627614724524215918834775)
        ·
          refine ⟨252941422086786323878252163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168627614724524215918834775 252941422086786323878252163)
          ·
            refine ⟨379412133130179485817378245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252941422086786323878252163 379412133130179485817378245)
            ·
              refine ⟨71139774961908653590758421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 379412133130179485817378245 71139774961908653590758421)
              ·
                refine ⟨3334676951339468137066801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71139774961908653590758421 3334676951339468137066801)
                ·
                  refine ⟨2501007713504601102800101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3334676951339468137066801 2501007713504601102800101)
                  ·
                    refine ⟨468938946282112706775019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2501007713504601102800101 468938946282112706775019)
                    ·
                      rfl

theorem cell22_1369883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_1369883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369883 prefixEnd_1369883 := by exact prefixLift 1369883
  have htrace : WordTrace (prefixWord ++ tailWord_1369883) baseStart_1369883 baseEnd_1369883 := by
    simpa [prefixWord, tailWord_1369883, baseEnd_1369883] using wordTrace_append hprefix tailTrace_1369883
  have hstable : (prefixWord ++ tailWord_1369883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369883).length < 2 ^ (prefixWord ++ tailWord_1369883).sum := by decide
  have hdescent : baseEnd_1369883 < baseStart_1369883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369887 : List Nat := [1, 1, 2, 4, 2, 1, 5, 2, 4]
def baseStart_1369887 : Nat := 118140960795 + 1369887 * 2 ^ 59
def prefixEnd_1369887 : Nat := 4983230072969 + 3 ^ 40 * 1369887 * 2
def baseEnd_1369887 : Nat := 156313438521286009891669

theorem tailTrace_1369887 : CollatzResearch.WordTrace tailWord_1369887 prefixEnd_1369887 156313438521286009891669 := by
  unfold tailWord_1369887
  simp only [CollatzResearch.WordTrace]
  refine ⟨49963883588140831918355915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33309255725427221278903943 49963883588140831918355915)
  ·
    refine ⟨74945825382211247877533873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49963883588140831918355915 74945825382211247877533873)
    ·
      refine ⟨56209369036658435908150405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74945825382211247877533873 56209369036658435908150405)
      ·
        refine ⟨10539256694373456732778201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56209369036658435908150405 10539256694373456732778201)
        ·
          refine ⟨7904442520780092549583651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10539256694373456732778201 7904442520780092549583651)
          ·
            refine ⟨11856663781170138824375477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904442520780092549583651 11856663781170138824375477)
            ·
              refine ⟨1111562229484700514785201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11856663781170138824375477 1111562229484700514785201)
              ·
                refine ⟨833671672113525386088901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111562229484700514785201 833671672113525386088901)
                ·
                  refine ⟨156313438521286009891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833671672113525386088901 156313438521286009891669)
                  ·
                    rfl

theorem cell22_1369887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 4].length) (baseStart_1369887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369887 prefixEnd_1369887 := by exact prefixLift 1369887
  have htrace : WordTrace (prefixWord ++ tailWord_1369887) baseStart_1369887 baseEnd_1369887 := by
    simpa [prefixWord, tailWord_1369887, baseEnd_1369887] using wordTrace_append hprefix tailTrace_1369887
  have hstable : (prefixWord ++ tailWord_1369887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369887).length < 2 ^ (prefixWord ++ tailWord_1369887).sum := by decide
  have hdescent : baseEnd_1369887 < baseStart_1369887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369917 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1369917 : Nat := 118140960795 + 1369917 * 2 ^ 59
def prefixEnd_1369917 : Nat := 4983230072969 + 3 ^ 40 * 1369917 * 2
def baseEnd_1369917 : Nat := 468950585176947951424915

theorem tailTrace_1369917 : CollatzResearch.WordTrace tailWord_1369917 prefixEnd_1369917 468950585176947951424915 := by
  unfold tailWord_1369917
  simp only [CollatzResearch.WordTrace]
  refine ⟨49964977778032147041948005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33309985185354764694632003 49964977778032147041948005)
  ·
    refine ⟨9368433333381027570365251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49964977778032147041948005 9368433333381027570365251)
    ·
      refine ⟨14052650000071541355547877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9368433333381027570365251 14052650000071541355547877)
      ·
        refine ⟨2634871875013414004165227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14052650000071541355547877 2634871875013414004165227)
        ·
          refine ⟨3952307812520121006247841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634871875013414004165227 3952307812520121006247841)
          ·
            refine ⟨2964230859390090754685881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3952307812520121006247841 2964230859390090754685881)
            ·
              refine ⟨2223173144542568066014411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2964230859390090754685881 2223173144542568066014411)
              ·
                refine ⟨3334759716813852099021617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223173144542568066014411 3334759716813852099021617)
                ·
                  refine ⟨2501069787610389074266213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3334759716813852099021617 2501069787610389074266213)
                  ·
                    refine ⟨468950585176947951424915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2501069787610389074266213 468950585176947951424915)
                    ·
                      rfl

theorem cell22_1369917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1369917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369917 prefixEnd_1369917 := by exact prefixLift 1369917
  have htrace : WordTrace (prefixWord ++ tailWord_1369917) baseStart_1369917 baseEnd_1369917 := by
    simpa [prefixWord, tailWord_1369917, baseEnd_1369917] using wordTrace_append hprefix tailTrace_1369917
  have hstable : (prefixWord ++ tailWord_1369917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369917).length < 2 ^ (prefixWord ++ tailWord_1369917).sum := by decide
  have hdescent : baseEnd_1369917 < baseStart_1369917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369960 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 5]
def baseStart_1369960 : Nat := 118140960795 + 1369960 * 2 ^ 59
def prefixEnd_1369960 : Nat := 4983230072969 + 3 ^ 40 * 1369960 * 2
def baseEnd_1369960 : Nat := 156321768318570057533261

theorem tailTrace_1369960 : CollatzResearch.WordTrace tailWord_1369960 prefixEnd_1369960 156321768318570057533261 := by
  unfold tailWord_1369960
  simp only [CollatzResearch.WordTrace]
  refine ⟨24983273058438182692881667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33311030744584243590508889 24983273058438182692881667)
  ·
    refine ⟨37474909587657274039322501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24983273058438182692881667 37474909587657274039322501)
    ·
      refine ⟨7026545547685738882372969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37474909587657274039322501 7026545547685738882372969)
      ·
        refine ⟨5269909160764304161779727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7026545547685738882372969 5269909160764304161779727)
        ·
          refine ⟨7904863741146456242669591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5269909160764304161779727 7904863741146456242669591)
          ·
            refine ⟨11857295611719684364004387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904863741146456242669591 11857295611719684364004387)
            ·
              refine ⟨17785943417579526546006581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11857295611719684364004387 17785943417579526546006581)
              ·
                refine ⟨1667432195398080613688117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17785943417579526546006581 1667432195398080613688117)
                ·
                  refine ⟨156321768318570057533261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1667432195398080613688117 156321768318570057533261)
                  ·
                    rfl

theorem cell22_1369960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_1369960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369960 prefixEnd_1369960 := by exact prefixLift 1369960
  have htrace : WordTrace (prefixWord ++ tailWord_1369960) baseStart_1369960 baseEnd_1369960 := by
    simpa [prefixWord, tailWord_1369960, baseEnd_1369960] using wordTrace_append hprefix tailTrace_1369960
  have hstable : (prefixWord ++ tailWord_1369960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369960).length < 2 ^ (prefixWord ++ tailWord_1369960).sum := by decide
  have hdescent : baseEnd_1369960 < baseStart_1369960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369994 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_1369994 : Nat := 118140960795 + 1369994 * 2 ^ 59
def prefixEnd_1369994 : Nat := 4983230072969 + 3 ^ 40 * 1369994 * 2
def baseEnd_1369994 : Nat := 156325647950181805749893

theorem tailTrace_1369994 : CollatzResearch.WordTrace tailWord_1369994 prefixEnd_1369994 156325647950181805749893 := by
  unfold tailWord_1369994
  simp only [CollatzResearch.WordTrace]
  refine ⟨12491946549688297298125259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33311857465835459461667357 12491946549688297298125259)
  ·
    refine ⟨18737919824532445947187889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12491946549688297298125259 18737919824532445947187889)
    ·
      refine ⟨14053439868399334460390917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18737919824532445947187889 14053439868399334460390917)
      ·
        refine ⟨2635019975324875211323297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14053439868399334460390917 2635019975324875211323297)
        ·
          refine ⟨1976264981493656408492473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2635019975324875211323297 1976264981493656408492473)
          ·
            refine ⟨1482198736120242306369355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976264981493656408492473 1482198736120242306369355)
            ·
              refine ⟨2223298104180363459554033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482198736120242306369355 2223298104180363459554033)
              ·
                refine ⟨1667473578135272594665525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223298104180363459554033 1667473578135272594665525)
                ·
                  refine ⟨156325647950181805749893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1667473578135272594665525 156325647950181805749893)
                  ·
                    rfl

theorem cell22_1369994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_1369994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1369994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1369994 prefixEnd_1369994 := by exact prefixLift 1369994
  have htrace : WordTrace (prefixWord ++ tailWord_1369994) baseStart_1369994 baseEnd_1369994 := by
    simpa [prefixWord, tailWord_1369994, baseEnd_1369994] using wordTrace_append hprefix tailTrace_1369994
  have hstable : (prefixWord ++ tailWord_1369994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369994).length < 2 ^ (prefixWord ++ tailWord_1369994).sum := by decide
  have hdescent : baseEnd_1369994 < baseStart_1369994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370005 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 6]
def baseStart_1370005 : Nat := 118140960795 + 1370005 * 2 ^ 59
def prefixEnd_1370005 : Nat := 4983230072969 + 3 ^ 40 * 1370005 * 2
def baseEnd_1370005 : Nat := 156326903125115018408215

theorem tailTrace_1370005 : CollatzResearch.WordTrace tailWord_1370005 prefixEnd_1370005 156326903125115018408215 := by
  unfold tailWord_1370005
  simp only [CollatzResearch.WordTrace]
  refine ⟨49968187401713338071151469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33312124934475558714100979 49968187401713338071151469)
  ·
    refine ⟨18738070275642501776681801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49968187401713338071151469 18738070275642501776681801)
    ·
      refine ⟨14053552706731876332511351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18738070275642501776681801 14053552706731876332511351)
      ·
        refine ⟨21080329060097814498767027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14053552706731876332511351 21080329060097814498767027)
        ·
          refine ⟨31620493590146721748150541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21080329060097814498767027 31620493590146721748150541)
          ·
            refine ⟨11857685096305020655556453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31620493590146721748150541 11857685096305020655556453)
            ·
              refine ⟨2223315955557191372916835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11857685096305020655556453 2223315955557191372916835)
              ·
                refine ⟨3334973933335787059375253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223315955557191372916835 3334973933335787059375253)
                ·
                  refine ⟨156326903125115018408215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3334973933335787059375253 156326903125115018408215)
                  ·
                    rfl

theorem cell22_1370005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_1370005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370005 prefixEnd_1370005 := by exact prefixLift 1370005
  have htrace : WordTrace (prefixWord ++ tailWord_1370005) baseStart_1370005 baseEnd_1370005 := by
    simpa [prefixWord, tailWord_1370005, baseEnd_1370005] using wordTrace_append hprefix tailTrace_1370005
  have hstable : (prefixWord ++ tailWord_1370005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370005).length < 2 ^ (prefixWord ++ tailWord_1370005).sum := by decide
  have hdescent : baseEnd_1370005 < baseStart_1370005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370035 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 2, 4]
def baseStart_1370035 : Nat := 118140960795 + 1370035 * 2 ^ 59
def prefixEnd_1370035 : Nat := 4983230072969 + 3 ^ 40 * 1370035 * 2
def baseEnd_1370035 : Nat := 468990978988434976974553

theorem tailTrace_1370035 : CollatzResearch.WordTrace tailWord_1370035 prefixEnd_1370035 468990978988434976974553 := by
  unfold tailWord_1370035
  simp only [CollatzResearch.WordTrace]
  refine ⟨49969281591604653194743559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33312854394403102129829039 49969281591604653194743559)
  ·
    refine ⟨74953922387406979792115339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49969281591604653194743559 74953922387406979792115339)
    ·
      refine ⟨112430883581110469688173009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74953922387406979792115339 112430883581110469688173009)
      ·
        refine ⟨84323162685832852266129757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112430883581110469688173009 84323162685832852266129757)
        ·
          refine ⟨31621186007187319599798659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84323162685832852266129757 31621186007187319599798659)
          ·
            refine ⟨47431779010780979399697989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31621186007187319599798659 47431779010780979399697989)
            ·
              refine ⟨8893458564521433637443373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47431779010780979399697989 8893458564521433637443373)
              ·
                refine ⟨3335046961695537614041265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8893458564521433637443373 3335046961695537614041265)
                ·
                  refine ⟨2501285221271653210530949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3335046961695537614041265 2501285221271653210530949)
                  ·
                    refine ⟨468990978988434976974553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2501285221271653210530949 468990978988434976974553)
                    ·
                      rfl

theorem cell22_1370035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_1370035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370035 prefixEnd_1370035 := by exact prefixLift 1370035
  have htrace : WordTrace (prefixWord ++ tailWord_1370035) baseStart_1370035 baseEnd_1370035 := by
    simpa [prefixWord, tailWord_1370035, baseEnd_1370035] using wordTrace_append hprefix tailTrace_1370035
  have hstable : (prefixWord ++ tailWord_1370035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370035).length < 2 ^ (prefixWord ++ tailWord_1370035).sum := by decide
  have hdescent : baseEnd_1370035 < baseStart_1370035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370037 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1370037 : Nat := 118140960795 + 1370037 * 2 ^ 59
def prefixEnd_1370037 : Nat := 4983230072969 + 3 ^ 40 * 1370037 * 2
def baseEnd_1370037 : Nat := 468991663629307638424547

theorem tailTrace_1370037 : CollatzResearch.WordTrace tailWord_1370037 prefixEnd_1370037 468991663629307638424547 := by
  unfold tailWord_1370037
  simp only [CollatzResearch.WordTrace]
  refine ⟨49969354537597407536316365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33312903025064938357544243 49969354537597407536316365)
  ·
    refine ⟨18738507951599027826118637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49969354537597407536316365 18738507951599027826118637)
    ·
      refine ⟨7026940481849635434794489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18738507951599027826118637 7026940481849635434794489)
      ·
        refine ⟨5270205361387226576095867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7026940481849635434794489 5270205361387226576095867)
        ·
          refine ⟨7905308042080839864143801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270205361387226576095867 7905308042080839864143801)
          ·
            refine ⟨5928981031560629898107851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7905308042080839864143801 5928981031560629898107851)
            ·
              refine ⟨8893471547340944847161777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928981031560629898107851 8893471547340944847161777)
              ·
                refine ⟨6670103660505708635371333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8893471547340944847161777 6670103660505708635371333)
                ·
                  refine ⟨1250644436344820369132125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6670103660505708635371333 1250644436344820369132125)
                  ·
                    refine ⟨468991663629307638424547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250644436344820369132125 468991663629307638424547)
                    ·
                      rfl

theorem cell22_1370037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1370037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370037 prefixEnd_1370037 := by exact prefixLift 1370037
  have htrace : WordTrace (prefixWord ++ tailWord_1370037) baseStart_1370037 baseEnd_1370037 := by
    simpa [prefixWord, tailWord_1370037, baseEnd_1370037] using wordTrace_append hprefix tailTrace_1370037
  have hstable : (prefixWord ++ tailWord_1370037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370037).length < 2 ^ (prefixWord ++ tailWord_1370037).sum := by decide
  have hdescent : baseEnd_1370037 < baseStart_1370037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370155 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 3, 5]
def baseStart_1370155 : Nat := 118140960795 + 1370155 * 2 ^ 59
def prefixEnd_1370155 : Nat := 4983230072969 + 3 ^ 40 * 1370155 * 2
def baseEnd_1370155 : Nat := 469032057440794663974185

theorem tailTrace_1370155 : CollatzResearch.WordTrace tailWord_1370155 prefixEnd_1370155 469032057440794663974185 := by
  unfold tailWord_1370155
  simp only [CollatzResearch.WordTrace]
  refine ⟨49973658351169913689111919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33315772234113275792741279 49973658351169913689111919)
  ·
    refine ⟨74960487526754870533667879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49973658351169913689111919 74960487526754870533667879)
    ·
      refine ⟨112440731290132305800501819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74960487526754870533667879 112440731290132305800501819)
      ·
        refine ⟨168661096935198458700752729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112440731290132305800501819 168661096935198458700752729)
        ·
          refine ⟨126495822701398844025564547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168661096935198458700752729 126495822701398844025564547)
          ·
            refine ⟨189743734052098266038346821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126495822701398844025564547 189743734052098266038346821)
            ·
              refine ⟨35576950134768424882190029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189743734052098266038346821 35576950134768424882190029)
              ·
                refine ⟨13341356300538159330821261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35576950134768424882190029 13341356300538159330821261)
                ·
                  refine ⟨5003008612701809749057973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13341356300538159330821261 5003008612701809749057973)
                  ·
                    refine ⟨469032057440794663974185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5003008612701809749057973 469032057440794663974185)
                    ·
                      rfl

theorem cell22_1370155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_1370155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370155 prefixEnd_1370155 := by exact prefixLift 1370155
  have htrace : WordTrace (prefixWord ++ tailWord_1370155) baseStart_1370155 baseEnd_1370155 := by
    simpa [prefixWord, tailWord_1370155, baseEnd_1370155] using wordTrace_append hprefix tailTrace_1370155
  have hstable : (prefixWord ++ tailWord_1370155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370155).length < 2 ^ (prefixWord ++ tailWord_1370155).sum := by decide
  have hdescent : baseEnd_1370155 < baseStart_1370155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370185 : List Nat := [1, 2, 1, 1, 2, 2, 4, 9]
def baseStart_1370185 : Nat := 118140960795 + 1370185 * 2 ^ 59
def prefixEnd_1370185 : Nat := 4983230072969 + 3 ^ 40 * 1370185 * 2
def baseEnd_1370185 : Nat := 52115814117098287302677

theorem tailTrace_1370185 : CollatzResearch.WordTrace tailWord_1370185 prefixEnd_1370185 52115814117098287302677 := by
  unfold tailWord_1370185
  simp only [CollatzResearch.WordTrace]
  refine ⟨49974752541061228812704009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33316501694040819208469339 49974752541061228812704009)
  ·
    refine ⟨37481064405795921609528007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49974752541061228812704009 37481064405795921609528007)
    ·
      refine ⟨56221596608693882414292011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37481064405795921609528007 56221596608693882414292011)
      ·
        refine ⟨84332394913040823621438017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56221596608693882414292011 84332394913040823621438017)
        ·
          refine ⟨63249296184780617716078513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84332394913040823621438017 63249296184780617716078513)
          ·
            refine ⟨47436972138585463287058885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63249296184780617716078513 47436972138585463287058885)
            ·
              refine ⟨8894432275984774366323541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47436972138585463287058885 8894432275984774366323541)
              ·
                refine ⟨52115814117098287302677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8894432275984774366323541 52115814117098287302677)
                ·
                  rfl

theorem cell22_1370185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 9].length) (baseStart_1370185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370185 prefixEnd_1370185 := by exact prefixLift 1370185
  have htrace : WordTrace (prefixWord ++ tailWord_1370185) baseStart_1370185 baseEnd_1370185 := by
    simpa [prefixWord, tailWord_1370185, baseEnd_1370185] using wordTrace_append hprefix tailTrace_1370185
  have hstable : (prefixWord ++ tailWord_1370185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370185).length < 2 ^ (prefixWord ++ tailWord_1370185).sum := by decide
  have hdescent : baseEnd_1370185 < baseStart_1370185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370285 : List Nat := [1, 5, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1370285 : Nat := 118140960795 + 1370285 * 2 ^ 59
def prefixEnd_1370285 : Nat := 4983230072969 + 3 ^ 40 * 1370285 * 2
def baseEnd_1370285 : Nat := 469076559097517658223787

theorem tailTrace_1370285 : CollatzResearch.WordTrace tailWord_1370285 prefixEnd_1370285 469076559097517658223787 := by
  unfold tailWord_1370285
  simp only [CollatzResearch.WordTrace]
  refine ⟨49978399840698945891344309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33318933227132630594229539 49978399840698945891344309)
  ·
    refine ⟨4685474985065526177313529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49978399840698945891344309 4685474985065526177313529)
    ·
      refine ⟨3514106238799144632985147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4685474985065526177313529 3514106238799144632985147)
      ·
        refine ⟨5271159358198716949477721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514106238799144632985147 5271159358198716949477721)
        ·
          refine ⟨3953369518649037712108291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5271159358198716949477721 3953369518649037712108291)
          ·
            refine ⟨5930054277973556568162437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3953369518649037712108291 5930054277973556568162437)
            ·
              refine ⟨1111885177120041856530457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5930054277973556568162437 1111885177120041856530457)
              ·
                refine ⟨833913882840031392397843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111885177120041856530457 833913882840031392397843)
                ·
                  refine ⟨1250870824260047088596765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833913882840031392397843 1250870824260047088596765)
                  ·
                    refine ⟨469076559097517658223787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250870824260047088596765 469076559097517658223787)
                    ·
                      rfl

theorem cell22_1370285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1370285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370285 prefixEnd_1370285 := by exact prefixLift 1370285
  have htrace : WordTrace (prefixWord ++ tailWord_1370285) baseStart_1370285 baseEnd_1370285 := by
    simpa [prefixWord, tailWord_1370285, baseEnd_1370285] using wordTrace_append hprefix tailTrace_1370285
  have hstable : (prefixWord ++ tailWord_1370285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370285).length < 2 ^ (prefixWord ++ tailWord_1370285).sum := by decide
  have hdescent : baseEnd_1370285 < baseStart_1370285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370328 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 1, 4]
def baseStart_1370328 : Nat := 118140960795 + 1370328 * 2 ^ 59
def prefixEnd_1370328 : Nat := 4983230072969 + 3 ^ 40 * 1370328 * 2
def baseEnd_1370328 : Nat := 469091278876279879398655

theorem tailTrace_1370328 : CollatzResearch.WordTrace tailWord_1370328 prefixEnd_1370328 469091278876279879398655 := by
  unfold tailWord_1370328
  simp only [CollatzResearch.WordTrace]
  refine ⟨24989984089771582117579819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33319978786362109490106425 24989984089771582117579819)
  ·
    refine ⟨37484976134657373176369729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24989984089771582117579819 37484976134657373176369729)
    ·
      refine ⟨28113732100993029882277297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37484976134657373176369729 28113732100993029882277297)
      ·
        refine ⟨21085299075744772411707973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28113732100993029882277297 21085299075744772411707973)
        ·
          refine ⟨3953493576702144827195245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21085299075744772411707973 3953493576702144827195245)
          ·
            refine ⟨1482560091263304310198217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3953493576702144827195245 1482560091263304310198217)
            ·
              refine ⟨1111920068447478232648663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1482560091263304310198217 1111920068447478232648663)
              ·
                refine ⟨1667880102671217348972995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111920068447478232648663 1667880102671217348972995)
                ·
                  refine ⟨2501820154006826023459493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667880102671217348972995 2501820154006826023459493)
                  ·
                    refine ⟨469091278876279879398655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2501820154006826023459493 469091278876279879398655)
                    ·
                      rfl

theorem cell22_1370328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_1370328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370328 prefixEnd_1370328 := by exact prefixLift 1370328
  have htrace : WordTrace (prefixWord ++ tailWord_1370328) baseStart_1370328 baseEnd_1370328 := by
    simpa [prefixWord, tailWord_1370328, baseEnd_1370328] using wordTrace_append hprefix tailTrace_1370328
  have hstable : (prefixWord ++ tailWord_1370328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370328).length < 2 ^ (prefixWord ++ tailWord_1370328).sum := by decide
  have hdescent : baseEnd_1370328 < baseStart_1370328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370337 : List Nat := [1, 2, 3, 1, 3, 1, 11]
def baseStart_1370337 : Nat := 118140960795 + 1370337 * 2 ^ 59
def prefixEnd_1370337 : Nat := 4983230072969 + 3 ^ 40 * 1370337 * 2
def baseEnd_1370337 : Nat := 17373865176303957626801

theorem tailTrace_1370337 : CollatzResearch.WordTrace tailWord_1370337 prefixEnd_1370337 17373865176303957626801 := by
  unfold tailWord_1370337
  simp only [CollatzResearch.WordTrace]
  refine ⟨49980296436510558772237265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33320197624340372514824843 49980296436510558772237265)
  ·
    refine ⟨37485222327382919079177949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49980296436510558772237265 37485222327382919079177949)
    ·
      refine ⟨14056958372768594654691731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37485222327382919079177949 14056958372768594654691731)
      ·
        refine ⟨21085437559152891982037597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14056958372768594654691731 21085437559152891982037597)
        ·
          refine ⟨7907039084682334493264099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21085437559152891982037597 7907039084682334493264099)
          ·
            refine ⟨11860558627023501739896149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907039084682334493264099 11860558627023501739896149)
            ·
              refine ⟨17373865176303957626801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11860558627023501739896149 17373865176303957626801)
              ·
                rfl

theorem cell22_1370337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 11].length) (baseStart_1370337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370337 prefixEnd_1370337 := by exact prefixLift 1370337
  have htrace : WordTrace (prefixWord ++ tailWord_1370337) baseStart_1370337 baseEnd_1370337 := by
    simpa [prefixWord, tailWord_1370337, baseEnd_1370337] using wordTrace_append hprefix tailTrace_1370337
  have hstable : (prefixWord ++ tailWord_1370337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370337).length < 2 ^ (prefixWord ++ tailWord_1370337).sum := by decide
  have hdescent : baseEnd_1370337 < baseStart_1370337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370341 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_1370341 : Nat := 118140960795 + 1370341 * 2 ^ 59
def prefixEnd_1370341 : Nat := 4983230072969 + 3 ^ 40 * 1370341 * 2
def baseEnd_1370341 : Nat := 469095729041952178823615

theorem tailTrace_1370341 : CollatzResearch.WordTrace tailWord_1370341 prefixEnd_1370341 469095729041952178823615 := by
  unfold tailWord_1370341
  simp only [CollatzResearch.WordTrace]
  refine ⟨49980442328496067455382877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33320294885664044970255251 49980442328496067455382877)
  ·
    refine ⟨18742665873186025295768579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49980442328496067455382877 18742665873186025295768579)
    ·
      refine ⟨28113998809779037943652869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18742665873186025295768579 28113998809779037943652869)
      ·
        refine ⟨5271374776833569614434913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28113998809779037943652869 5271374776833569614434913)
        ·
          refine ⟨3953531082625177210826185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5271374776833569614434913 3953531082625177210826185)
          ·
            refine ⟨2965148311968882908119639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953531082625177210826185 2965148311968882908119639)
            ·
              refine ⟨4447722467953324362179459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965148311968882908119639 4447722467953324362179459)
              ·
                refine ⟨6671583701929986543269189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447722467953324362179459 6671583701929986543269189)
                ·
                  refine ⟨1250921944111872476862973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6671583701929986543269189 1250921944111872476862973)
                  ·
                    refine ⟨469095729041952178823615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250921944111872476862973 469095729041952178823615)
                    ·
                      rfl

theorem cell22_1370341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_1370341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370341 prefixEnd_1370341 := by exact prefixLift 1370341
  have htrace : WordTrace (prefixWord ++ tailWord_1370341) baseStart_1370341 baseEnd_1370341 := by
    simpa [prefixWord, tailWord_1370341, baseEnd_1370341] using wordTrace_append hprefix tailTrace_1370341
  have hstable : (prefixWord ++ tailWord_1370341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370341).length < 2 ^ (prefixWord ++ tailWord_1370341).sum := by decide
  have hdescent : baseEnd_1370341 < baseStart_1370341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370399 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 7]
def baseStart_1370399 : Nat := 118140960795 + 1370399 * 2 ^ 59
def prefixEnd_1370399 : Nat := 4983230072969 + 3 ^ 40 * 1370399 * 2
def baseEnd_1370399 : Nat := 156371861209086453624479

theorem tailTrace_1370399 : CollatzResearch.WordTrace tailWord_1370399 prefixEnd_1370399 156371861209086453624479 := by
  unfold tailWord_1370399
  simp only [CollatzResearch.WordTrace]
  refine ⟨49982557762285943360994251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33321705174857295573996167 49982557762285943360994251)
  ·
    refine ⟨74973836643428915041491377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49982557762285943360994251 74973836643428915041491377)
    ·
      refine ⟨56230377482571686281118533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74973836643428915041491377 56230377482571686281118533)
      ·
        refine ⟨10543195777982191177709725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56230377482571686281118533 10543195777982191177709725)
        ·
          refine ⟨3953698416743321691641147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10543195777982191177709725 3953698416743321691641147)
          ·
            refine ⟨5930547625114982537461721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3953698416743321691641147 5930547625114982537461721)
            ·
              refine ⟨4447910718836236903096291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5930547625114982537461721 4447910718836236903096291)
              ·
                refine ⟨6671866078254355354644437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447910718836236903096291 6671866078254355354644437)
                ·
                  refine ⟨156371861209086453624479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6671866078254355354644437 156371861209086453624479)
                  ·
                    rfl

theorem cell22_1370399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 7].length) (baseStart_1370399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370399 prefixEnd_1370399 := by exact prefixLift 1370399
  have htrace : WordTrace (prefixWord ++ tailWord_1370399) baseStart_1370399 baseEnd_1370399 := by
    simpa [prefixWord, tailWord_1370399, baseEnd_1370399] using wordTrace_append hprefix tailTrace_1370399
  have hstable : (prefixWord ++ tailWord_1370399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370399).length < 2 ^ (prefixWord ++ tailWord_1370399).sum := by decide
  have hdescent : baseEnd_1370399 < baseStart_1370399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370491 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 2, 4]
def baseStart_1370491 : Nat := 118140960795 + 1370491 * 2 ^ 59
def prefixEnd_1370491 : Nat := 4983230072969 + 3 ^ 40 * 1370491 * 2
def baseEnd_1370491 : Nat := 469147077107401787573155

theorem tailTrace_1370491 : CollatzResearch.WordTrace tailWord_1370491 prefixEnd_1370491 469147077107401787573155 := by
  unfold tailWord_1370491
  simp only [CollatzResearch.WordTrace]
  refine ⟨49985913277952643073343327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33323942185301762048895551 49985913277952643073343327)
  ·
    refine ⟨74978869916928964610014991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49985913277952643073343327 74978869916928964610014991)
    ·
      refine ⟨112468304875393446915022487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74978869916928964610014991 112468304875393446915022487)
      ·
        refine ⟨168702457313090170372533731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112468304875393446915022487 168702457313090170372533731)
        ·
          refine ⟨253053685969635255558800597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168702457313090170372533731 253053685969635255558800597)
          ·
            refine ⟨5930945764913326302159389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 253053685969635255558800597 5930945764913326302159389)
            ·
              refine ⟨2224104661842497363309771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5930945764913326302159389 2224104661842497363309771)
              ·
                refine ⟨3336156992763746044964657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224104661842497363309771 3336156992763746044964657)
                ·
                  refine ⟨2502117744572809533723493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3336156992763746044964657 2502117744572809533723493)
                  ·
                    refine ⟨469147077107401787573155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2502117744572809533723493 469147077107401787573155)
                    ·
                      rfl

theorem cell22_1370491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4].length) (baseStart_1370491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370491 prefixEnd_1370491 := by exact prefixLift 1370491
  have htrace : WordTrace (prefixWord ++ tailWord_1370491) baseStart_1370491 baseEnd_1370491 := by
    simpa [prefixWord, tailWord_1370491, baseEnd_1370491] using wordTrace_append hprefix tailTrace_1370491
  have hstable : (prefixWord ++ tailWord_1370491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370491).length < 2 ^ (prefixWord ++ tailWord_1370491).sum := by decide
  have hdescent : baseEnd_1370491 < baseStart_1370491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370510 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_1370510 : Nat := 118140960795 + 1370510 * 2 ^ 59
def prefixEnd_1370510 : Nat := 4983230072969 + 3 ^ 40 * 1370510 * 2
def baseEnd_1370510 : Nat := 469153581195692071348097

theorem tailTrace_1370510 : CollatzResearch.WordTrace tailWord_1370510 prefixEnd_1370510 469153581195692071348097 := by
  unfold tailWord_1370510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6248325783110476164785623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33324404176589206212189989 6248325783110476164785623)
  ·
    refine ⟨9372488674665714247178435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6248325783110476164785623 9372488674665714247178435)
    ·
      refine ⟨14058733011998571370767653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9372488674665714247178435 14058733011998571370767653)
      ·
        refine ⟨2636012439749732132018935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14058733011998571370767653 2636012439749732132018935)
        ·
          refine ⟨3954018659624598198028403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636012439749732132018935 3954018659624598198028403)
          ·
            refine ⟨5931027989436897297042605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954018659624598198028403 5931027989436897297042605)
            ·
              refine ⟨2224135496038836486390977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5931027989436897297042605 2224135496038836486390977)
              ·
                refine ⟨1668101622029127364793233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224135496038836486390977 1668101622029127364793233)
                ·
                  refine ⟨1251076216521845523594925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668101622029127364793233 1251076216521845523594925)
                  ·
                    refine ⟨469153581195692071348097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251076216521845523594925 469153581195692071348097)
                    ·
                      rfl

theorem cell22_1370510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_1370510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370510 prefixEnd_1370510 := by exact prefixLift 1370510
  have htrace : WordTrace (prefixWord ++ tailWord_1370510) baseStart_1370510 baseEnd_1370510 := by
    simpa [prefixWord, tailWord_1370510, baseEnd_1370510] using wordTrace_append hprefix tailTrace_1370510
  have hstable : (prefixWord ++ tailWord_1370510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370510).length < 2 ^ (prefixWord ++ tailWord_1370510).sum := by decide
  have hdescent : baseEnd_1370510 < baseStart_1370510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370519 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1370519 : Nat := 118140960795 + 1370519 * 2 ^ 59
def prefixEnd_1370519 : Nat := 4983230072969 + 3 ^ 40 * 1370519 * 2
def baseEnd_1370519 : Nat := 469156662079619047873069

theorem tailTrace_1370519 : CollatzResearch.WordTrace tailWord_1370519 prefixEnd_1370519 469156662079619047873069 := by
  unfold tailWord_1370519
  simp only [CollatzResearch.WordTrace]
  refine ⟨49986934521851203855362611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33324623014567469236908407 49986934521851203855362611)
  ·
    refine ⟨74980401782776805783043917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49986934521851203855362611 74980401782776805783043917)
    ·
      refine ⟨28117650668541302168641469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74980401782776805783043917 28117650668541302168641469)
      ·
        refine ⟨10544119000702988313240551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28117650668541302168641469 10544119000702988313240551)
        ·
          refine ⟨15816178501054482469860827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544119000702988313240551 15816178501054482469860827)
          ·
            refine ⟨23724267751581723704791241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15816178501054482469860827 23724267751581723704791241)
            ·
              refine ⟨17793200813686292778593431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23724267751581723704791241 17793200813686292778593431)
              ·
                refine ⟨26689801220529439167890147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17793200813686292778593431 26689801220529439167890147)
                ·
                  refine ⟨40034701830794158751835221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26689801220529439167890147 40034701830794158751835221)
                  ·
                    refine ⟨469156662079619047873069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40034701830794158751835221 469156662079619047873069)
                    ·
                      rfl

theorem cell22_1370519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1370519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370519 prefixEnd_1370519 := by exact prefixLift 1370519
  have htrace : WordTrace (prefixWord ++ tailWord_1370519) baseStart_1370519 baseEnd_1370519 := by
    simpa [prefixWord, tailWord_1370519, baseEnd_1370519] using wordTrace_append hprefix tailTrace_1370519
  have hstable : (prefixWord ++ tailWord_1370519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370519).length < 2 ^ (prefixWord ++ tailWord_1370519).sum := by decide
  have hdescent : baseEnd_1370519 < baseStart_1370519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370572 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_1370572 : Nat := 118140960795 + 1370572 * 2 ^ 59
def prefixEnd_1370572 : Nat := 4983230072969 + 3 ^ 40 * 1370572 * 2
def baseEnd_1370572 : Nat := 469174805062744576297907

theorem tailTrace_1370572 : CollatzResearch.WordTrace tailWord_1370572 prefixEnd_1370572 469174805062744576297907 := by
  unfold tailWord_1370572
  simp only [CollatzResearch.WordTrace]
  refine ⟨24994433795329596953520985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33325911727106129271361313 24994433795329596953520985)
  ·
    refine ⟨18745825346497197715140739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24994433795329596953520985 18745825346497197715140739)
    ·
      refine ⟨28118738019745796572711109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18745825346497197715140739 28118738019745796572711109)
      ·
        refine ⟨5272263378702336857383333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28118738019745796572711109 5272263378702336857383333)
        ·
          refine ⟨988549383506688160759375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5272263378702336857383333 988549383506688160759375)
          ·
            refine ⟨1482824075260032241139063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988549383506688160759375 1482824075260032241139063)
            ·
              refine ⟨2224236112890048361708595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482824075260032241139063 2224236112890048361708595)
              ·
                refine ⟨3336354169335072542562893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224236112890048361708595 3336354169335072542562893)
                ·
                  refine ⟨1251132813500652203461085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3336354169335072542562893 1251132813500652203461085)
                  ·
                    refine ⟨469174805062744576297907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251132813500652203461085 469174805062744576297907)
                    ·
                      rfl

theorem cell22_1370572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_1370572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370572 prefixEnd_1370572 := by exact prefixLift 1370572
  have htrace : WordTrace (prefixWord ++ tailWord_1370572) baseStart_1370572 baseEnd_1370572 := by
    simpa [prefixWord, tailWord_1370572, baseEnd_1370572] using wordTrace_append hprefix tailTrace_1370572
  have hstable : (prefixWord ++ tailWord_1370572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370572).length < 2 ^ (prefixWord ++ tailWord_1370572).sum := by decide
  have hdescent : baseEnd_1370572 < baseStart_1370572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370611 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 1, 5]
def baseStart_1370611 : Nat := 118140960795 + 1370611 * 2 ^ 59
def prefixEnd_1370611 : Nat := 4983230072969 + 3 ^ 40 * 1370611 * 2
def baseEnd_1370611 : Nat := 469188155559761474572787

theorem tailTrace_1370611 : CollatzResearch.WordTrace tailWord_1370611 prefixEnd_1370611 469188155559761474572787 := by
  unfold tailWord_1370611
  simp only [CollatzResearch.WordTrace]
  refine ⟨49990290037517903567711687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33326860025011935711807791 49990290037517903567711687)
  ·
    refine ⟨74985435056276855351567531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49990290037517903567711687 74985435056276855351567531)
    ·
      refine ⟨112478152584415283027351297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74985435056276855351567531 112478152584415283027351297)
      ·
        refine ⟨84358614438311462270513473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112478152584415283027351297 84358614438311462270513473)
        ·
          refine ⟨63268960828733596702885105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84358614438311462270513473 63268960828733596702885105)
          ·
            refine ⟨47451720621550197527163829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63268960828733596702885105 47451720621550197527163829)
            ·
              refine ⟨4448598808270331018171609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47451720621550197527163829 4448598808270331018171609)
              ·
                refine ⟨3336449106202748263628707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4448598808270331018171609 3336449106202748263628707)
                ·
                  refine ⟨5004673659304122395443061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336449106202748263628707 5004673659304122395443061)
                  ·
                    refine ⟨469188155559761474572787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5004673659304122395443061 469188155559761474572787)
                    ·
                      rfl

theorem cell22_1370611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_1370611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370611 prefixEnd_1370611 := by exact prefixLift 1370611
  have htrace : WordTrace (prefixWord ++ tailWord_1370611) baseStart_1370611 baseEnd_1370611 := by
    simpa [prefixWord, tailWord_1370611, baseEnd_1370611] using wordTrace_append hprefix tailTrace_1370611
  have hstable : (prefixWord ++ tailWord_1370611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370611).length < 2 ^ (prefixWord ++ tailWord_1370611).sum := by decide
  have hdescent : baseEnd_1370611 < baseStart_1370611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370660 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_1370660 : Nat := 118140960795 + 1370660 * 2 ^ 59
def prefixEnd_1370660 : Nat := 4983230072969 + 3 ^ 40 * 1370660 * 2
def baseEnd_1370660 : Nat := 469204929261141680097637

theorem tailTrace_1370660 : CollatzResearch.WordTrace tailWord_1370660 prefixEnd_1370660 469204929261141680097637 := by
  unfold tailWord_1370660
  simp only [CollatzResearch.WordTrace]
  refine ⟨24996038607170192468122717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33328051476226923290830289 24996038607170192468122717)
  ·
    refine ⟨9373514477688822175546019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24996038607170192468122717 9373514477688822175546019)
    ·
      refine ⟨14060271716533233263319029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9373514477688822175546019 14060271716533233263319029)
      ·
        refine ⟨1318150473424990618436159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14060271716533233263319029 1318150473424990618436159)
        ·
          refine ⟨1977225710137485927654239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318150473424990618436159 1977225710137485927654239)
          ·
            refine ⟨2965838565206228891481359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977225710137485927654239 2965838565206228891481359)
            ·
              refine ⟨4448757847809343337222039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965838565206228891481359 4448757847809343337222039)
              ·
                refine ⟨6673136771714015005833059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448757847809343337222039 6673136771714015005833059)
                ·
                  refine ⟨10009705157571022508749589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6673136771714015005833059 10009705157571022508749589)
                  ·
                    refine ⟨469204929261141680097637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10009705157571022508749589 469204929261141680097637)
                    ·
                      rfl

theorem cell22_1370660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_1370660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370660 prefixEnd_1370660 := by exact prefixLift 1370660
  have htrace : WordTrace (prefixWord ++ tailWord_1370660) baseStart_1370660 baseEnd_1370660 := by
    simpa [prefixWord, tailWord_1370660, baseEnd_1370660] using wordTrace_append hprefix tailTrace_1370660
  have hstable : (prefixWord ++ tailWord_1370660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370660).length < 2 ^ (prefixWord ++ tailWord_1370660).sum := by decide
  have hdescent : baseEnd_1370660 < baseStart_1370660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370741 : List Nat := [1, 3, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1370741 : Nat := 118140960795 + 1370741 * 2 ^ 59
def prefixEnd_1370741 : Nat := 4983230072969 + 3 ^ 40 * 1370741 * 2
def baseEnd_1370741 : Nat := 469232657216484468822389

theorem tailTrace_1370741 : CollatzResearch.WordTrace tailWord_1370741 prefixEnd_1370741 469232657216484468822389 := by
  unfold tailWord_1370741
  simp only [CollatzResearch.WordTrace]
  refine ⟨49995031527046935769944077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33330021018031290513296051 49995031527046935769944077)
  ·
    refine ⟨18748136822642600913729029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49995031527046935769944077 18748136822642600913729029)
    ·
      refine ⟨3515275654245487671324193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18748136822642600913729029 3515275654245487671324193)
      ·
        refine ⟨2636456740684115753493145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3515275654245487671324193 2636456740684115753493145)
        ·
          refine ⟨1977342555513086815119859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2636456740684115753493145 1977342555513086815119859)
          ·
            refine ⟨2966013833269630222679789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977342555513086815119859 2966013833269630222679789)
            ·
              refine ⟨1112255187476111333504921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2966013833269630222679789 1112255187476111333504921)
              ·
                refine ⟨834191390607083500128691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112255187476111333504921 834191390607083500128691)
                ·
                  refine ⟨1251287085910625250193037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834191390607083500128691 1251287085910625250193037)
                  ·
                    refine ⟨469232657216484468822389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251287085910625250193037 469232657216484468822389)
                    ·
                      rfl

theorem cell22_1370741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1370741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370741 prefixEnd_1370741 := by exact prefixLift 1370741
  have htrace : WordTrace (prefixWord ++ tailWord_1370741) baseStart_1370741 baseEnd_1370741 := by
    simpa [prefixWord, tailWord_1370741, baseEnd_1370741] using wordTrace_append hprefix tailTrace_1370741
  have hstable : (prefixWord ++ tailWord_1370741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370741).length < 2 ^ (prefixWord ++ tailWord_1370741).sum := by decide
  have hdescent : baseEnd_1370741 < baseStart_1370741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370748 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 6]
def baseStart_1370748 : Nat := 118140960795 + 1370748 * 2 ^ 59
def prefixEnd_1370748 : Nat := 4983230072969 + 3 ^ 40 * 1370748 * 2
def baseEnd_1370748 : Nat := 156411684486512927965789

theorem tailTrace_1370748 : CollatzResearch.WordTrace tailWord_1370748 prefixEnd_1370748 156411684486512927965789 := by
  unfold tailWord_1370748
  simp only [CollatzResearch.WordTrace]
  refine ⟨24997643419010787982724449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33330191225347717310299265 24997643419010787982724449)
  ·
    refine ⟨18748232564258090987043337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24997643419010787982724449 18748232564258090987043337)
    ·
      refine ⟨14061174423193568240282503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18748232564258090987043337 14061174423193568240282503)
      ·
        refine ⟨21091761634790352360423755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14061174423193568240282503 21091761634790352360423755)
        ·
          refine ⟨31637642452185528540635633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21091761634790352360423755 31637642452185528540635633)
          ·
            refine ⟨23728231839139146405476725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31637642452185528540635633 23728231839139146405476725)
            ·
              refine ⟨2224521734919294975513443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23728231839139146405476725 2224521734919294975513443)
              ·
                refine ⟨3336782602378942463270165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224521734919294975513443 3336782602378942463270165)
                ·
                  refine ⟨156411684486512927965789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3336782602378942463270165 156411684486512927965789)
                  ·
                    rfl

theorem cell22_1370748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_1370748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370748 prefixEnd_1370748 := by exact prefixLift 1370748
  have htrace : WordTrace (prefixWord ++ tailWord_1370748) baseStart_1370748 baseEnd_1370748 := by
    simpa [prefixWord, tailWord_1370748, baseEnd_1370748] using wordTrace_append hprefix tailTrace_1370748
  have hstable : (prefixWord ++ tailWord_1370748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370748).length < 2 ^ (prefixWord ++ tailWord_1370748).sum := by decide
  have hdescent : baseEnd_1370748 < baseStart_1370748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370763 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 6, 3]
def baseStart_1370763 : Nat := 118140960795 + 1370763 * 2 ^ 59
def prefixEnd_1370763 : Nat := 4983230072969 + 3 ^ 40 * 1370763 * 2
def baseEnd_1370763 : Nat := 469240188266083744772321

theorem tailTrace_1370763 : CollatzResearch.WordTrace tailWord_1370763 prefixEnd_1370763 469240188266083744772321 := by
  unfold tailWord_1370763
  simp only [CollatzResearch.WordTrace]
  refine ⟨49995833932967233527244943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33330555955311489018163295 49995833932967233527244943)
  ·
    refine ⟨74993750899450850290867415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49995833932967233527244943 74993750899450850290867415)
    ·
      refine ⟨112490626349176275436301123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74993750899450850290867415 112490626349176275436301123)
      ·
        refine ⟨168735939523764413154451685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112490626349176275436301123 168735939523764413154451685)
        ·
          refine ⟨31637988660705827466459691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168735939523764413154451685 31637988660705827466459691)
          ·
            refine ⟨47456982991058741199689537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31637988660705827466459691 47456982991058741199689537)
            ·
              refine ⟨35592737243294055899767153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47456982991058741199689537 35592737243294055899767153)
              ·
                refine ⟨26694552932470541924825365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35592737243294055899767153 26694552932470541924825365)
                ·
                  refine ⟨1251307168709556652726189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26694552932470541924825365 1251307168709556652726189)
                  ·
                    refine ⟨469240188266083744772321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251307168709556652726189 469240188266083744772321)
                    ·
                      rfl

theorem cell22_1370763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 3].length) (baseStart_1370763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370763 prefixEnd_1370763 := by exact prefixLift 1370763
  have htrace : WordTrace (prefixWord ++ tailWord_1370763) baseStart_1370763 baseEnd_1370763 := by
    simpa [prefixWord, tailWord_1370763, baseEnd_1370763] using wordTrace_append hprefix tailTrace_1370763
  have hstable : (prefixWord ++ tailWord_1370763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370763).length < 2 ^ (prefixWord ++ tailWord_1370763).sum := by decide
  have hdescent : baseEnd_1370763 < baseStart_1370763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370780 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1370780 : Nat := 118140960795 + 1370780 * 2 ^ 59
def prefixEnd_1370780 : Nat := 4983230072969 + 3 ^ 40 * 1370780 * 2
def baseEnd_1370780 : Nat := 469246007713501367097269

theorem tailTrace_1370780 : CollatzResearch.WordTrace tailWord_1370780 prefixEnd_1370780 469246007713501367097269 := by
  unfold tailWord_1370780
  simp only [CollatzResearch.WordTrace]
  refine ⟨24998226986952822715306897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33330969315937096953742529 24998226986952822715306897)
  ·
    refine ⟨18748670240214617036480173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24998226986952822715306897 18748670240214617036480173)
    ·
      refine ⟨7030751340080481388680065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18748670240214617036480173 7030751340080481388680065)
      ·
        refine ⟨5273063505060361041510049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7030751340080481388680065 5273063505060361041510049)
        ·
          refine ⟨3954797628795270781132537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5273063505060361041510049 3954797628795270781132537)
          ·
            refine ⟨2966098221596453085849403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3954797628795270781132537 2966098221596453085849403)
            ·
              refine ⟨4449147332394679628774105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966098221596453085849403 4449147332394679628774105)
              ·
                refine ⟨3336860499296009721580579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4449147332394679628774105 3336860499296009721580579)
                ·
                  refine ⟨5005290748944014582370869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336860499296009721580579 5005290748944014582370869)
                  ·
                    refine ⟨469246007713501367097269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5005290748944014582370869 469246007713501367097269)
                    ·
                      rfl

theorem cell22_1370780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1370780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370780 prefixEnd_1370780 := by exact prefixLift 1370780
  have htrace : WordTrace (prefixWord ++ tailWord_1370780) baseStart_1370780 baseEnd_1370780 := by
    simpa [prefixWord, tailWord_1370780, baseEnd_1370780] using wordTrace_append hprefix tailTrace_1370780
  have hstable : (prefixWord ++ tailWord_1370780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370780).length < 2 ^ (prefixWord ++ tailWord_1370780).sum := by decide
  have hdescent : baseEnd_1370780 < baseStart_1370780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370782 : List Nat := [4, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1370782 : Nat := 118140960795 + 1370782 * 2 ^ 59
def prefixEnd_1370782 : Nat := 4983230072969 + 3 ^ 40 * 1370782 * 2
def baseEnd_1370782 : Nat := 156415564118124676182421

theorem tailTrace_1370782 : CollatzResearch.WordTrace tailWord_1370782 prefixEnd_1370782 156415564118124676182421 := by
  unfold tailWord_1370782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249565864987299971523325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33331017946598933181457733 6249565864987299971523325)
  ·
    refine ⟨2343587199370237489321247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6249565864987299971523325 2343587199370237489321247)
    ·
      refine ⟨3515380799055356233981871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2343587199370237489321247 3515380799055356233981871)
      ·
        refine ⟨5273071198583034350972807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515380799055356233981871 5273071198583034350972807)
        ·
          refine ⟨7909606797874551526459211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273071198583034350972807 7909606797874551526459211)
          ·
            refine ⟨11864410196811827289688817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7909606797874551526459211 11864410196811827289688817)
            ·
              refine ⟨8898307647608870467266613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11864410196811827289688817 8898307647608870467266613)
              ·
                refine ⟨834216341963331606306245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8898307647608870467266613 834216341963331606306245)
                ·
                  refine ⟨156415564118124676182421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834216341963331606306245 156415564118124676182421)
                  ·
                    rfl

theorem cell22_1370782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1370782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370782 prefixEnd_1370782 := by exact prefixLift 1370782
  have htrace : WordTrace (prefixWord ++ tailWord_1370782) baseStart_1370782 baseEnd_1370782 := by
    simpa [prefixWord, tailWord_1370782, baseEnd_1370782] using wordTrace_append hprefix tailTrace_1370782
  have hstable : (prefixWord ++ tailWord_1370782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370782).length < 2 ^ (prefixWord ++ tailWord_1370782).sum := by decide
  have hdescent : baseEnd_1370782 < baseStart_1370782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370797 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1370797 : Nat := 118140960795 + 1370797 * 2 ^ 59
def prefixEnd_1370797 : Nat := 4983230072969 + 3 ^ 40 * 1370797 * 2
def baseEnd_1370797 : Nat := 469251827160918989422217

theorem tailTrace_1370797 : CollatzResearch.WordTrace tailWord_1370797 prefixEnd_1370797 469251827160918989422217 := by
  unfold tailWord_1370797
  simp only [CollatzResearch.WordTrace]
  refine ⟨49997074014844057333982645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33331382676562704889321763 49997074014844057333982645)
  ·
    refine ⟨4687225688891630375060873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49997074014844057333982645 4687225688891630375060873)
    ·
      refine ⟨3515419266668722781295655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4687225688891630375060873 3515419266668722781295655)
      ·
        refine ⟨5273128900003084171943483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515419266668722781295655 5273128900003084171943483)
        ·
          refine ⟨7909693350004626257915225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273128900003084171943483 7909693350004626257915225)
          ·
            refine ⟨5932270012503469693436419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7909693350004626257915225 5932270012503469693436419)
            ·
              refine ⟨8898405018755204540154629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932270012503469693436419 8898405018755204540154629)
              ·
                refine ⟨1668450941016600851278993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8898405018755204540154629 1668450941016600851278993)
                ·
                  refine ⟨1251338205762450638459245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668450941016600851278993 1251338205762450638459245)
                  ·
                    refine ⟨469251827160918989422217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251338205762450638459245 469251827160918989422217)
                    ·
                      rfl

theorem cell22_1370797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1370797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370797 prefixEnd_1370797 := by exact prefixLift 1370797
  have htrace : WordTrace (prefixWord ++ tailWord_1370797) baseStart_1370797 baseEnd_1370797 := by
    simpa [prefixWord, tailWord_1370797, baseEnd_1370797] using wordTrace_append hprefix tailTrace_1370797
  have hstable : (prefixWord ++ tailWord_1370797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370797).length < 2 ^ (prefixWord ++ tailWord_1370797).sum := by decide
  have hdescent : baseEnd_1370797 < baseStart_1370797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370870 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1370870 : Nat := 118140960795 + 1370870 * 2 ^ 59
def prefixEnd_1370870 : Nat := 4983230072969 + 3 ^ 40 * 1370870 * 2
def baseEnd_1370870 : Nat := 469276816552771132346993

theorem tailTrace_1370870 : CollatzResearch.WordTrace tailWord_1370870 prefixEnd_1370870 469276816552771132346993 := by
  unfold tailWord_1370870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124983533973724425086879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33333157695719727200926709 3124983533973724425086879)
  ·
    refine ⟨4687475300960586637630319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3124983533973724425086879 4687475300960586637630319)
    ·
      refine ⟨7031212951440879956445479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687475300960586637630319 7031212951440879956445479)
      ·
        refine ⟨10546819427161319934668219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7031212951440879956445479 10546819427161319934668219)
        ·
          refine ⟨15820229140741979902002329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546819427161319934668219 15820229140741979902002329)
          ·
            refine ⟨11865171855556484926501747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15820229140741979902002329 11865171855556484926501747)
            ·
              refine ⟨17797757783334727389752621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865171855556484926501747 17797757783334727389752621)
              ·
                refine ⟨6674159168750522771157233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17797757783334727389752621 6674159168750522771157233)
                ·
                  refine ⟨5005619376562892078367925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674159168750522771157233 5005619376562892078367925)
                  ·
                    refine ⟨469276816552771132346993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5005619376562892078367925 469276816552771132346993)
                    ·
                      rfl

theorem cell22_1370870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1370870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370870 prefixEnd_1370870 := by exact prefixLift 1370870
  have htrace : WordTrace (prefixWord ++ tailWord_1370870) baseStart_1370870 baseEnd_1370870 := by
    simpa [prefixWord, tailWord_1370870, baseEnd_1370870] using wordTrace_append hprefix tailTrace_1370870
  have hstable : (prefixWord ++ tailWord_1370870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370870).length < 2 ^ (prefixWord ++ tailWord_1370870).sum := by decide
  have hdescent : baseEnd_1370870 < baseStart_1370870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370930 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1370930 : Nat := 118140960795 + 1370930 * 2 ^ 59
def prefixEnd_1370930 : Nat := 4983230072969 + 3 ^ 40 * 1370930 * 2
def baseEnd_1370930 : Nat := 469297355778950975846809

theorem tailTrace_1370930 : CollatzResearch.WordTrace tailWord_1370930 prefixEnd_1370930 469297355778950975846809 := by
  unfold tailWord_1370930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12500481230840555262143561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33334616615574814032382829 12500481230840555262143561)
  ·
    refine ⟨9375360923130416446607671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12500481230840555262143561 9375360923130416446607671)
    ·
      refine ⟨14063041384695624669911507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9375360923130416446607671 14063041384695624669911507)
      ·
        refine ⟨21094562077043437004867261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14063041384695624669911507 21094562077043437004867261)
        ·
          refine ⟨7910460778891288876825223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21094562077043437004867261 7910460778891288876825223)
          ·
            refine ⟨11865691168336933315237835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910460778891288876825223 11865691168336933315237835)
            ·
              refine ⟨17798536752505399972856753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865691168336933315237835 17798536752505399972856753)
              ·
                refine ⟨13348902564379049979642565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17798536752505399972856753 13348902564379049979642565)
                ·
                  refine ⟨2502919230821071871182981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13348902564379049979642565 2502919230821071871182981)
                  ·
                    refine ⟨469297355778950975846809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2502919230821071871182981 469297355778950975846809)
                    ·
                      rfl

theorem cell22_1370930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1370930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1370930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1370930 prefixEnd_1370930 := by exact prefixLift 1370930
  have htrace : WordTrace (prefixWord ++ tailWord_1370930) baseStart_1370930 baseEnd_1370930 := by
    simpa [prefixWord, tailWord_1370930, baseEnd_1370930] using wordTrace_append hprefix tailTrace_1370930
  have hstable : (prefixWord ++ tailWord_1370930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370930).length < 2 ^ (prefixWord ++ tailWord_1370930).sum := by decide
  have hdescent : baseEnd_1370930 < baseStart_1370930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371084 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_1371084 : Nat := 118140960795 + 1371084 * 2 ^ 59
def prefixEnd_1371084 : Nat := 4983230072969 + 3 ^ 40 * 1371084 * 2
def baseEnd_1371084 : Nat := 469350073126145907496337

theorem tailTrace_1371084 : CollatzResearch.WordTrace tailWord_1371084 prefixEnd_1371084 469350073126145907496337 := by
  unfold tailWord_1371084
  simp only [CollatzResearch.WordTrace]
  refine ⟨25003770882402152674840153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33338361176536203566453537 25003770882402152674840153)
  ·
    refine ⟨18752828161801614506130115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25003770882402152674840153 18752828161801614506130115)
    ·
      refine ⟨28129242242702421759195173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18752828161801614506130115 28129242242702421759195173)
      ·
        refine ⟨5274232920506704079849095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28129242242702421759195173 5274232920506704079849095)
        ·
          refine ⟨7911349380760056119773643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5274232920506704079849095 7911349380760056119773643)
          ·
            refine ⟨11867024071140084179660465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7911349380760056119773643 11867024071140084179660465)
            ·
              refine ⟨8900268053355063134745349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11867024071140084179660465 8900268053355063134745349)
              ·
                refine ⟨1668800260004074337764753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8900268053355063134745349 1668800260004074337764753)
                ·
                  refine ⟨1251600195003055753323565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668800260004074337764753 1251600195003055753323565)
                  ·
                    refine ⟨469350073126145907496337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251600195003055753323565 469350073126145907496337)
                    ·
                      rfl

theorem cell22_1371084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_1371084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371084 prefixEnd_1371084 := by exact prefixLift 1371084
  have htrace : WordTrace (prefixWord ++ tailWord_1371084) baseStart_1371084 baseEnd_1371084 := by
    simpa [prefixWord, tailWord_1371084, baseEnd_1371084] using wordTrace_append hprefix tailTrace_1371084
  have hstable : (prefixWord ++ tailWord_1371084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371084).length < 2 ^ (prefixWord ++ tailWord_1371084).sum := by decide
  have hdescent : baseEnd_1371084 < baseStart_1371084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371086 : List Nat := [4, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_1371086 : Nat := 118140960795 + 1371086 * 2 ^ 59
def prefixEnd_1371086 : Nat := 4983230072969 + 3 ^ 40 * 1371086 * 2
def baseEnd_1371086 : Nat := 156450252589006189648777

theorem tailTrace_1371086 : CollatzResearch.WordTrace tailWord_1371086 prefixEnd_1371086 156450252589006189648777 := by
  unfold tailWord_1371086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250951838849632461406639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33338409807198039794168741 6250951838849632461406639)
  ·
    refine ⟨9376427758274448692109959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6250951838849632461406639 9376427758274448692109959)
    ·
      refine ⟨14064641637411673038164939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9376427758274448692109959 14064641637411673038164939)
      ·
        refine ⟨21096962456117509557247409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14064641637411673038164939 21096962456117509557247409)
        ·
          refine ⟨15822721842088132167935557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21096962456117509557247409 15822721842088132167935557)
          ·
            refine ⟨2966760345391524781487917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15822721842088132167935557 2966760345391524781487917)
            ·
              refine ⟨1112535129521821793057969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2966760345391524781487917 1112535129521821793057969)
              ·
                refine ⟨834401347141366344793477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112535129521821793057969 834401347141366344793477)
                ·
                  refine ⟨156450252589006189648777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834401347141366344793477 156450252589006189648777)
                  ·
                    rfl

theorem cell22_1371086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_1371086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371086 prefixEnd_1371086 := by exact prefixLift 1371086
  have htrace : WordTrace (prefixWord ++ tailWord_1371086) baseStart_1371086 baseEnd_1371086 := by
    simpa [prefixWord, tailWord_1371086, baseEnd_1371086] using wordTrace_append hprefix tailTrace_1371086
  have hstable : (prefixWord ++ tailWord_1371086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371086).length < 2 ^ (prefixWord ++ tailWord_1371086).sum := by decide
  have hdescent : baseEnd_1371086 < baseStart_1371086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371095 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1371095 : Nat := 118140960795 + 1371095 * 2 ^ 59
def prefixEnd_1371095 : Nat := 4983230072969 + 3 ^ 40 * 1371095 * 2
def baseEnd_1371095 : Nat := 469353838650945545471303

theorem tailTrace_1371095 : CollatzResearch.WordTrace tailWord_1371095 prefixEnd_1371095 469353838650945545471303 := by
  unfold tailWord_1371095
  simp only [CollatzResearch.WordTrace]
  refine ⟨50007942967764454228330739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33338628645176302818887159 50007942967764454228330739)
  ·
    refine ⟨75011914451646681342496109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50007942967764454228330739 75011914451646681342496109)
    ·
      refine ⟨28129467919367505503436041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75011914451646681342496109 28129467919367505503436041)
      ·
        refine ⟨21097100939525629127577031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28129467919367505503436041 21097100939525629127577031)
        ·
          refine ⟨31645651409288443691365547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21097100939525629127577031 31645651409288443691365547)
          ·
            refine ⟨47468477113932665537048321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31645651409288443691365547 47468477113932665537048321)
            ·
              refine ⟨35601357835449499152786241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47468477113932665537048321 35601357835449499152786241)
              ·
                refine ⟨26701018376587124364589681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35601357835449499152786241 26701018376587124364589681)
                ·
                  refine ⟨20025763782440343273442261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26701018376587124364589681 20025763782440343273442261)
                  ·
                    refine ⟨469353838650945545471303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20025763782440343273442261 469353838650945545471303)
                    ·
                      rfl

theorem cell22_1371095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1371095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371095 prefixEnd_1371095 := by exact prefixLift 1371095
  have htrace : WordTrace (prefixWord ++ tailWord_1371095) baseStart_1371095 baseEnd_1371095 := by
    simpa [prefixWord, tailWord_1371095, baseEnd_1371095] using wordTrace_append hprefix tailTrace_1371095
  have hstable : (prefixWord ++ tailWord_1371095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371095).length < 2 ^ (prefixWord ++ tailWord_1371095).sum := by decide
  have hdescent : baseEnd_1371095 < baseStart_1371095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371097 : List Nat := [1, 2, 1, 2, 5, 2, 2, 7]
def baseStart_1371097 : Nat := 118140960795 + 1371097 * 2 ^ 59
def prefixEnd_1371097 : Nat := 4983230072969 + 3 ^ 40 * 1371097 * 2
def baseEnd_1371097 : Nat := 52150502587979800769033

theorem tailTrace_1371097 : CollatzResearch.WordTrace tailWord_1371097 prefixEnd_1371097 52150502587979800769033 := by
  unfold tailWord_1371097
  simp only [CollatzResearch.WordTrace]
  refine ⟨50008015913757208569903545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33338677275838139046602363 50008015913757208569903545)
  ·
    refine ⟨37506011935317906427427659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50008015913757208569903545 37506011935317906427427659)
    ·
      refine ⟨56259017902976859641141489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37506011935317906427427659 56259017902976859641141489)
      ·
        refine ⟨42194263427232644730856117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56259017902976859641141489 42194263427232644730856117)
        ·
          refine ⟨3955712196303060443517761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42194263427232644730856117 3955712196303060443517761)
          ·
            refine ⟨2966784147227295332638321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955712196303060443517761 2966784147227295332638321)
            ·
              refine ⟨2225088110420471499478741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2966784147227295332638321 2225088110420471499478741)
              ·
                refine ⟨52150502587979800769033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2225088110420471499478741 52150502587979800769033)
                ·
                  rfl

theorem cell22_1371097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 7].length) (baseStart_1371097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371097 prefixEnd_1371097 := by exact prefixLift 1371097
  have htrace : WordTrace (prefixWord ++ tailWord_1371097) baseStart_1371097 baseEnd_1371097 := by
    simpa [prefixWord, tailWord_1371097, baseEnd_1371097] using wordTrace_append hprefix tailTrace_1371097
  have hstable : (prefixWord ++ tailWord_1371097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371097).length < 2 ^ (prefixWord ++ tailWord_1371097).sum := by decide
  have hdescent : baseEnd_1371097 < baseStart_1371097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371101 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1371101 : Nat := 118140960795 + 1371101 * 2 ^ 59
def prefixEnd_1371101 : Nat := 4983230072969 + 3 ^ 40 * 1371101 * 2
def baseEnd_1371101 : Nat := 469355892573563529821285

theorem tailTrace_1371101 : CollatzResearch.WordTrace tailWord_1371101 prefixEnd_1371101 469355892573563529821285 := by
  unfold tailWord_1371101
  simp only [CollatzResearch.WordTrace]
  refine ⟨50008161805742717253049157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33338774537161811502032771 50008161805742717253049157)
  ·
    refine ⟨9376530338576759484946717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50008161805742717253049157 9376530338576759484946717)
    ·
      refine ⟨3516198876966284806855019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9376530338576759484946717 3516198876966284806855019)
      ·
        refine ⟨5274298315449427210282529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3516198876966284806855019 5274298315449427210282529)
        ·
          refine ⟨3955723736587070407711897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5274298315449427210282529 3955723736587070407711897)
          ·
            refine ⟨2966792802440302805783923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955723736587070407711897 2966792802440302805783923)
            ·
              refine ⟨4450189203660454208675885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966792802440302805783923 4450189203660454208675885)
              ·
                refine ⟨1668820951372670328253457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4450189203660454208675885 1668820951372670328253457)
                ·
                  refine ⟨1251615713529502746190093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668820951372670328253457 1251615713529502746190093)
                  ·
                    refine ⟨469355892573563529821285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251615713529502746190093 469355892573563529821285)
                    ·
                      rfl

theorem cell22_1371101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1371101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371101 prefixEnd_1371101 := by exact prefixLift 1371101
  have htrace : WordTrace (prefixWord ++ tailWord_1371101) baseStart_1371101 baseEnd_1371101 := by
    simpa [prefixWord, tailWord_1371101, baseEnd_1371101] using wordTrace_append hprefix tailTrace_1371101
  have hstable : (prefixWord ++ tailWord_1371101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371101).length < 2 ^ (prefixWord ++ tailWord_1371101).sum := by decide
  have hdescent : baseEnd_1371101 < baseStart_1371101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371157 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1371157 : Nat := 118140960795 + 1371157 * 2 ^ 59
def prefixEnd_1371157 : Nat := 4983230072969 + 3 ^ 40 * 1371157 * 2
def baseEnd_1371157 : Nat := 469375062517998050421113

theorem tailTrace_1371157 : CollatzResearch.WordTrace tailWord_1371157 prefixEnd_1371157 469375062517998050421113 := by
  unfold tailWord_1371157
  simp only [CollatzResearch.WordTrace]
  refine ⟨50010204293539838817087725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33340136195693225878058483 50010204293539838817087725)
  ·
    refine ⟨18753826610077439556407897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50010204293539838817087725 18753826610077439556407897)
    ·
      refine ⟨14065369957558079667305923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18753826610077439556407897 14065369957558079667305923)
      ·
        refine ⟨21098054936337119500958885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14065369957558079667305923 21098054936337119500958885)
        ·
          refine ⟨3955885300563209906429791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21098054936337119500958885 3955885300563209906429791)
          ·
            refine ⟨5933827950844814859644687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955885300563209906429791 5933827950844814859644687)
            ·
              refine ⟨8900741926267222289467031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933827950844814859644687 8900741926267222289467031)
              ·
                refine ⟨13351112889400833434200547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8900741926267222289467031 13351112889400833434200547)
                ·
                  refine ⟨20026669334101250151300821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13351112889400833434200547 20026669334101250151300821)
                  ·
                    refine ⟨469375062517998050421113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20026669334101250151300821 469375062517998050421113)
                    ·
                      rfl

theorem cell22_1371157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1371157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371157 prefixEnd_1371157 := by exact prefixLift 1371157
  have htrace : WordTrace (prefixWord ++ tailWord_1371157) baseStart_1371157 baseEnd_1371157 := by
    simpa [prefixWord, tailWord_1371157, baseEnd_1371157] using wordTrace_append hprefix tailTrace_1371157
  have hstable : (prefixWord ++ tailWord_1371157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371157).length < 2 ^ (prefixWord ++ tailWord_1371157).sum := by decide
  have hdescent : baseEnd_1371157 < baseStart_1371157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371159 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 5]
def baseStart_1371159 : Nat := 118140960795 + 1371159 * 2 ^ 59
def prefixEnd_1371159 : Nat := 4983230072969 + 3 ^ 40 * 1371159 * 2
def baseEnd_1371159 : Nat := 156458582386290237290369

theorem tailTrace_1371159 : CollatzResearch.WordTrace tailWord_1371159 prefixEnd_1371159 156458582386290237290369 := by
  unfold tailWord_1371159
  simp only [CollatzResearch.WordTrace]
  refine ⟨50010277239532593158660531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33340184826355062105773687 50010277239532593158660531)
  ·
    refine ⟨75015415859298889737990797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50010277239532593158660531 75015415859298889737990797)
    ·
      refine ⟨28130780947237083651746549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75015415859298889737990797 28130780947237083651746549)
      ·
        refine ⟨2637260713803476592351239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28130780947237083651746549 2637260713803476592351239)
        ·
          refine ⟨3955891070705214888526859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637260713803476592351239 3955891070705214888526859)
          ·
            refine ⟨5933836606057822332790289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955891070705214888526859 5933836606057822332790289)
            ·
              refine ⟨4450377454543366749592717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5933836606057822332790289 4450377454543366749592717)
              ·
                refine ⟨1668891545453762531097269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4450377454543366749592717 1668891545453762531097269)
                ·
                  refine ⟨156458582386290237290369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1668891545453762531097269 156458582386290237290369)
                  ·
                    rfl

theorem cell22_1371159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 5].length) (baseStart_1371159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371159 prefixEnd_1371159 := by exact prefixLift 1371159
  have htrace : WordTrace (prefixWord ++ tailWord_1371159) baseStart_1371159 baseEnd_1371159 := by
    simpa [prefixWord, tailWord_1371159, baseEnd_1371159] using wordTrace_append hprefix tailTrace_1371159
  have hstable : (prefixWord ++ tailWord_1371159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371159).length < 2 ^ (prefixWord ++ tailWord_1371159).sum := by decide
  have hdescent : baseEnd_1371159 < baseStart_1371159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371217 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_1371217 : Nat := 118140960795 + 1371217 * 2 ^ 59
def prefixEnd_1371217 : Nat := 4983230072969 + 3 ^ 40 * 1371217 * 2
def baseEnd_1371217 : Nat := 469395601744177893920929

theorem tailTrace_1371217 : CollatzResearch.WordTrace tailWord_1371217 prefixEnd_1371217 469395601744177893920929 := by
  unfold tailWord_1371217
  simp only [CollatzResearch.WordTrace]
  refine ⟨50012392673322469064271905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33341595115548312709514603 50012392673322469064271905)
  ·
    refine ⟨37509294504991851798203929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50012392673322469064271905 37509294504991851798203929)
    ·
      refine ⟨28131970878743888848652947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37509294504991851798203929 28131970878743888848652947)
      ·
        refine ⟨42197956318115833272979421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28131970878743888848652947 42197956318115833272979421)
        ·
          refine ⟨15824233619293437477367283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42197956318115833272979421 15824233619293437477367283)
          ·
            refine ⟨23736350428940156216050925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15824233619293437477367283 23736350428940156216050925)
            ·
              refine ⟨8901131410852558581019097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23736350428940156216050925 8901131410852558581019097)
              ·
                refine ⟨6675848558139418935764323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8901131410852558581019097 6675848558139418935764323)
                ·
                  refine ⟨10013772837209128403646485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675848558139418935764323 10013772837209128403646485)
                  ·
                    refine ⟨469395601744177893920929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10013772837209128403646485 469395601744177893920929)
                    ·
                      rfl

theorem cell22_1371217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_1371217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371217 prefixEnd_1371217 := by exact prefixLift 1371217
  have htrace : WordTrace (prefixWord ++ tailWord_1371217) baseStart_1371217 baseEnd_1371217 := by
    simpa [prefixWord, tailWord_1371217, baseEnd_1371217] using wordTrace_append hprefix tailTrace_1371217
  have hstable : (prefixWord ++ tailWord_1371217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371217).length < 2 ^ (prefixWord ++ tailWord_1371217).sum := by decide
  have hdescent : baseEnd_1371217 < baseStart_1371217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371232 : List Nat := [2, 1, 1, 3, 2, 2, 3, 8]
def baseStart_1371232 : Nat := 118140960795 + 1371232 * 2 ^ 59
def prefixEnd_1371232 : Nat := 4983230072969 + 3 ^ 40 * 1371232 * 2
def baseEnd_1371232 : Nat := 52155637394524761643987

theorem tailTrace_1371232 : CollatzResearch.WordTrace tailWord_1371232 prefixEnd_1371232 52155637394524761643987 := by
  unfold tailWord_1371232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25006469884134063313033975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33341959845512084417378633 25006469884134063313033975)
  ·
    refine ⟨37509704826201094969550963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25006469884134063313033975 37509704826201094969550963)
    ·
      refine ⟨56264557239301642454326445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37509704826201094969550963 56264557239301642454326445)
      ·
        refine ⟨21099208964738115920372417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56264557239301642454326445 21099208964738115920372417)
        ·
          refine ⟨15824406723553586940279313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21099208964738115920372417 15824406723553586940279313)
          ·
            refine ⟨11868305042665190205209485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15824406723553586940279313 11868305042665190205209485)
            ·
              refine ⟨4450614390999446326953557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11868305042665190205209485 4450614390999446326953557)
              ·
                refine ⟨52155637394524761643987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4450614390999446326953557 52155637394524761643987)
                ·
                  rfl

theorem cell22_1371232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_1371232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371232 prefixEnd_1371232 := by exact prefixLift 1371232
  have htrace : WordTrace (prefixWord ++ tailWord_1371232) baseStart_1371232 baseEnd_1371232 := by
    simpa [prefixWord, tailWord_1371232, baseEnd_1371232] using wordTrace_append hprefix tailTrace_1371232
  have hstable : (prefixWord ++ tailWord_1371232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371232).length < 2 ^ (prefixWord ++ tailWord_1371232).sum := by decide
  have hdescent : baseEnd_1371232 < baseStart_1371232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371326 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1371326 : Nat := 118140960795 + 1371326 * 2 ^ 59
def prefixEnd_1371326 : Nat := 4983230072969 + 3 ^ 40 * 1371326 * 2
def baseEnd_1371326 : Nat := 469432914671737942945595

theorem tailTrace_1371326 : CollatzResearch.WordTrace tailWord_1371326 prefixEnd_1371326 469432914671737942945595 := by
  unfold tailWord_1371326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252046028740947584998729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33344245486618387119993221 6252046028740947584998729)
  ·
    refine ⟨4689034521555710688749047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6252046028740947584998729 4689034521555710688749047)
    ·
      refine ⟨7033551782333566033123571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689034521555710688749047 7033551782333566033123571)
      ·
        refine ⟨10550327673500349049685357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7033551782333566033123571 10550327673500349049685357)
        ·
          refine ⟨3956372877562630893632009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10550327673500349049685357 3956372877562630893632009)
          ·
            refine ⟨2967279658171973170224007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3956372877562630893632009 2967279658171973170224007)
            ·
              refine ⟨4450919487257959755336011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967279658171973170224007 4450919487257959755336011)
              ·
                refine ⟨6676379230886939633004017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450919487257959755336011 6676379230886939633004017)
                ·
                  refine ⟨5007284423165204724753013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6676379230886939633004017 5007284423165204724753013)
                  ·
                    refine ⟨469432914671737942945595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5007284423165204724753013 469432914671737942945595)
                    ·
                      rfl

theorem cell22_1371326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1371326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371326 prefixEnd_1371326 := by exact prefixLift 1371326
  have htrace : WordTrace (prefixWord ++ tailWord_1371326) baseStart_1371326 baseEnd_1371326 := by
    simpa [prefixWord, tailWord_1371326, baseEnd_1371326] using wordTrace_append hprefix tailTrace_1371326
  have hstable : (prefixWord ++ tailWord_1371326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371326).length < 2 ^ (prefixWord ++ tailWord_1371326).sum := by decide
  have hdescent : baseEnd_1371326 < baseStart_1371326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371371 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 4, 3]
def baseStart_1371371 : Nat := 118140960795 + 1371371 * 2 ^ 59
def prefixEnd_1371371 : Nat := 4983230072969 + 3 ^ 40 * 1371371 * 2
def baseEnd_1371371 : Nat := 469448319091372825570457

theorem tailTrace_1371371 : CollatzResearch.WordTrace tailWord_1371371 prefixEnd_1371371 469448319091372825570457 := by
  unfold tailWord_1371371
  simp only [CollatzResearch.WordTrace]
  refine ⟨50018009514764553365377967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33345339676509702243585311 50018009514764553365377967)
  ·
    refine ⟨75027014272146830048066951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50018009514764553365377967 75027014272146830048066951)
    ·
      refine ⟨112540521408220245072100427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75027014272146830048066951 112540521408220245072100427)
      ·
        refine ⟨168810782112330367608150641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112540521408220245072100427 168810782112330367608150641)
        ·
          refine ⟨126608086584247775706112981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168810782112330367608150641 126608086584247775706112981)
          ·
            refine ⟨2967377029318307243112023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 126608086584247775706112981 2967377029318307243112023)
            ·
              refine ⟨4451065543977460864668035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967377029318307243112023 4451065543977460864668035)
              ·
                refine ⟨6676598315966191297002053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4451065543977460864668035 6676598315966191297002053)
                ·
                  refine ⟨1251862184243660868187885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6676598315966191297002053 1251862184243660868187885)
                  ·
                    refine ⟨469448319091372825570457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251862184243660868187885 469448319091372825570457)
                    ·
                      rfl

theorem cell22_1371371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 3].length) (baseStart_1371371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371371 prefixEnd_1371371 := by exact prefixLift 1371371
  have htrace : WordTrace (prefixWord ++ tailWord_1371371) baseStart_1371371 baseEnd_1371371 := by
    simpa [prefixWord, tailWord_1371371, baseEnd_1371371] using wordTrace_append hprefix tailTrace_1371371
  have hstable : (prefixWord ++ tailWord_1371371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371371).length < 2 ^ (prefixWord ++ tailWord_1371371).sum := by decide
  have hdescent : baseEnd_1371371 < baseStart_1371371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371373 : List Nat := [1, 5, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1371373 : Nat := 118140960795 + 1371373 * 2 ^ 59
def prefixEnd_1371373 : Nat := 4983230072969 + 3 ^ 40 * 1371373 * 2
def baseEnd_1371373 : Nat := 156483001244081829006817

theorem tailTrace_1371373 : CollatzResearch.WordTrace tailWord_1371373 prefixEnd_1371373 156483001244081829006817 := by
  unfold tailWord_1371373
  simp only [CollatzResearch.WordTrace]
  refine ⟨50018082460757307706950773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33345388307171538471300515 50018082460757307706950773)
  ·
    refine ⟨4689195230695997597526635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50018082460757307706950773 4689195230695997597526635)
    ·
      refine ⟨7033792846043996396289953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689195230695997597526635 7033792846043996396289953)
      ·
        refine ⟨5275344634532997297217465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7033792846043996396289953 5275344634532997297217465)
        ·
          refine ⟨3956508475899747972913099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5275344634532997297217465 3956508475899747972913099)
          ·
            refine ⟨5934762713849621959369649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956508475899747972913099 5934762713849621959369649)
            ·
              refine ⟨4451072035387216469527237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5934762713849621959369649 4451072035387216469527237)
              ·
                refine ⟨834576006635103088036357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4451072035387216469527237 834576006635103088036357)
                ·
                  refine ⟨156483001244081829006817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834576006635103088036357 156483001244081829006817)
                  ·
                    rfl

theorem cell22_1371373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1371373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371373 prefixEnd_1371373 := by exact prefixLift 1371373
  have htrace : WordTrace (prefixWord ++ tailWord_1371373) baseStart_1371373 baseEnd_1371373 := by
    simpa [prefixWord, tailWord_1371373, baseEnd_1371373] using wordTrace_append hprefix tailTrace_1371373
  have hstable : (prefixWord ++ tailWord_1371373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371373).length < 2 ^ (prefixWord ++ tailWord_1371373).sum := by decide
  have hdescent : baseEnd_1371373 < baseStart_1371373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371388 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_1371388 : Nat := 118140960795 + 1371388 * 2 ^ 59
def prefixEnd_1371388 : Nat := 4983230072969 + 3 ^ 40 * 1371388 * 2
def baseEnd_1371388 : Nat := 469454138538790447895405

theorem tailTrace_1371388 : CollatzResearch.WordTrace tailWord_1371388 prefixEnd_1371388 469454138538790447895405 := by
  unfold tailWord_1371388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25009314777851482634373409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33345753037135310179164545 25009314777851482634373409)
  ·
    refine ⟨18756986083388611975780057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25009314777851482634373409 18756986083388611975780057)
    ·
      refine ⟨14067739562541458981835043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18756986083388611975780057 14067739562541458981835043)
      ·
        refine ⟨21101609343812188472752565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14067739562541458981835043 21101609343812188472752565)
        ·
          refine ⟨1978275875982392669320553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21101609343812188472752565 1978275875982392669320553)
          ·
            refine ⟨1483706906986794501990415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1978275875982392669320553 1483706906986794501990415)
            ·
              refine ⟨2225560360480191752985623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483706906986794501990415 2225560360480191752985623)
              ·
                refine ⟨3338340540720287629478435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2225560360480191752985623 3338340540720287629478435)
                ·
                  refine ⟨5007510811080431444217653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338340540720287629478435 5007510811080431444217653)
                  ·
                    refine ⟨469454138538790447895405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5007510811080431444217653 469454138538790447895405)
                    ·
                      rfl

theorem cell22_1371388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_1371388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371388 prefixEnd_1371388 := by exact prefixLift 1371388
  have htrace : WordTrace (prefixWord ++ tailWord_1371388) baseStart_1371388 baseEnd_1371388 := by
    simpa [prefixWord, tailWord_1371388, baseEnd_1371388] using wordTrace_append hprefix tailTrace_1371388
  have hstable : (prefixWord ++ tailWord_1371388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371388).length < 2 ^ (prefixWord ++ tailWord_1371388).sum := by decide
  have hdescent : baseEnd_1371388 < baseStart_1371388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371540 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1371540 : Nat := 118140960795 + 1371540 * 2 ^ 59
def prefixEnd_1371540 : Nat := 4983230072969 + 3 ^ 40 * 1371540 * 2
def baseEnd_1371540 : Nat := 469506171245112718094939

theorem tailTrace_1371540 : CollatzResearch.WordTrace tailWord_1371540 prefixEnd_1371540 469506171245112718094939 := by
  unfold tailWord_1371540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25012086725576147614140037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33349448967434863485520049 25012086725576147614140037)
  ·
    refine ⟨4689766261045527677651257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25012086725576147614140037 4689766261045527677651257)
    ·
      refine ⟨3517324695784145758238443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4689766261045527677651257 3517324695784145758238443)
      ·
        refine ⟨5275987043676218637357665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517324695784145758238443 5275987043676218637357665)
        ·
          refine ⟨3956990282757163978018249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5275987043676218637357665 3956990282757163978018249)
          ·
            refine ⟨2967742712067872983513687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3956990282757163978018249 2967742712067872983513687)
            ·
              refine ⟨4451614068101809475270531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967742712067872983513687 4451614068101809475270531)
              ·
                refine ⟨6677421102152714212905797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4451614068101809475270531 6677421102152714212905797)
                ·
                  refine ⟨1252016456653633914919837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6677421102152714212905797 1252016456653633914919837)
                  ·
                    refine ⟨469506171245112718094939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252016456653633914919837 469506171245112718094939)
                    ·
                      rfl

theorem cell22_1371540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1371540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371540 prefixEnd_1371540 := by exact prefixLift 1371540
  have htrace : WordTrace (prefixWord ++ tailWord_1371540) baseStart_1371540 baseEnd_1371540 := by
    simpa [prefixWord, tailWord_1371540, baseEnd_1371540] using wordTrace_append hprefix tailTrace_1371540
  have hstable : (prefixWord ++ tailWord_1371540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371540).length < 2 ^ (prefixWord ++ tailWord_1371540).sum := by decide
  have hdescent : baseEnd_1371540 < baseStart_1371540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371581 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 9]
def baseStart_1371581 : Nat := 118140960795 + 1371581 * 2 ^ 59
def prefixEnd_1371581 : Nat := 4983230072969 + 3 ^ 40 * 1371581 * 2
def baseEnd_1371581 : Nat := 156506735461000759273271

theorem tailTrace_1371581 : CollatzResearch.WordTrace tailWord_1371581 prefixEnd_1371581 156506735461000759273271 := by
  unfold tailWord_1371581
  simp only [CollatzResearch.WordTrace]
  refine ⟨50025668844003759230522597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33350445896002506153681731 50025668844003759230522597)
  ·
    refine ⟨9379812908250704855722987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50025668844003759230522597 9379812908250704855722987)
    ·
      refine ⟨14069719362376057283584481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9379812908250704855722987 14069719362376057283584481)
      ·
        refine ⟨10552289521782042962688361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14069719362376057283584481 10552289521782042962688361)
        ·
          refine ⟨7914217141336532222016271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10552289521782042962688361 7914217141336532222016271)
          ·
            refine ⟨11871325712004798333024407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914217141336532222016271 11871325712004798333024407)
            ·
              refine ⟨17806988568007197499536611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871325712004798333024407 17806988568007197499536611)
              ·
                refine ⟨26710482852010796249304917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17806988568007197499536611 26710482852010796249304917)
                ·
                  refine ⟨156506735461000759273271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26710482852010796249304917 156506735461000759273271)
                  ·
                    rfl

theorem cell22_1371581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_1371581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371581 prefixEnd_1371581 := by exact prefixLift 1371581
  have htrace : WordTrace (prefixWord ++ tailWord_1371581) baseStart_1371581 baseEnd_1371581 := by
    simpa [prefixWord, tailWord_1371581, baseEnd_1371581] using wordTrace_append hprefix tailTrace_1371581
  have hstable : (prefixWord ++ tailWord_1371581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371581).length < 2 ^ (prefixWord ++ tailWord_1371581).sum := by decide
  have hdescent : baseEnd_1371581 < baseStart_1371581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371611 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 9, 4]
def baseStart_1371611 : Nat := 118140960795 + 1371611 * 2 ^ 59
def prefixEnd_1371611 : Nat := 4983230072969 + 3 ^ 40 * 1371611 * 2
def baseEnd_1371611 : Nat := 469530475996092199569721

theorem tailTrace_1371611 : CollatzResearch.WordTrace tailWord_1371611 prefixEnd_1371611 469530475996092199569721 := by
  unfold tailWord_1371611
  simp only [CollatzResearch.WordTrace]
  refine ⟨50026763033895074354114687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33351175355930049569409791 50026763033895074354114687)
  ·
    refine ⟨75040144550842611531172031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50026763033895074354114687 75040144550842611531172031)
    ·
      refine ⟨112560216826263917296758047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75040144550842611531172031 112560216826263917296758047)
      ·
        refine ⟨168840325239395875945137071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112560216826263917296758047 168840325239395875945137071)
        ·
          refine ⟨253260487859093813917705607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168840325239395875945137071 253260487859093813917705607)
          ·
            refine ⟨379890731788640720876558411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253260487859093813917705607 379890731788640720876558411)
            ·
              refine ⟨569836097682961081314837617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379890731788640720876558411 569836097682961081314837617)
              ·
                refine ⟨427377073262220810986128213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569836097682961081314837617 427377073262220810986128213)
                ·
                  refine ⟨2504162538645825064371845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 427377073262220810986128213 2504162538645825064371845)
                  ·
                    refine ⟨469530475996092199569721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504162538645825064371845 469530475996092199569721)
                    ·
                      rfl

theorem cell22_1371611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_1371611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371611 prefixEnd_1371611 := by exact prefixLift 1371611
  have htrace : WordTrace (prefixWord ++ tailWord_1371611) baseStart_1371611 baseEnd_1371611 := by
    simpa [prefixWord, tailWord_1371611, baseEnd_1371611] using wordTrace_append hprefix tailTrace_1371611
  have hstable : (prefixWord ++ tailWord_1371611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371611).length < 2 ^ (prefixWord ++ tailWord_1371611).sum := by decide
  have hdescent : baseEnd_1371611 < baseStart_1371611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371628 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_1371628 : Nat := 118140960795 + 1371628 * 2 ^ 59
def prefixEnd_1371628 : Nat := 4983230072969 + 3 ^ 40 * 1371628 * 2
def baseEnd_1371628 : Nat := 469536295443509821894669

theorem tailTrace_1371628 : CollatzResearch.WordTrace tailWord_1371628 prefixEnd_1371628 469536295443509821894669 := by
  unfold tailWord_1371628
  simp only [CollatzResearch.WordTrace]
  refine ⟨25013691537416743128741769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33351588716555657504989025 25013691537416743128741769)
  ·
    refine ⟨18760268653062557346556327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25013691537416743128741769 18760268653062557346556327)
    ·
      refine ⟨28140402979593836019834491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18760268653062557346556327 28140402979593836019834491)
      ·
        refine ⟨42210604469390754029751737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28140402979593836019834491 42210604469390754029751737)
        ·
          refine ⟨31657953352043065522313803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42210604469390754029751737 31657953352043065522313803)
          ·
            refine ⟨47486930028064598283470705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31657953352043065522313803 47486930028064598283470705)
            ·
              refine ⟨35615197521048448712603029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47486930028064598283470705 35615197521048448712603029)
              ·
                refine ⟨1669462383799146033403267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35615197521048448712603029 1669462383799146033403267)
                ·
                  refine ⟨2504193575698719050104901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669462383799146033403267 2504193575698719050104901)
                  ·
                    refine ⟨469536295443509821894669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504193575698719050104901 469536295443509821894669)
                    ·
                      rfl

theorem cell22_1371628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_1371628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371628 prefixEnd_1371628 := by exact prefixLift 1371628
  have htrace : WordTrace (prefixWord ++ tailWord_1371628) baseStart_1371628 baseEnd_1371628 := by
    simpa [prefixWord, tailWord_1371628, baseEnd_1371628] using wordTrace_append hprefix tailTrace_1371628
  have hstable : (prefixWord ++ tailWord_1371628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371628).length < 2 ^ (prefixWord ++ tailWord_1371628).sum := by decide
  have hdescent : baseEnd_1371628 < baseStart_1371628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371709 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_1371709 : Nat := 118140960795 + 1371709 * 2 ^ 59
def prefixEnd_1371709 : Nat := 4983230072969 + 3 ^ 40 * 1371709 * 2
def baseEnd_1371709 : Nat := 469564023398852610619421

theorem tailTrace_1371709 : CollatzResearch.WordTrace tailWord_1371709 prefixEnd_1371709 469564023398852610619421 := by
  unfold tailWord_1371709
  simp only [CollatzResearch.WordTrace]
  refine ⟨50030337387540037091182181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33353558258360024727454787 50030337387540037091182181)
  ·
    refine ⟨9380688260163756954596659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50030337387540037091182181 9380688260163756954596659)
    ·
      refine ⟨14071032390245635431894989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9380688260163756954596659 14071032390245635431894989)
      ·
        refine ⟨5276637146342113286960621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14071032390245635431894989 5276637146342113286960621)
        ·
          refine ⟨1978738929878292482610233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5276637146342113286960621 1978738929878292482610233)
          ·
            refine ⟨1484054197408719361957675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1978738929878292482610233 1484054197408719361957675)
            ·
              refine ⟨2226081296113079042936513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484054197408719361957675 2226081296113079042936513)
              ·
                refine ⟨1669560972084809282202385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226081296113079042936513 1669560972084809282202385)
                ·
                  refine ⟨1252170729063606961651789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669560972084809282202385 1252170729063606961651789)
                  ·
                    refine ⟨469564023398852610619421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252170729063606961651789 469564023398852610619421)
                    ·
                      rfl

theorem cell22_1371709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_1371709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371709 prefixEnd_1371709 := by exact prefixLift 1371709
  have htrace : WordTrace (prefixWord ++ tailWord_1371709) baseStart_1371709 baseEnd_1371709 := by
    simpa [prefixWord, tailWord_1371709, baseEnd_1371709] using wordTrace_append hprefix tailTrace_1371709
  have hstable : (prefixWord ++ tailWord_1371709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371709).length < 2 ^ (prefixWord ++ tailWord_1371709).sum := by decide
  have hdescent : baseEnd_1371709 < baseStart_1371709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371754 : List Nat := [3, 1, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_1371754 : Nat := 118140960795 + 1371754 * 2 ^ 59
def prefixEnd_1371754 : Nat := 4983230072969 + 3 ^ 40 * 1371754 * 2
def baseEnd_1371754 : Nat := 469579427818487493244283

theorem tailTrace_1371754 : CollatzResearch.WordTrace tailWord_1371754 prefixEnd_1371754 469579427818487493244283 := by
  unfold tailWord_1371754
  simp only [CollatzResearch.WordTrace]
  refine ⟨12507994668094252444142579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33354652448251339851046877 12507994668094252444142579)
  ·
    refine ⟨18761992002141378666213869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12507994668094252444142579 18761992002141378666213869)
    ·
      refine ⟨7035747000803016999830201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18761992002141378666213869 7035747000803016999830201)
      ·
        refine ⟨5276810250602262749872651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7035747000803016999830201 5276810250602262749872651)
        ·
          refine ⟨7915215375903394124808977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276810250602262749872651 7915215375903394124808977)
          ·
            refine ⟨5936411531927545593606733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7915215375903394124808977 5936411531927545593606733)
            ·
              refine ⟨2226154324472829597602525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5936411531927545593606733 2226154324472829597602525)
              ·
                refine ⟨834807871677311099100947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2226154324472829597602525 834807871677311099100947)
                ·
                  refine ⟨1252211807515966648651421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834807871677311099100947 1252211807515966648651421)
                  ·
                    refine ⟨469579427818487493244283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252211807515966648651421 469579427818487493244283)
                    ·
                      rfl

theorem cell22_1371754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_1371754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371754 prefixEnd_1371754 := by exact prefixLift 1371754
  have htrace : WordTrace (prefixWord ++ tailWord_1371754) baseStart_1371754 baseEnd_1371754 := by
    simpa [prefixWord, tailWord_1371754, baseEnd_1371754] using wordTrace_append hprefix tailTrace_1371754
  have hstable : (prefixWord ++ tailWord_1371754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371754).length < 2 ^ (prefixWord ++ tailWord_1371754).sum := by decide
  have hdescent : baseEnd_1371754 < baseStart_1371754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371827 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 2, 3]
def baseStart_1371827 : Nat := 118140960795 + 1371827 * 2 ^ 59
def prefixEnd_1371827 : Nat := 4983230072969 + 3 ^ 40 * 1371827 * 2
def baseEnd_1371827 : Nat := 469604417210339636169059

theorem tailTrace_1371827 : CollatzResearch.WordTrace tailWord_1371827 prefixEnd_1371827 469604417210339636169059 := by
  unfold tailWord_1371827
  simp only [CollatzResearch.WordTrace]
  refine ⟨50034641201112543243977735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33356427467408362162651823 50034641201112543243977735)
  ·
    refine ⟨75051961801668814865966603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50034641201112543243977735 75051961801668814865966603)
    ·
      refine ⟨112577942702503222298949905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75051961801668814865966603 112577942702503222298949905)
      ·
        refine ⟨84433457026877416724212429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112577942702503222298949905 84433457026877416724212429)
        ·
          refine ⟨31662546385079031271579661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84433457026877416724212429 31662546385079031271579661)
          ·
            refine ⟨11873454894404636726842373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31662546385079031271579661 11873454894404636726842373)
            ·
              refine ⟨2226272792700869386282945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11873454894404636726842373 2226272792700869386282945)
              ·
                refine ⟨1669704594525652039712209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226272792700869386282945 1669704594525652039712209)
                ·
                  refine ⟨1252278445894239029784157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669704594525652039712209 1252278445894239029784157)
                  ·
                    refine ⟨469604417210339636169059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252278445894239029784157 469604417210339636169059)
                    ·
                      rfl

theorem cell22_1371827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 3].length) (baseStart_1371827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371827 prefixEnd_1371827 := by exact prefixLift 1371827
  have htrace : WordTrace (prefixWord ++ tailWord_1371827) baseStart_1371827 baseEnd_1371827 := by
    simpa [prefixWord, tailWord_1371827, baseEnd_1371827] using wordTrace_append hprefix tailTrace_1371827
  have hstable : (prefixWord ++ tailWord_1371827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371827).length < 2 ^ (prefixWord ++ tailWord_1371827).sum := by decide
  have hdescent : baseEnd_1371827 < baseStart_1371827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371829 : List Nat := [1, 3, 3, 3, 2, 1, 1, 4, 4]
def baseStart_1371829 : Nat := 118140960795 + 1371829 * 2 ^ 59
def prefixEnd_1371829 : Nat := 4983230072969 + 3 ^ 40 * 1371829 * 2
def baseEnd_1371829 : Nat := 156535033950404099206351

theorem tailTrace_1371829 : CollatzResearch.WordTrace tailWord_1371829 prefixEnd_1371829 156535033950404099206351 := by
  unfold tailWord_1371829
  simp only [CollatzResearch.WordTrace]
  refine ⟨50034714147105297585550541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33356476098070198390367027 50034714147105297585550541)
  ·
    refine ⟨18763017805164486594581453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50034714147105297585550541 18763017805164486594581453)
    ·
      refine ⟨7036131676936682472968045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18763017805164486594581453 7036131676936682472968045)
      ·
        refine ⟨2638549378851255927363017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7036131676936682472968045 2638549378851255927363017)
        ·
          refine ⟨1978912034138441945522263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2638549378851255927363017 1978912034138441945522263)
          ·
            refine ⟨2968368051207662918283395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978912034138441945522263 2968368051207662918283395)
            ·
              refine ⟨4452552076811494377425093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968368051207662918283395 4452552076811494377425093)
              ·
                refine ⟨834853514402155195767205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4452552076811494377425093 834853514402155195767205)
                ·
                  refine ⟨156535033950404099206351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 834853514402155195767205 156535033950404099206351)
                  ·
                    rfl

theorem cell22_1371829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_1371829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371829 prefixEnd_1371829 := by exact prefixLift 1371829
  have htrace : WordTrace (prefixWord ++ tailWord_1371829) baseStart_1371829 baseEnd_1371829 := by
    simpa [prefixWord, tailWord_1371829, baseEnd_1371829] using wordTrace_append hprefix tailTrace_1371829
  have hstable : (prefixWord ++ tailWord_1371829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371829).length < 2 ^ (prefixWord ++ tailWord_1371829).sum := by decide
  have hdescent : baseEnd_1371829 < baseStart_1371829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371889 : List Nat := [1, 2, 2, 2, 2, 3, 2, 4, 1, 3]
def baseStart_1371889 : Nat := 118140960795 + 1371889 * 2 ^ 59
def prefixEnd_1371889 : Nat := 4983230072969 + 3 ^ 40 * 1371889 * 2
def baseEnd_1371889 : Nat := 469625641077392141118869

theorem tailTrace_1371889 : CollatzResearch.WordTrace tailWord_1371889 prefixEnd_1371889 469625641077392141118869 := by
  unfold tailWord_1371889
  simp only [CollatzResearch.WordTrace]
  refine ⟨50036902526887927832734721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33357935017925285221823147 50036902526887927832734721)
  ·
    refine ⟨37527676895165945874551041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50036902526887927832734721 37527676895165945874551041)
    ·
      refine ⟨28145757671374459405913281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37527676895165945874551041 28145757671374459405913281)
      ·
        refine ⟨21109318253530844554434961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28145757671374459405913281 21109318253530844554434961)
        ·
          refine ⟨15831988690148133415826221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21109318253530844554434961 15831988690148133415826221)
          ·
            refine ⟨5936995758805550030934833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15831988690148133415826221 5936995758805550030934833)
            ·
              refine ⟨4452746819104162523201125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5936995758805550030934833 4452746819104162523201125)
              ·
                refine ⟨834890028582030473100211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4452746819104162523201125 834890028582030473100211)
                ·
                  refine ⟨1252335042873045709650317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834890028582030473100211 1252335042873045709650317)
                  ·
                    refine ⟨469625641077392141118869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252335042873045709650317 469625641077392141118869)
                    ·
                      rfl

theorem cell22_1371889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_1371889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371889 prefixEnd_1371889 := by exact prefixLift 1371889
  have htrace : WordTrace (prefixWord ++ tailWord_1371889) baseStart_1371889 baseEnd_1371889 := by
    simpa [prefixWord, tailWord_1371889, baseEnd_1371889] using wordTrace_append hprefix tailTrace_1371889
  have hstable : (prefixWord ++ tailWord_1371889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371889).length < 2 ^ (prefixWord ++ tailWord_1371889).sum := by decide
  have hdescent : baseEnd_1371889 < baseStart_1371889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371900 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1371900 : Nat := 118140960795 + 1371900 * 2 ^ 59
def prefixEnd_1371900 : Nat := 4983230072969 + 3 ^ 40 * 1371900 * 2
def baseEnd_1371900 : Nat := 469629406602191779093835

theorem tailTrace_1371900 : CollatzResearch.WordTrace tailWord_1371900 prefixEnd_1371900 469629406602191779093835 := by
  unfold tailWord_1371900
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018651864924038355692577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33358202486565384474256769 25018651864924038355692577)
  ·
    refine ⟨18763988898693028766769433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25018651864924038355692577 18763988898693028766769433)
    ·
      refine ⟨14072991674019771575077075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18763988898693028766769433 14072991674019771575077075)
      ·
        refine ⟨21109487511029657362615613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072991674019771575077075 21109487511029657362615613)
        ·
          refine ⟨7916057816636121510980855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21109487511029657362615613 7916057816636121510980855)
          ·
            refine ⟨11874086724954182266471283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7916057816636121510980855 11874086724954182266471283)
            ·
              refine ⟨17811130087431273399706925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11874086724954182266471283 17811130087431273399706925)
              ·
                refine ⟨6679173782786727524890097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17811130087431273399706925 6679173782786727524890097)
                ·
                  refine ⟨5009380337090045643667573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6679173782786727524890097 5009380337090045643667573)
                  ·
                    refine ⟨469629406602191779093835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5009380337090045643667573 469629406602191779093835)
                    ·
                      rfl

theorem cell22_1371900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1371900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371900 prefixEnd_1371900 := by exact prefixLift 1371900
  have htrace : WordTrace (prefixWord ++ tailWord_1371900) baseStart_1371900 baseEnd_1371900 := by
    simpa [prefixWord, tailWord_1371900, baseEnd_1371900] using wordTrace_append hprefix tailTrace_1371900
  have hstable : (prefixWord ++ tailWord_1371900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371900).length < 2 ^ (prefixWord ++ tailWord_1371900).sum := by decide
  have hdescent : baseEnd_1371900 < baseStart_1371900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371915 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 3, 4]
def baseStart_1371915 : Nat := 118140960795 + 1371915 * 2 ^ 59
def prefixEnd_1371915 : Nat := 4983230072969 + 3 ^ 40 * 1371915 * 2
def baseEnd_1371915 : Nat := 469634541408736739968789

theorem tailTrace_1371915 : CollatzResearch.WordTrace tailWord_1371915 prefixEnd_1371915 469634541408736739968789 := by
  unfold tailWord_1371915
  simp only [CollatzResearch.WordTrace]
  refine ⟨50037850824793734273181199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33358567216529156182120799 50037850824793734273181199)
  ·
    refine ⟨75056776237190601409771799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50037850824793734273181199 75056776237190601409771799)
    ·
      refine ⟨112585164355785902114657699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75056776237190601409771799 112585164355785902114657699)
      ·
        refine ⟨168877746533678853171986549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112585164355785902114657699 168877746533678853171986549)
        ·
          refine ⟨15832288737532392484873739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168877746533678853171986549 15832288737532392484873739)
          ·
            refine ⟨23748433106298588727310609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15832288737532392484873739 23748433106298588727310609)
            ·
              refine ⟨17811324829723941545482957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23748433106298588727310609 17811324829723941545482957)
              ·
                refine ⟨6679246811146478079556109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17811324829723941545482957 6679246811146478079556109)
                ·
                  refine ⟨2504717554179929279833541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6679246811146478079556109 2504717554179929279833541)
                  ·
                    refine ⟨469634541408736739968789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504717554179929279833541 469634541408736739968789)
                    ·
                      rfl

theorem cell22_1371915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_1371915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371915 prefixEnd_1371915 := by exact prefixLift 1371915
  have htrace : WordTrace (prefixWord ++ tailWord_1371915) baseStart_1371915 baseEnd_1371915 := by
    simpa [prefixWord, tailWord_1371915, baseEnd_1371915] using wordTrace_append hprefix tailTrace_1371915
  have hstable : (prefixWord ++ tailWord_1371915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371915).length < 2 ^ (prefixWord ++ tailWord_1371915).sum := by decide
  have hdescent : baseEnd_1371915 < baseStart_1371915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371932 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1371932 : Nat := 118140960795 + 1371932 * 2 ^ 59
def prefixEnd_1371932 : Nat := 4983230072969 + 3 ^ 40 * 1371932 * 2
def baseEnd_1371932 : Nat := 469640360856154362293737

theorem tailTrace_1371932 : CollatzResearch.WordTrace tailWord_1371932 prefixEnd_1371932 469640360856154362293737 := by
  unfold tailWord_1371932
  simp only [CollatzResearch.WordTrace]
  refine ⟨25019235432866073088275025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33358980577154764117700033 25019235432866073088275025)
  ·
    refine ⟨18764426574649554816206269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25019235432866073088275025 18764426574649554816206269)
    ·
      refine ⟨7036659965493583056077351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18764426574649554816206269 7036659965493583056077351)
      ·
        refine ⟨10554989948240374584116027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7036659965493583056077351 10554989948240374584116027)
        ·
          refine ⟨15832484922360561876174041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10554989948240374584116027 15832484922360561876174041)
          ·
            refine ⟨11874363691770421407130531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15832484922360561876174041 11874363691770421407130531)
            ·
              refine ⟨17811545537655632110695797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11874363691770421407130531 17811545537655632110695797)
              ·
                refine ⟨1669832394155215510377731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17811545537655632110695797 1669832394155215510377731)
                ·
                  refine ⟨2504748591232823265566597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669832394155215510377731 2504748591232823265566597)
                  ·
                    refine ⟨469640360856154362293737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504748591232823265566597 469640360856154362293737)
                    ·
                      rfl

theorem cell22_1371932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1371932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371932 prefixEnd_1371932 := by exact prefixLift 1371932
  have htrace : WordTrace (prefixWord ++ tailWord_1371932) baseStart_1371932 baseEnd_1371932 := by
    simpa [prefixWord, tailWord_1371932, baseEnd_1371932] using wordTrace_append hprefix tailTrace_1371932
  have hstable : (prefixWord ++ tailWord_1371932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371932).length < 2 ^ (prefixWord ++ tailWord_1371932).sum := by decide
  have hdescent : baseEnd_1371932 < baseStart_1371932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371966 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1371966 : Nat := 118140960795 + 1371966 * 2 ^ 59
def prefixEnd_1371966 : Nat := 4983230072969 + 3 ^ 40 * 1371966 * 2
def baseEnd_1371966 : Nat := 469651999750989606943633

theorem tailTrace_1371966 : CollatzResearch.WordTrace tailWord_1371966 prefixEnd_1371966 469651999750989606943633 := by
  unfold tailWord_1371966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254963868451121247910969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33359807298405979988858501 6254963868451121247910969)
  ·
    refine ⟨4691222901338340935933227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6254963868451121247910969 4691222901338340935933227)
    ·
      refine ⟨7036834352007511403899841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4691222901338340935933227 7036834352007511403899841)
      ·
        refine ⟨5277625764005633552924881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7036834352007511403899841 5277625764005633552924881)
        ·
          refine ⟨3958219323004225164693661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5277625764005633552924881 3958219323004225164693661)
          ·
            refine ⟨1484332246126584436760123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3958219323004225164693661 1484332246126584436760123)
            ·
              refine ⟨2226498369189876655140185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484332246126584436760123 2226498369189876655140185)
              ·
                refine ⟨1669873776892407491355139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226498369189876655140185 1669873776892407491355139)
                ·
                  refine ⟨2504810665338611237032709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669873776892407491355139 2504810665338611237032709)
                  ·
                    refine ⟨469651999750989606943633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504810665338611237032709 469651999750989606943633)
                    ·
                      rfl

theorem cell22_1371966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1371966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371966 prefixEnd_1371966 := by exact prefixLift 1371966
  have htrace : WordTrace (prefixWord ++ tailWord_1371966) baseStart_1371966 baseEnd_1371966 := by
    simpa [prefixWord, tailWord_1371966, baseEnd_1371966] using wordTrace_append hprefix tailTrace_1371966
  have hstable : (prefixWord ++ tailWord_1371966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371966).length < 2 ^ (prefixWord ++ tailWord_1371966).sum := by decide
  have hdescent : baseEnd_1371966 < baseStart_1371966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371975 : List Nat := [1, 1, 4, 1, 2, 1, 4, 8]
def baseStart_1371975 : Nat := 118140960795 + 1371975 * 2 ^ 59
def prefixEnd_1371975 : Nat := 4983230072969 + 3 ^ 40 * 1371975 * 2
def baseEnd_1371975 : Nat := 52183897848324064829845

theorem tailTrace_1371975 : CollatzResearch.WordTrace tailWord_1371975 prefixEnd_1371975 52183897848324064829845 := by
  unfold tailWord_1371975
  simp only [CollatzResearch.WordTrace]
  refine ⟨50040039204576364520365379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33360026136384243013576919 50040039204576364520365379)
  ·
    refine ⟨75060058806864546780548069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50040039204576364520365379 75060058806864546780548069)
    ·
      refine ⟨14073761026287102521352763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75060058806864546780548069 14073761026287102521352763)
      ·
        refine ⟨21110641539430653782029145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14073761026287102521352763 21110641539430653782029145)
        ·
          refine ⟨15832981154572990336521859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21110641539430653782029145 15832981154572990336521859)
          ·
            refine ⟨23749471731859485504782789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15832981154572990336521859 23749471731859485504782789)
            ·
              refine ⟨4453025949723653532146773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23749471731859485504782789 4453025949723653532146773)
              ·
                refine ⟨52183897848324064829845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4453025949723653532146773 52183897848324064829845)
                ·
                  rfl

theorem cell22_1371975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 8].length) (baseStart_1371975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371975 prefixEnd_1371975 := by exact prefixLift 1371975
  have htrace : WordTrace (prefixWord ++ tailWord_1371975) baseStart_1371975 baseEnd_1371975 := by
    simpa [prefixWord, tailWord_1371975, baseEnd_1371975] using wordTrace_append hprefix tailTrace_1371975
  have hstable : (prefixWord ++ tailWord_1371975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371975).length < 2 ^ (prefixWord ++ tailWord_1371975).sum := by decide
  have hdescent : baseEnd_1371975 < baseStart_1371975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371977 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_1371977 : Nat := 118140960795 + 1371977 * 2 ^ 59
def prefixEnd_1371977 : Nat := 4983230072969 + 3 ^ 40 * 1371977 * 2
def baseEnd_1371977 : Nat := 469655765275789244918599

theorem tailTrace_1371977 : CollatzResearch.WordTrace tailWord_1371977 prefixEnd_1371977 469655765275789244918599 := by
  unfold tailWord_1371977
  simp only [CollatzResearch.WordTrace]
  refine ⟨50040112150569118861938185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33360074767046079241292123 50040112150569118861938185)
  ·
    refine ⟨37530084112926839146453639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50040112150569118861938185 37530084112926839146453639)
    ·
      refine ⟨56295126169390258719680459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37530084112926839146453639 56295126169390258719680459)
      ·
        refine ⟨84442689254085388079520689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56295126169390258719680459 84442689254085388079520689)
        ·
          refine ⟨63332016940564041059640517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84442689254085388079520689 63332016940564041059640517)
          ·
            refine ⟨11874753176355757698682597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63332016940564041059640517 11874753176355757698682597)
            ·
              refine ⟨2226516220566704568502987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11874753176355757698682597 2226516220566704568502987)
              ·
                refine ⟨3339774330850056852754481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226516220566704568502987 3339774330850056852754481)
                ·
                  refine ⟨2504830748137542639565861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3339774330850056852754481 2504830748137542639565861)
                  ·
                    refine ⟨469655765275789244918599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2504830748137542639565861 469655765275789244918599)
                    ·
                      rfl

theorem cell22_1371977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_1371977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1371977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1371977 prefixEnd_1371977 := by exact prefixLift 1371977
  have htrace : WordTrace (prefixWord ++ tailWord_1371977) baseStart_1371977 baseEnd_1371977 := by
    simpa [prefixWord, tailWord_1371977, baseEnd_1371977] using wordTrace_append hprefix tailTrace_1371977
  have hstable : (prefixWord ++ tailWord_1371977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371977).length < 2 ^ (prefixWord ++ tailWord_1371977).sum := by decide
  have hdescent : baseEnd_1371977 < baseStart_1371977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372041 : List Nat := [1, 2, 1, 1, 5, 1, 4, 3, 1, 3]
def baseStart_1372041 : Nat := 118140960795 + 1372041 * 2 ^ 59
def prefixEnd_1372041 : Nat := 4983230072969 + 3 ^ 40 * 1372041 * 2
def baseEnd_1372041 : Nat := 469677673783714411318403

theorem tailTrace_1372041 : CollatzResearch.WordTrace tailWord_1372041 prefixEnd_1372041 469677673783714411318403 := by
  unfold tailWord_1372041
  simp only [CollatzResearch.WordTrace]
  refine ⟨50042446422337257792267977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33361630948224838528178651 50042446422337257792267977)
  ·
    refine ⟨37531834816752943344200983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50042446422337257792267977 37531834816752943344200983)
    ·
      refine ⟨56297752225129415016301475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37531834816752943344200983 56297752225129415016301475)
      ·
        refine ⟨84446628337694122524452213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56297752225129415016301475 84446628337694122524452213)
        ·
          refine ⟨7916871406658823986667395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84446628337694122524452213 7916871406658823986667395)
          ·
            refine ⟨11875307109988235980001093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7916871406658823986667395 11875307109988235980001093)
            ·
              refine ⟨2226620083122794246250205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11875307109988235980001093 2226620083122794246250205)
              ·
                refine ⟨834982531171047842343827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2226620083122794246250205 834982531171047842343827)
                ·
                  refine ⟨1252473796756571763515741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834982531171047842343827 1252473796756571763515741)
                  ·
                    refine ⟨469677673783714411318403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252473796756571763515741 469677673783714411318403)
                    ·
                      rfl

theorem cell22_1372041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 3].length) (baseStart_1372041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372041 prefixEnd_1372041 := by exact prefixLift 1372041
  have htrace : WordTrace (prefixWord ++ tailWord_1372041) baseStart_1372041 baseEnd_1372041 := by
    simpa [prefixWord, tailWord_1372041, baseEnd_1372041] using wordTrace_append hprefix tailTrace_1372041
  have hstable : (prefixWord ++ tailWord_1372041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372041).length < 2 ^ (prefixWord ++ tailWord_1372041).sum := by decide
  have hdescent : baseEnd_1372041 < baseStart_1372041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372071 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 5]
def baseStart_1372071 : Nat := 118140960795 + 1372071 * 2 ^ 59
def prefixEnd_1372071 : Nat := 4983230072969 + 3 ^ 40 * 1372071 * 2
def baseEnd_1372071 : Nat := 156562647798934777689437

theorem tailTrace_1372071 : CollatzResearch.WordTrace tailWord_1372071 prefixEnd_1372071 156562647798934777689437 := by
  unfold tailWord_1372071
  simp only [CollatzResearch.WordTrace]
  refine ⟨50043540612228572915860067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33362360408152381943906711 50043540612228572915860067)
  ·
    refine ⟨75065310918342859373790101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50043540612228572915860067 75065310918342859373790101)
    ·
      refine ⟨3518686449297321533146411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75065310918342859373790101 3518686449297321533146411)
      ·
        refine ⟨5278029673945982299719617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518686449297321533146411 5278029673945982299719617)
        ·
          refine ⟨3958522255459486724789713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5278029673945982299719617 3958522255459486724789713)
          ·
            refine ⟨2968891691594615043592285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3958522255459486724789713 2968891691594615043592285)
            ·
              refine ⟨1113334384347980641347107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2968891691594615043592285 1113334384347980641347107)
              ·
                refine ⟨1670001576521970962020661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113334384347980641347107 1670001576521970962020661)
                ·
                  refine ⟨156562647798934777689437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1670001576521970962020661 156562647798934777689437)
                  ·
                    rfl

theorem cell22_1372071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 5].length) (baseStart_1372071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372071 prefixEnd_1372071 := by exact prefixLift 1372071
  have htrace : WordTrace (prefixWord ++ tailWord_1372071) baseStart_1372071 baseEnd_1372071 := by
    simpa [prefixWord, tailWord_1372071, baseEnd_1372071] using wordTrace_append hprefix tailTrace_1372071
  have hstable : (prefixWord ++ tailWord_1372071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372071).length < 2 ^ (prefixWord ++ tailWord_1372071).sum := by decide
  have hdescent : baseEnd_1372071 < baseStart_1372071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372092 : List Nat := [2, 2, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_1372092 : Nat := 118140960795 + 1372092 * 2 ^ 59
def prefixEnd_1372092 : Nat := 4983230072969 + 3 ^ 40 * 1372092 * 2
def baseEnd_1372092 : Nat := 469695132125967278293247

theorem tailTrace_1372092 : CollatzResearch.WordTrace tailWord_1372092 prefixEnd_1372092 469695132125967278293247 := by
  unfold tailWord_1372092
  simp only [CollatzResearch.WordTrace]
  refine ⟨25022153272576246751187265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33362871030101662334916353 25022153272576246751187265)
  ·
    refine ⟨18766614954432185063390449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25022153272576246751187265 18766614954432185063390449)
    ·
      refine ⟨14074961215824138797542837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18766614954432185063390449 14074961215824138797542837)
      ·
        refine ⟨1319527613983513012269641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14074961215824138797542837 1319527613983513012269641)
        ·
          refine ⟨989645710487634759202231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319527613983513012269641 989645710487634759202231)
          ·
            refine ⟨1484468565731452138803347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989645710487634759202231 1484468565731452138803347)
            ·
              refine ⟨2226702848597178208205021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484468565731452138803347 2226702848597178208205021)
              ·
                refine ⟨835013568223941828076883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2226702848597178208205021 835013568223941828076883)
                ·
                  refine ⟨1252520352335912742115325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835013568223941828076883 1252520352335912742115325)
                  ·
                    refine ⟨469695132125967278293247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252520352335912742115325 469695132125967278293247)
                    ·
                      rfl

theorem cell22_1372092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_1372092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372092 prefixEnd_1372092 := by exact prefixLift 1372092
  have htrace : WordTrace (prefixWord ++ tailWord_1372092) baseStart_1372092 baseEnd_1372092 := by
    simpa [prefixWord, tailWord_1372092, baseEnd_1372092] using wordTrace_append hprefix tailTrace_1372092
  have hstable : (prefixWord ++ tailWord_1372092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372092).length < 2 ^ (prefixWord ++ tailWord_1372092).sum := by decide
  have hdescent : baseEnd_1372092 < baseStart_1372092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372112 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_1372112 : Nat := 118140960795 + 1372112 * 2 ^ 59
def prefixEnd_1372112 : Nat := 4983230072969 + 3 ^ 40 * 1372112 * 2
def baseEnd_1372112 : Nat := 469701978534693892793185

theorem tailTrace_1372112 : CollatzResearch.WordTrace tailWord_1372112 prefixEnd_1372112 469701978534693892793185 := by
  unfold tailWord_1372112
  simp only [CollatzResearch.WordTrace]
  refine ⟨25022518002540018459051295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33363357336720024612068393 25022518002540018459051295)
  ·
    refine ⟨37533777003810027688576943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25022518002540018459051295 37533777003810027688576943)
    ·
      refine ⟨56300665505715041532865415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37533777003810027688576943 56300665505715041532865415)
      ·
        refine ⟨84450998258572562299298123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56300665505715041532865415 84450998258572562299298123)
        ·
          refine ⟨126676497387858843448947185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84450998258572562299298123 126676497387858843448947185)
          ·
            refine ⟨95007373040894132586710389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126676497387858843448947185 95007373040894132586710389)
            ·
              refine ⟨8906941222583824930004099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95007373040894132586710389 8906941222583824930004099)
              ·
                refine ⟨13360411833875737395006149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8906941222583824930004099 13360411833875737395006149)
                ·
                  refine ⟨2505077218851700761563653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13360411833875737395006149 2505077218851700761563653)
                  ·
                    refine ⟨469701978534693892793185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2505077218851700761563653 469701978534693892793185)
                    ·
                      rfl

theorem cell22_1372112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_1372112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372112 prefixEnd_1372112 := by exact prefixLift 1372112
  have htrace : WordTrace (prefixWord ++ tailWord_1372112) baseStart_1372112 baseEnd_1372112 := by
    simpa [prefixWord, tailWord_1372112, baseEnd_1372112] using wordTrace_append hprefix tailTrace_1372112
  have hstable : (prefixWord ++ tailWord_1372112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372112).length < 2 ^ (prefixWord ++ tailWord_1372112).sum := by decide
  have hdescent : baseEnd_1372112 < baseStart_1372112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372127 : List Nat := [1, 1, 2, 3, 4, 1, 1, 9]
def baseStart_1372127 : Nat := 118140960795 + 1372127 * 2 ^ 59
def prefixEnd_1372127 : Nat := 4983230072969 + 3 ^ 40 * 1372127 * 2
def baseEnd_1372127 : Nat := 52189679260137650407571

theorem tailTrace_1372127 : CollatzResearch.WordTrace tailWord_1372127 prefixEnd_1372127 52189679260137650407571 := by
  unfold tailWord_1372127
  simp only [CollatzResearch.WordTrace]
  refine ⟨50045583100025694479898635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33363722066683796319932423 50045583100025694479898635)
  ·
    refine ⟨75068374650038541719847953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50045583100025694479898635 75068374650038541719847953)
    ·
      refine ⟨56301280987528906289885965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75068374650038541719847953 56301280987528906289885965)
      ·
        refine ⟨21112980370323339858707237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56301280987528906289885965 21112980370323339858707237)
        ·
          refine ⟨3958683819435626223507607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21112980370323339858707237 3958683819435626223507607)
          ·
            refine ⟨5938025729153439335261411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958683819435626223507607 5938025729153439335261411)
            ·
              refine ⟨8907038593730159002892117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938025729153439335261411 8907038593730159002892117)
              ·
                refine ⟨52189679260137650407571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8907038593730159002892117 52189679260137650407571)
                ·
                  rfl

theorem cell22_1372127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 9].length) (baseStart_1372127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372127 prefixEnd_1372127 := by exact prefixLift 1372127
  have htrace : WordTrace (prefixWord ++ tailWord_1372127) baseStart_1372127 baseEnd_1372127 := by
    simpa [prefixWord, tailWord_1372127, baseEnd_1372127] using wordTrace_append hprefix tailTrace_1372127
  have hstable : (prefixWord ++ tailWord_1372127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372127).length < 2 ^ (prefixWord ++ tailWord_1372127).sum := by decide
  have hdescent : baseEnd_1372127 < baseStart_1372127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372131 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 2, 3]
def baseStart_1372131 : Nat := 118140960795 + 1372131 * 2 ^ 59
def prefixEnd_1372131 : Nat := 4983230072969 + 3 ^ 40 * 1372131 * 2
def baseEnd_1372131 : Nat := 469708482622984176568127

theorem tailTrace_1372131 : CollatzResearch.WordTrace tailWord_1372131 prefixEnd_1372131 469708482622984176568127 := by
  unfold tailWord_1372131
  simp only [CollatzResearch.WordTrace]
  refine ⟨50045728992011203163044247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33363819328007468775362831 50045728992011203163044247)
  ·
    refine ⟨75068593488016804744566371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50045728992011203163044247 75068593488016804744566371)
    ·
      refine ⟨112602890232025207116849557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75068593488016804744566371 112602890232025207116849557)
      ·
        refine ⟨5278260479626181583602323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112602890232025207116849557 5278260479626181583602323)
        ·
          refine ⟨7917390719439272375403485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278260479626181583602323 7917390719439272375403485)
          ·
            refine ⟨2969021519789727140776307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7917390719439272375403485 2969021519789727140776307)
            ·
              refine ⟨4453532279684590711164461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969021519789727140776307 4453532279684590711164461)
              ·
                refine ⟨1670074604881721516686673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4453532279684590711164461 1670074604881721516686673)
                ·
                  refine ⟨1252555953661291137515005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1670074604881721516686673 1252555953661291137515005)
                  ·
                    refine ⟨469708482622984176568127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252555953661291137515005 469708482622984176568127)
                    ·
                      rfl

theorem cell22_1372131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 3].length) (baseStart_1372131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372131 prefixEnd_1372131 := by exact prefixLift 1372131
  have htrace : WordTrace (prefixWord ++ tailWord_1372131) baseStart_1372131 baseEnd_1372131 := by
    simpa [prefixWord, tailWord_1372131, baseEnd_1372131] using wordTrace_append hprefix tailTrace_1372131
  have hstable : (prefixWord ++ tailWord_1372131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372131).length < 2 ^ (prefixWord ++ tailWord_1372131).sum := by decide
  have hdescent : baseEnd_1372131 < baseStart_1372131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372176 : List Nat := [2, 1, 1, 1, 1, 1, 1, 10, 1, 3]
def baseStart_1372176 : Nat := 118140960795 + 1372176 * 2 ^ 59
def prefixEnd_1372176 : Nat := 4983230072969 + 3 ^ 40 * 1372176 * 2
def baseEnd_1372176 : Nat := 469723887042619059192989

theorem tailTrace_1372176 : CollatzResearch.WordTrace tailWord_1372176 prefixEnd_1372176 469723887042619059192989 := by
  unfold tailWord_1372176
  simp only [CollatzResearch.WordTrace]
  refine ⟨25023685138424087924216191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33364913517898783898954921 25023685138424087924216191)
  ·
    refine ⟨37535527707636131886324287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25023685138424087924216191 37535527707636131886324287)
    ·
      refine ⟨56303291561454197829486431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37535527707636131886324287 56303291561454197829486431)
      ·
        refine ⟨84454937342181296744229647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56303291561454197829486431 84454937342181296744229647)
        ·
          refine ⟨126682406013271945116344471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84454937342181296744229647 126682406013271945116344471)
          ·
            refine ⟨190023609019907917674516707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126682406013271945116344471 190023609019907917674516707)
            ·
              refine ⟨285035413529861876511775061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190023609019907917674516707 285035413529861876511775061)
              ·
                refine ⟨835064688075767216343091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 285035413529861876511775061 835064688075767216343091)
                ·
                  refine ⟨1252597032113650824514637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835064688075767216343091 1252597032113650824514637)
                  ·
                    refine ⟨469723887042619059192989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252597032113650824514637 469723887042619059192989)
                    ·
                      rfl

theorem cell22_1372176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 3].length) (baseStart_1372176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372176 prefixEnd_1372176 := by exact prefixLift 1372176
  have htrace : WordTrace (prefixWord ++ tailWord_1372176) baseStart_1372176 baseEnd_1372176 := by
    simpa [prefixWord, tailWord_1372176, baseEnd_1372176] using wordTrace_append hprefix tailTrace_1372176
  have hstable : (prefixWord ++ tailWord_1372176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372176).length < 2 ^ (prefixWord ++ tailWord_1372176).sum := by decide
  have hdescent : baseEnd_1372176 < baseStart_1372176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372219 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 1, 4]
def baseStart_1372219 : Nat := 118140960795 + 1372219 * 2 ^ 59
def prefixEnd_1372219 : Nat := 4983230072969 + 3 ^ 40 * 1372219 * 2
def baseEnd_1372219 : Nat := 469738606821381280367857

theorem tailTrace_1372219 : CollatzResearch.WordTrace tailWord_1372219 prefixEnd_1372219 469738606821381280367857 := by
  unfold tailWord_1372219
  simp only [CollatzResearch.WordTrace]
  refine ⟨50048938615692394192247711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33365959077128262794831807 50048938615692394192247711)
  ·
    refine ⟨75073407923538591288371567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50048938615692394192247711 75073407923538591288371567)
    ·
      refine ⟨112610111885307886932557351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75073407923538591288371567 112610111885307886932557351)
      ·
        refine ⟨168915167827961830398836027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112610111885307886932557351 168915167827961830398836027)
        ·
          refine ⟨253372751741942745598254041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168915167827961830398836027 253372751741942745598254041)
          ·
            refine ⟨190029563806457059198690531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253372751741942745598254041 190029563806457059198690531)
            ·
              refine ⟨285044345709685588798035797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190029563806457059198690531 285044345709685588798035797)
              ·
                refine ⟨1670181713142688996863491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 285044345709685588798035797 1670181713142688996863491)
                ·
                  refine ⟨2505272569714033495295237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670181713142688996863491 2505272569714033495295237)
                  ·
                    refine ⟨469738606821381280367857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2505272569714033495295237 469738606821381280367857)
                    ·
                      rfl

theorem cell22_1372219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 4].length) (baseStart_1372219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372219 prefixEnd_1372219 := by exact prefixLift 1372219
  have htrace : WordTrace (prefixWord ++ tailWord_1372219) baseStart_1372219 baseEnd_1372219 := by
    simpa [prefixWord, tailWord_1372219, baseEnd_1372219] using wordTrace_append hprefix tailTrace_1372219
  have hstable : (prefixWord ++ tailWord_1372219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372219).length < 2 ^ (prefixWord ++ tailWord_1372219).sum := by decide
  have hdescent : baseEnd_1372219 < baseStart_1372219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372253 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1372253 : Nat := 118140960795 + 1372253 * 2 ^ 59
def prefixEnd_1372253 : Nat := 4983230072969 + 3 ^ 40 * 1372253 * 2
def baseEnd_1372253 : Nat := 469750245716216525017753

theorem tailTrace_1372253 : CollatzResearch.WordTrace tailWord_1372253 prefixEnd_1372253 469750245716216525017753 := by
  unfold tailWord_1372253
  simp only [CollatzResearch.WordTrace]
  refine ⟨50050178697569217998985413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33366785798379478665990275 50050178697569217998985413)
  ·
    refine ⟨9384408505794228374809765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50050178697569217998985413 9384408505794228374809765)
    ·
      refine ⟨1759576594836417820276831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9384408505794228374809765 1759576594836417820276831)
      ·
        refine ⟨2639364892254626730415247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759576594836417820276831 2639364892254626730415247)
        ·
          refine ⟨3959047338381940095622871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2639364892254626730415247 3959047338381940095622871)
          ·
            refine ⟨5938571007572910143434307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959047338381940095622871 5938571007572910143434307)
            ·
              refine ⟨8907856511359365215151461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938571007572910143434307 8907856511359365215151461)
              ·
                refine ⟨1670223095879880977840899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8907856511359365215151461 1670223095879880977840899)
                ·
                  refine ⟨2505334643819821466761349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670223095879880977840899 2505334643819821466761349)
                  ·
                    refine ⟨469750245716216525017753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2505334643819821466761349 469750245716216525017753)
                    ·
                      rfl

theorem cell22_1372253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1372253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372253 prefixEnd_1372253 := by exact prefixLift 1372253
  have htrace : WordTrace (prefixWord ++ tailWord_1372253) baseStart_1372253 baseEnd_1372253 := by
    simpa [prefixWord, tailWord_1372253, baseEnd_1372253] using wordTrace_append hprefix tailTrace_1372253
  have hstable : (prefixWord ++ tailWord_1372253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372253).length < 2 ^ (prefixWord ++ tailWord_1372253).sum := by decide
  have hdescent : baseEnd_1372253 < baseStart_1372253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372268 : List Nat := [2, 2, 1, 1, 3, 5, 1, 3, 4]
def baseStart_1372268 : Nat := 118140960795 + 1372268 * 2 ^ 59
def prefixEnd_1372268 : Nat := 4983230072969 + 3 ^ 40 * 1372268 * 2
def baseEnd_1372268 : Nat := 156585126840920495297569

theorem tailTrace_1372268 : CollatzResearch.WordTrace tailWord_1372268 prefixEnd_1372268 156585126840920495297569 := by
  unfold tailWord_1372268
  simp only [CollatzResearch.WordTrace]
  refine ⟨25025362896257437780390729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33367150528343250373854305 25025362896257437780390729)
  ·
    refine ⟨18769022172193078335293047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25025362896257437780390729 18769022172193078335293047)
    ·
      refine ⟨28153533258289617502939571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18769022172193078335293047 28153533258289617502939571)
      ·
        refine ⟨42230299887434426254409357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28153533258289617502939571 42230299887434426254409357)
        ·
          refine ⟨15836362457787909845403509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42230299887434426254409357 15836362457787909845403509)
          ·
            refine ⟨1484658980417616548006579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15836362457787909845403509 1484658980417616548006579)
            ·
              refine ⟨2226988470626424822009869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484658980417616548006579 2226988470626424822009869)
              ·
                refine ⟨835120676484909308253701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2226988470626424822009869 835120676484909308253701)
                ·
                  refine ⟨156585126840920495297569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835120676484909308253701 156585126840920495297569)
                  ·
                    rfl

theorem cell22_1372268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_1372268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372268 prefixEnd_1372268 := by exact prefixLift 1372268
  have htrace : WordTrace (prefixWord ++ tailWord_1372268) baseStart_1372268 baseEnd_1372268 := by
    simpa [prefixWord, tailWord_1372268, baseEnd_1372268] using wordTrace_append hprefix tailTrace_1372268
  have hstable : (prefixWord ++ tailWord_1372268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372268).length < 2 ^ (prefixWord ++ tailWord_1372268).sum := by decide
  have hdescent : baseEnd_1372268 < baseStart_1372268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372279 : List Nat := [1, 1, 3, 1, 1, 7, 8]
def baseStart_1372279 : Nat := 118140960795 + 1372279 * 2 ^ 59
def prefixEnd_1372279 : Nat := 4983230072969 + 3 ^ 40 * 1372279 * 2
def baseEnd_1372279 : Nat := 17398486890650411995099

theorem tailTrace_1372279 : CollatzResearch.WordTrace tailWord_1372279 prefixEnd_1372279 17398486890650411995099 := by
  unfold tailWord_1372279
  simp only [CollatzResearch.WordTrace]
  refine ⟨50051126995475024439431891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33367417996983349626287927 50051126995475024439431891)
  ·
    refine ⟨75076690493212536659147837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50051126995475024439431891 75076690493212536659147837)
    ·
      refine ⟨28153758934954701247180439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75076690493212536659147837 28153758934954701247180439)
      ·
        refine ⟨42230638402432051870770659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28153758934954701247180439 42230638402432051870770659)
        ·
          refine ⟨63345957603648077806155989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42230638402432051870770659 63345957603648077806155989)
          ·
            refine ⟨1484670881335501823581781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 63345957603648077806155989 1484670881335501823581781)
            ·
              refine ⟨17398486890650411995099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1484670881335501823581781 17398486890650411995099)
              ·
                rfl

theorem cell22_1372279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 8].length) (baseStart_1372279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372279 prefixEnd_1372279 := by exact prefixLift 1372279
  have htrace : WordTrace (prefixWord ++ tailWord_1372279) baseStart_1372279 baseEnd_1372279 := by
    simpa [prefixWord, tailWord_1372279, baseEnd_1372279] using wordTrace_append hprefix tailTrace_1372279
  have hstable : (prefixWord ++ tailWord_1372279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372279).length < 2 ^ (prefixWord ++ tailWord_1372279).sum := by decide
  have hdescent : baseEnd_1372279 < baseStart_1372279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372281 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_1372281 : Nat := 118140960795 + 1372281 * 2 ^ 59
def prefixEnd_1372281 : Nat := 4983230072969 + 3 ^ 40 * 1372281 * 2
def baseEnd_1372281 : Nat := 469759830688433785317667

theorem tailTrace_1372281 : CollatzResearch.WordTrace tailWord_1372281 prefixEnd_1372281 469759830688433785317667 := by
  unfold tailWord_1372281
  simp only [CollatzResearch.WordTrace]
  refine ⟨50051199941467778781004697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33367466627645185854003131 50051199941467778781004697)
  ·
    refine ⟨37538399956100834085753523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50051199941467778781004697 37538399956100834085753523)
    ·
      refine ⟨56307599934151251128630285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37538399956100834085753523 56307599934151251128630285)
      ·
        refine ⟨21115349975306719173236357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56307599934151251128630285 21115349975306719173236357)
        ·
          refine ⟨3959128120370009844981817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21115349975306719173236357 3959128120370009844981817)
          ·
            refine ⟨2969346090277507383736363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3959128120370009844981817 2969346090277507383736363)
            ·
              refine ⟨4454019135416261075604545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969346090277507383736363 4454019135416261075604545)
              ·
                refine ⟨3340514351562195806703409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454019135416261075604545 3340514351562195806703409)
                ·
                  refine ⟨2505385763671646855027557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340514351562195806703409 2505385763671646855027557)
                  ·
                    refine ⟨469759830688433785317667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2505385763671646855027557 469759830688433785317667)
                    ·
                      rfl

theorem cell22_1372281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_1372281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372281 prefixEnd_1372281 := by exact prefixLift 1372281
  have htrace : WordTrace (prefixWord ++ tailWord_1372281) baseStart_1372281 baseEnd_1372281 := by
    simpa [prefixWord, tailWord_1372281, baseEnd_1372281] using wordTrace_append hprefix tailTrace_1372281
  have hstable : (prefixWord ++ tailWord_1372281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372281).length < 2 ^ (prefixWord ++ tailWord_1372281).sum := by decide
  have hdescent : baseEnd_1372281 < baseStart_1372281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372296 : List Nat := [2, 1, 3, 4, 1, 2, 2, 7]
def baseStart_1372296 : Nat := 118140960795 + 1372296 * 2 ^ 59
def prefixEnd_1372296 : Nat := 4983230072969 + 3 ^ 40 * 1372296 * 2
def baseEnd_1372296 : Nat := 52196107277219860688069

theorem tailTrace_1372296 : CollatzResearch.WordTrace tailWord_1372296 prefixEnd_1372296 52196107277219860688069 := by
  unfold tailWord_1372296
  simp only [CollatzResearch.WordTrace]
  refine ⟨25025873518206718171400371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33367831357608957561867161 25025873518206718171400371)
  ·
    refine ⟨37538810277310077257100557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25025873518206718171400371 37538810277310077257100557)
    ·
      refine ⟨14077053853991278971412709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37538810277310077257100557 14077053853991278971412709)
      ·
        refine ⟨2639447597623364807139883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14077053853991278971412709 2639447597623364807139883)
        ·
          refine ⟨3959171396435047210709825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2639447597623364807139883 3959171396435047210709825)
          ·
            refine ⟨2969378547326285408032369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3959171396435047210709825 2969378547326285408032369)
            ·
              refine ⟨2227033910494714056024277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969378547326285408032369 2227033910494714056024277)
              ·
                refine ⟨52196107277219860688069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2227033910494714056024277 52196107277219860688069)
                ·
                  rfl

theorem cell22_1372296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_1372296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372296 prefixEnd_1372296 := by exact prefixLift 1372296
  have htrace : WordTrace (prefixWord ++ tailWord_1372296) baseStart_1372296 baseEnd_1372296 := by
    simpa [prefixWord, tailWord_1372296, baseEnd_1372296] using wordTrace_append hprefix tailTrace_1372296
  have hstable : (prefixWord ++ tailWord_1372296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372296).length < 2 ^ (prefixWord ++ tailWord_1372296).sum := by decide
  have hdescent : baseEnd_1372296 < baseStart_1372296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372339 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 2, 5]
def baseStart_1372339 : Nat := 118140960795 + 1372339 * 2 ^ 59
def prefixEnd_1372339 : Nat := 4983230072969 + 3 ^ 40 * 1372339 * 2
def baseEnd_1372339 : Nat := 469779685273740967367489

theorem tailTrace_1372339 : CollatzResearch.WordTrace tailWord_1372339 prefixEnd_1372339 469779685273740967367489 := by
  unfold tailWord_1372339
  simp only [CollatzResearch.WordTrace]
  refine ⟨50053315375257654686616071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33368876916838436457744047 50053315375257654686616071)
  ·
    refine ⟨75079973062886482029924107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50053315375257654686616071 75079973062886482029924107)
    ·
      refine ⟨112619959594329723044886161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75079973062886482029924107 112619959594329723044886161)
      ·
        refine ⟨84464969695747292283664621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112619959594329723044886161 84464969695747292283664621)
        ·
          refine ⟨31674363635905234606374233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84464969695747292283664621 31674363635905234606374233)
          ·
            refine ⟨23755772726928925954780675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31674363635905234606374233 23755772726928925954780675)
            ·
              refine ⟨35633659090393388932171013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23755772726928925954780675 35633659090393388932171013)
              ·
                refine ⟨6681311079448760424782065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35633659090393388932171013 6681311079448760424782065)
                ·
                  refine ⟨5010983309586570318586549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6681311079448760424782065 5010983309586570318586549)
                  ·
                    refine ⟨469779685273740967367489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5010983309586570318586549 469779685273740967367489)
                    ·
                      rfl

theorem cell22_1372339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_1372339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372339 prefixEnd_1372339 := by exact prefixLift 1372339
  have htrace : WordTrace (prefixWord ++ tailWord_1372339) baseStart_1372339 baseEnd_1372339 := by
    simpa [prefixWord, tailWord_1372339, baseEnd_1372339] using wordTrace_append hprefix tailTrace_1372339
  have hstable : (prefixWord ++ tailWord_1372339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372339).length < 2 ^ (prefixWord ++ tailWord_1372339).sum := by decide
  have hdescent : baseEnd_1372339 < baseStart_1372339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372356 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1372356 : Nat := 118140960795 + 1372356 * 2 ^ 59
def prefixEnd_1372356 : Nat := 4983230072969 + 3 ^ 40 * 1372356 * 2
def baseEnd_1372356 : Nat := 469785504721158589692437

theorem tailTrace_1372356 : CollatzResearch.WordTrace tailWord_1372356 prefixEnd_1372356 469785504721158589692437 := by
  unfold tailWord_1372356
  simp only [CollatzResearch.WordTrace]
  refine ⟨25026967708098033294992461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33369290277464044393323281 25026967708098033294992461)
  ·
    refine ⟨9385112890536762485622173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25026967708098033294992461 9385112890536762485622173)
    ·
      refine ⟨3519417333951285932108315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9385112890536762485622173 3519417333951285932108315)
      ·
        refine ⟨5279126000926928898162473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519417333951285932108315 5279126000926928898162473)
        ·
          refine ⟨3959344500695196673621855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5279126000926928898162473 3959344500695196673621855)
          ·
            refine ⟨5939016751042795010432783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959344500695196673621855 5939016751042795010432783)
            ·
              refine ⟨8908525126564192515649175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939016751042795010432783 8908525126564192515649175)
              ·
                refine ⟨13362787689846288773473763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8908525126564192515649175 13362787689846288773473763)
                ·
                  refine ⟨20044181534769433160210645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13362787689846288773473763 20044181534769433160210645)
                  ·
                    refine ⟨469785504721158589692437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20044181534769433160210645 469785504721158589692437)
                    ·
                      rfl

theorem cell22_1372356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1372356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372356 prefixEnd_1372356 := by exact prefixLift 1372356
  have htrace : WordTrace (prefixWord ++ tailWord_1372356) baseStart_1372356 baseEnd_1372356 := by
    simpa [prefixWord, tailWord_1372356, baseEnd_1372356] using wordTrace_append hprefix tailTrace_1372356
  have hstable : (prefixWord ++ tailWord_1372356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372356).length < 2 ^ (prefixWord ++ tailWord_1372356).sum := by decide
  have hdescent : baseEnd_1372356 < baseStart_1372356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372369 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 8]
def baseStart_1372369 : Nat := 118140960795 + 1372369 * 2 ^ 59
def prefixEnd_1372369 : Nat := 4983230072969 + 3 ^ 40 * 1372369 * 2
def baseEnd_1372369 : Nat := 156596651628943629705799

theorem tailTrace_1372369 : CollatzResearch.WordTrace tailWord_1372369 prefixEnd_1372369 156596651628943629705799 := by
  unfold tailWord_1372369
  simp only [CollatzResearch.WordTrace]
  refine ⟨50054409565148969810208161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33369606376765979873472107 50054409565148969810208161)
  ·
    refine ⟨37540807173861727357656121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50054409565148969810208161 37540807173861727357656121)
    ·
      refine ⟨28155605380396295518242091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37540807173861727357656121 28155605380396295518242091)
      ·
        refine ⟨42233408070594443277363137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28155605380396295518242091 42233408070594443277363137)
        ·
          refine ⟨31675056052945832458022353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42233408070594443277363137 31675056052945832458022353)
          ·
            refine ⟨23756292039709374343516765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31675056052945832458022353 23756292039709374343516765)
            ·
              refine ⟨8908609514891015378818787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23756292039709374343516765 8908609514891015378818787)
              ·
                refine ⟨13362914272336523068228181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8908609514891015378818787 13362914272336523068228181)
                ·
                  refine ⟨156596651628943629705799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13362914272336523068228181 156596651628943629705799)
                  ·
                    rfl

theorem cell22_1372369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_1372369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372369 prefixEnd_1372369 := by exact prefixLift 1372369
  have htrace : WordTrace (prefixWord ++ tailWord_1372369) baseStart_1372369 baseEnd_1372369 := by
    simpa [prefixWord, tailWord_1372369, baseEnd_1372369] using wordTrace_append hprefix tailTrace_1372369
  have hstable : (prefixWord ++ tailWord_1372369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372369).length < 2 ^ (prefixWord ++ tailWord_1372369).sum := by decide
  have hdescent : baseEnd_1372369 < baseStart_1372369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372463 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 3, 3]
def baseStart_1372463 : Nat := 118140960795 + 1372463 * 2 ^ 59
def prefixEnd_1372463 : Nat := 4983230072969 + 3 ^ 40 * 1372463 * 2
def baseEnd_1372463 : Nat := 469822133007845977267109

theorem tailTrace_1372463 : CollatzResearch.WordTrace tailWord_1372463 prefixEnd_1372463 469822133007845977267109 := by
  unfold tailWord_1372463
  simp only [CollatzResearch.WordTrace]
  refine ⟨50057838026808423864130043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33371892017872282576086695 50057838026808423864130043)
  ·
    refine ⟨75086757040212635796195065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50057838026808423864130043 75086757040212635796195065)
    ·
      refine ⟨56315067780159476847146299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75086757040212635796195065 56315067780159476847146299)
      ·
        refine ⟨84472601670239215270719449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56315067780159476847146299 84472601670239215270719449)
        ·
          refine ⟨63354451252679411453039587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84472601670239215270719449 63354451252679411453039587)
          ·
            refine ⟨95031676879019117179559381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63354451252679411453039587 95031676879019117179559381)
            ·
              refine ⟨2227304926852010558895923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95031676879019117179559381 2227304926852010558895923)
              ·
                refine ⟨3340957390278015838343885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227304926852010558895923 3340957390278015838343885)
                ·
                  refine ⟨1252859021354255939378957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3340957390278015838343885 1252859021354255939378957)
                  ·
                    refine ⟨469822133007845977267109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252859021354255939378957 469822133007845977267109)
                    ·
                      rfl

theorem cell22_1372463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_1372463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372463 prefixEnd_1372463 := by exact prefixLift 1372463
  have htrace : WordTrace (prefixWord ++ tailWord_1372463) baseStart_1372463 baseEnd_1372463 := by
    simpa [prefixWord, tailWord_1372463, baseEnd_1372463] using wordTrace_append hprefix tailTrace_1372463
  have hstable : (prefixWord ++ tailWord_1372463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372463).length < 2 ^ (prefixWord ++ tailWord_1372463).sum := by decide
  have hdescent : baseEnd_1372463 < baseStart_1372463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372514 : List Nat := [3, 3, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1372514 : Nat := 118140960795 + 1372514 * 2 ^ 59
def prefixEnd_1372514 : Nat := 4983230072969 + 3 ^ 40 * 1372514 * 2
def baseEnd_1372514 : Nat := 469839591350098844241953

theorem tailTrace_1372514 : CollatzResearch.WordTrace tailWord_1372514 prefixEnd_1372514 469839591350098844241953 := by
  unfold tailWord_1372514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12514924537405914893559149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33373132099749106382824397 12514924537405914893559149)
  ·
    refine ⟨4693096701527218085084681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12514924537405914893559149 4693096701527218085084681)
    ·
      refine ⟨3519822526145413563813511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4693096701527218085084681 3519822526145413563813511)
      ·
        refine ⟨5279733789218120345720267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519822526145413563813511 5279733789218120345720267)
        ·
          refine ⟨7919600683827180518580401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279733789218120345720267 7919600683827180518580401)
          ·
            refine ⟨5939700512870385388935301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7919600683827180518580401 5939700512870385388935301)
            ·
              refine ⟨1113693846163197260425369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5939700512870385388935301 1113693846163197260425369)
              ·
                refine ⟨835270384622397945319027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113693846163197260425369 835270384622397945319027)
                ·
                  refine ⟨1252905576933596917978541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835270384622397945319027 1252905576933596917978541)
                  ·
                    refine ⟨469839591350098844241953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252905576933596917978541 469839591350098844241953)
                    ·
                      rfl

theorem cell22_1372514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1372514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372514 prefixEnd_1372514 := by exact prefixLift 1372514
  have htrace : WordTrace (prefixWord ++ tailWord_1372514) baseStart_1372514 baseEnd_1372514 := by
    simpa [prefixWord, tailWord_1372514, baseEnd_1372514] using wordTrace_append hprefix tailTrace_1372514
  have hstable : (prefixWord ++ tailWord_1372514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372514).length < 2 ^ (prefixWord ++ tailWord_1372514).sum := by decide
  have hdescent : baseEnd_1372514 < baseStart_1372514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372521 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 6]
def baseStart_1372521 : Nat := 118140960795 + 1372521 * 2 ^ 59
def prefixEnd_1372521 : Nat := 4983230072969 + 3 ^ 40 * 1372521 * 2
def baseEnd_1372521 : Nat := 156613995864384386438977

theorem tailTrace_1372521 : CollatzResearch.WordTrace tailWord_1372521 prefixEnd_1372521 156613995864384386438977 := by
  unfold tailWord_1372521
  simp only [CollatzResearch.WordTrace]
  refine ⟨50059953460598299769741417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33373302307065533179827611 50059953460598299769741417)
  ·
    refine ⟨37544965095448724827306063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50059953460598299769741417 37544965095448724827306063)
    ·
      refine ⟨56317447643173087240959095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37544965095448724827306063 56317447643173087240959095)
      ·
        refine ⟨84476171464759630861438643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56317447643173087240959095 84476171464759630861438643)
        ·
          refine ⟨126714257197139446292157965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84476171464759630861438643 126714257197139446292157965)
          ·
            refine ⟨47517846448927292359559237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126714257197139446292157965 47517846448927292359559237)
            ·
              refine ⟨8909596209173867317417357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47517846448927292359559237 8909596209173867317417357)
              ·
                refine ⟨3341098578440200244031509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8909596209173867317417357 3341098578440200244031509)
                ·
                  refine ⟨156613995864384386438977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3341098578440200244031509 156613995864384386438977)
                  ·
                    rfl

theorem cell22_1372521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_1372521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372521 prefixEnd_1372521 := by exact prefixLift 1372521
  have htrace : WordTrace (prefixWord ++ tailWord_1372521) baseStart_1372521 baseEnd_1372521 := by
    simpa [prefixWord, tailWord_1372521, baseEnd_1372521] using wordTrace_append hprefix tailTrace_1372521
  have hstable : (prefixWord ++ tailWord_1372521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372521).length < 2 ^ (prefixWord ++ tailWord_1372521).sum := by decide
  have hdescent : baseEnd_1372521 < baseStart_1372521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372553 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_1372553 : Nat := 118140960795 + 1372553 * 2 ^ 59
def prefixEnd_1372553 : Nat := 4983230072969 + 3 ^ 40 * 1372553 * 2
def baseEnd_1372553 : Nat := 469852941847115742516833

theorem tailTrace_1372553 : CollatzResearch.WordTrace tailWord_1372553 prefixEnd_1372553 469852941847115742516833 := by
  unfold tailWord_1372553
  simp only [CollatzResearch.WordTrace]
  refine ⟨50061120596482369234906313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33374080397654912823270875 50061120596482369234906313)
  ·
    refine ⟨37545840447361776926179735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50061120596482369234906313 37545840447361776926179735)
    ·
      refine ⟨56318760671042665389269603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37545840447361776926179735 56318760671042665389269603)
      ·
        refine ⟨84478141006563998083904405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56318760671042665389269603 84478141006563998083904405)
        ·
          refine ⟨3959912859682687410183019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84478141006563998083904405 3959912859682687410183019)
          ·
            refine ⟨5939869289524031115274529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959912859682687410183019 5939869289524031115274529)
            ·
              refine ⟨4454901967143023336455897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5939869289524031115274529 4454901967143023336455897)
              ·
                refine ⟨3341176475357267502341923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454901967143023336455897 3341176475357267502341923)
                ·
                  refine ⟨5011764713035901253512885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341176475357267502341923 5011764713035901253512885)
                  ·
                    refine ⟨469852941847115742516833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5011764713035901253512885 469852941847115742516833)
                    ·
                      rfl

theorem cell22_1372553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_1372553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372553 prefixEnd_1372553 := by exact prefixLift 1372553
  have htrace : WordTrace (prefixWord ++ tailWord_1372553) baseStart_1372553 baseEnd_1372553 := by
    simpa [prefixWord, tailWord_1372553, baseEnd_1372553] using wordTrace_append hprefix tailTrace_1372553
  have hstable : (prefixWord ++ tailWord_1372553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372553).length < 2 ^ (prefixWord ++ tailWord_1372553).sum := by decide
  have hdescent : baseEnd_1372553 < baseStart_1372553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372555 : List Nat := [1, 1, 1, 1, 4, 5, 2, 3, 4]
def baseStart_1372555 : Nat := 118140960795 + 1372555 * 2 ^ 59
def prefixEnd_1372555 : Nat := 4983230072969 + 3 ^ 40 * 1372555 * 2
def baseEnd_1372555 : Nat := 156617875495996134655609

theorem tailTrace_1372555 : CollatzResearch.WordTrace tailWord_1372555 prefixEnd_1372555 156617875495996134655609 := by
  unfold tailWord_1372555
  simp only [CollatzResearch.WordTrace]
  refine ⟨50061193542475123576479119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33374129028316749050986079 50061193542475123576479119)
  ·
    refine ⟨75091790313712685364718679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50061193542475123576479119 75091790313712685364718679)
    ·
      refine ⟨112637685470569028047078019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75091790313712685364718679 112637685470569028047078019)
      ·
        refine ⟨168956528205853542070617029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112637685470569028047078019 168956528205853542070617029)
        ·
          refine ⟨31679349038597539138240693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168956528205853542070617029 31679349038597539138240693)
          ·
            refine ⟨2969938972368519294210065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31679349038597539138240693 2969938972368519294210065)
            ·
              refine ⟨2227454229276389470657549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969938972368519294210065 2227454229276389470657549)
              ·
                refine ⟨835295335978646051496581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2227454229276389470657549 835295335978646051496581)
                ·
                  refine ⟨156617875495996134655609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835295335978646051496581 156617875495996134655609)
                  ·
                    rfl

theorem cell22_1372555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 4].length) (baseStart_1372555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372555 prefixEnd_1372555 := by exact prefixLift 1372555
  have htrace : WordTrace (prefixWord ++ tailWord_1372555) baseStart_1372555 baseEnd_1372555 := by
    simpa [prefixWord, tailWord_1372555, baseEnd_1372555] using wordTrace_append hprefix tailTrace_1372555
  have hstable : (prefixWord ++ tailWord_1372555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372555).length < 2 ^ (prefixWord ++ tailWord_1372555).sum := by decide
  have hdescent : baseEnd_1372555 < baseStart_1372555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372570 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_1372570 : Nat := 118140960795 + 1372570 * 2 ^ 59
def prefixEnd_1372570 : Nat := 4983230072969 + 3 ^ 40 * 1372570 * 2
def baseEnd_1372570 : Nat := 469858761294533364841781

theorem tailTrace_1372570 : CollatzResearch.WordTrace tailWord_1372570 prefixEnd_1372570 469858761294533364841781 := by
  unfold tailWord_1372570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515435159355195284568791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33374493758280520758850109 12515435159355195284568791)
  ·
    refine ⟨18773152739032792926853187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12515435159355195284568791 18773152739032792926853187)
    ·
      refine ⟨28159729108549189390279781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18773152739032792926853187 28159729108549189390279781)
      ·
        refine ⟨5279949207852973010677459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28159729108549189390279781 5279949207852973010677459)
        ·
          refine ⟨7919923811779459516016189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279949207852973010677459 7919923811779459516016189)
          ·
            refine ⟨2969971429417297318506071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7919923811779459516016189 2969971429417297318506071)
            ·
              refine ⟨4454957144125945977759107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969971429417297318506071 4454957144125945977759107)
              ·
                refine ⟨6682435716188918966638661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454957144125945977759107 6682435716188918966638661)
                ·
                  refine ⟨1252956696785422306244749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6682435716188918966638661 1252956696785422306244749)
                  ·
                    refine ⟨469858761294533364841781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252956696785422306244749 469858761294533364841781)
                    ·
                      rfl

theorem cell22_1372570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_1372570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372570 prefixEnd_1372570 := by exact prefixLift 1372570
  have htrace : WordTrace (prefixWord ++ tailWord_1372570) baseStart_1372570 baseEnd_1372570 := by
    simpa [prefixWord, tailWord_1372570, baseEnd_1372570] using wordTrace_append hprefix tailTrace_1372570
  have hstable : (prefixWord ++ tailWord_1372570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372570).length < 2 ^ (prefixWord ++ tailWord_1372570).sum := by decide
  have hdescent : baseEnd_1372570 < baseStart_1372570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372630 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1372630 : Nat := 118140960795 + 1372630 * 2 ^ 59
def prefixEnd_1372630 : Nat := 4983230072969 + 3 ^ 40 * 1372630 * 2
def baseEnd_1372630 : Nat := 469879300520713208341597

theorem tailTrace_1372630 : CollatzResearch.WordTrace tailWord_1372630 prefixEnd_1372630 469879300520713208341597 := by
  unfold tailWord_1372630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128995563575213211591209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33375952678135607590306229 3128995563575213211591209)
  ·
    refine ⟨2346746672681409908693407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3128995563575213211591209 2346746672681409908693407)
    ·
      refine ⟨3520120009022114863040111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346746672681409908693407 3520120009022114863040111)
      ·
        refine ⟨5280180013533172294560167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520120009022114863040111 5280180013533172294560167)
        ·
          refine ⟨7920270020299758441840251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280180013533172294560167 7920270020299758441840251)
          ·
            refine ⟨11880405030449637662760377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7920270020299758441840251 11880405030449637662760377)
            ·
              refine ⟨8910303772837228247070283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11880405030449637662760377 8910303772837228247070283)
              ·
                refine ⟨13365455659255842370605425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8910303772837228247070283 13365455659255842370605425)
                ·
                  refine ⟨10024091744441881777954069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13365455659255842370605425 10024091744441881777954069)
                  ·
                    refine ⟨469879300520713208341597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10024091744441881777954069 469879300520713208341597)
                    ·
                      rfl

theorem cell22_1372630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1372630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372630 prefixEnd_1372630 := by exact prefixLift 1372630
  have htrace : WordTrace (prefixWord ++ tailWord_1372630) baseStart_1372630 baseEnd_1372630 := by
    simpa [prefixWord, tailWord_1372630, baseEnd_1372630] using wordTrace_append hprefix tailTrace_1372630
  have hstable : (prefixWord ++ tailWord_1372630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372630).length < 2 ^ (prefixWord ++ tailWord_1372630).sum := by decide
  have hdescent : baseEnd_1372630 < baseStart_1372630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372692 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1372692 : Nat := 118140960795 + 1372692 * 2 ^ 59
def prefixEnd_1372692 : Nat := 4983230072969 + 3 ^ 40 * 1372692 * 2
def baseEnd_1372692 : Nat := 469900524387765713291407

theorem tailTrace_1372692 : CollatzResearch.WordTrace tailWord_1372692 prefixEnd_1372692 469900524387765713291407 := by
  unfold tailWord_1372692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25033095171489397987108165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33377460228652530649477553 25033095171489397987108165)
  ·
    refine ⟨4693705344654262122582781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25033095171489397987108165 4693705344654262122582781)
    ·
      refine ⟨1760139504245348295968543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4693705344654262122582781 1760139504245348295968543)
      ·
        refine ⟨2640209256368022443952815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760139504245348295968543 2640209256368022443952815)
        ·
          refine ⟨3960313884552033665929223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640209256368022443952815 3960313884552033665929223)
          ·
            refine ⟨5940470826828050498893835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960313884552033665929223 5940470826828050498893835)
            ·
              refine ⟨8910706240242075748340753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940470826828050498893835 8910706240242075748340753)
              ·
                refine ⟨6683029680181556811255565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8910706240242075748340753 6683029680181556811255565)
                ·
                  refine ⟨2506136130068083804220837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6683029680181556811255565 2506136130068083804220837)
                  ·
                    refine ⟨469900524387765713291407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2506136130068083804220837 469900524387765713291407)
                    ·
                      rfl

theorem cell22_1372692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1372692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372692 prefixEnd_1372692 := by exact prefixLift 1372692
  have htrace : WordTrace (prefixWord ++ tailWord_1372692) baseStart_1372692 baseEnd_1372692 := by
    simpa [prefixWord, tailWord_1372692, baseEnd_1372692] using wordTrace_append hprefix tailTrace_1372692
  have hstable : (prefixWord ++ tailWord_1372692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372692).length < 2 ^ (prefixWord ++ tailWord_1372692).sum := by decide
  have hdescent : baseEnd_1372692 < baseStart_1372692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372703 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 1, 6]
def baseStart_1372703 : Nat := 118140960795 + 1372703 * 2 ^ 59
def prefixEnd_1372703 : Nat := 4983230072969 + 3 ^ 40 * 1372703 * 2
def baseEnd_1372703 : Nat := 469904289912565351266373

theorem tailTrace_1372703 : CollatzResearch.WordTrace tailWord_1372703 prefixEnd_1372703 469904289912565351266373 := by
  unfold tailWord_1372703
  simp only [CollatzResearch.WordTrace]
  refine ⟨50066591545938944852866763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33377727697292629901911175 50066591545938944852866763)
  ·
    refine ⟨75099887318908417279300145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50066591545938944852866763 75099887318908417279300145)
    ·
      refine ⟨56324915489181312959475109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75099887318908417279300145 56324915489181312959475109)
      ·
        refine ⟨10560921654221496179901583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56324915489181312959475109 10560921654221496179901583)
        ·
          refine ⟨15841382481332244269852375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10560921654221496179901583 15841382481332244269852375)
          ·
            refine ⟨23762073721998366404778563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15841382481332244269852375 23762073721998366404778563)
            ·
              refine ⟨35643110582997549607167845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23762073721998366404778563 35643110582997549607167845)
              ·
                refine ⟨6683083234312040551343971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35643110582997549607167845 6683083234312040551343971)
                ·
                  refine ⟨10024624851468060827015957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683083234312040551343971 10024624851468060827015957)
                  ·
                    refine ⟨469904289912565351266373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10024624851468060827015957 469904289912565351266373)
                    ·
                      rfl

theorem cell22_1372703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_1372703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372703 prefixEnd_1372703 := by exact prefixLift 1372703
  have htrace : WordTrace (prefixWord ++ tailWord_1372703) baseStart_1372703 baseEnd_1372703 := by
    simpa [prefixWord, tailWord_1372703, baseEnd_1372703] using wordTrace_append hprefix tailTrace_1372703
  have hstable : (prefixWord ++ tailWord_1372703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372703).length < 2 ^ (prefixWord ++ tailWord_1372703).sum := by decide
  have hdescent : baseEnd_1372703 < baseStart_1372703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372705 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1372705 : Nat := 118140960795 + 1372705 * 2 ^ 59
def prefixEnd_1372705 : Nat := 4983230072969 + 3 ^ 40 * 1372705 * 2
def baseEnd_1372705 : Nat := 469904974553438012716367

theorem tailTrace_1372705 : CollatzResearch.WordTrace tailWord_1372705 prefixEnd_1372705 469904974553438012716367 := by
  unfold tailWord_1372705
  simp only [CollatzResearch.WordTrace]
  refine ⟨50066664491931699194439569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33377776327954466129626379 50066664491931699194439569)
  ·
    refine ⟨37549998368948774395829677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50066664491931699194439569 37549998368948774395829677)
    ·
      refine ⟨14081249388355790398436129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37549998368948774395829677 14081249388355790398436129)
      ·
        refine ⟨10560937041266842798827097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14081249388355790398436129 10560937041266842798827097)
        ·
          refine ⟨7920702780950132099120323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10560937041266842798827097 7920702780950132099120323)
          ·
            refine ⟨11881054171425198148680485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7920702780950132099120323 11881054171425198148680485)
            ·
              refine ⟨2227697657142224652877591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11881054171425198148680485 2227697657142224652877591)
              ·
                refine ⟨3341546485713336979316387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227697657142224652877591 3341546485713336979316387)
                ·
                  refine ⟨5012319728570005468974581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341546485713336979316387 5012319728570005468974581)
                  ·
                    refine ⟨469904974553438012716367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5012319728570005468974581 469904974553438012716367)
                    ·
                      rfl

theorem cell22_1372705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1372705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372705 prefixEnd_1372705 := by exact prefixLift 1372705
  have htrace : WordTrace (prefixWord ++ tailWord_1372705) baseStart_1372705 baseEnd_1372705 := by
    simpa [prefixWord, tailWord_1372705, baseEnd_1372705] using wordTrace_append hprefix tailTrace_1372705
  have hstable : (prefixWord ++ tailWord_1372705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372705).length < 2 ^ (prefixWord ++ tailWord_1372705).sum := by decide
  have hdescent : baseEnd_1372705 < baseStart_1372705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372720 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_1372720 : Nat := 118140960795 + 1372720 * 2 ^ 59
def prefixEnd_1372720 : Nat := 4983230072969 + 3 ^ 40 * 1372720 * 2
def baseEnd_1372720 : Nat := 469910109359982973591321

theorem tailTrace_1372720 : CollatzResearch.WordTrace tailWord_1372720 prefixEnd_1372720 469910109359982973591321 := by
  unfold tailWord_1372720
  simp only [CollatzResearch.WordTrace]
  refine ⟨25033605793438678378117807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33378141057918237837490409 25033605793438678378117807)
  ·
    refine ⟨37550408690158017567176711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25033605793438678378117807 37550408690158017567176711)
    ·
      refine ⟨56325613035237026350765067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37550408690158017567176711 56325613035237026350765067)
      ·
        refine ⟨84488419552855539526147601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56325613035237026350765067 84488419552855539526147601)
        ·
          refine ⟨63366314664641654644610701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84488419552855539526147601 63366314664641654644610701)
          ·
            refine ⟨23762367999240620491729013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63366314664641654644610701 23762367999240620491729013)
            ·
              refine ⟨2227721999928808171099595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23762367999240620491729013 2227721999928808171099595)
              ·
                refine ⟨3341582999893212256649393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227721999928808171099595 3341582999893212256649393)
                ·
                  refine ⟨2506187249919909192487045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3341582999893212256649393 2506187249919909192487045)
                  ·
                    refine ⟨469910109359982973591321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2506187249919909192487045 469910109359982973591321)
                    ·
                      rfl

theorem cell22_1372720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_1372720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372720 prefixEnd_1372720 := by exact prefixLift 1372720
  have htrace : WordTrace (prefixWord ++ tailWord_1372720) baseStart_1372720 baseEnd_1372720 := by
    simpa [prefixWord, tailWord_1372720, baseEnd_1372720] using wordTrace_append hprefix tailTrace_1372720
  have hstable : (prefixWord ++ tailWord_1372720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372720).length < 2 ^ (prefixWord ++ tailWord_1372720).sum := by decide
  have hdescent : baseEnd_1372720 < baseStart_1372720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372726 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1372726 : Nat := 118140960795 + 1372726 * 2 ^ 59
def prefixEnd_1372726 : Nat := 4983230072969 + 3 ^ 40 * 1372726 * 2
def baseEnd_1372726 : Nat := 469912163282600957941303

theorem tailTrace_1372726 : CollatzResearch.WordTrace tailWord_1372726 prefixEnd_1372726 469912163282600957941303 := by
  unfold tailWord_1372726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129214401553476236309627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33378286949903746520636021 3129214401553476236309627)
  ·
    refine ⟨4693821602330214354464441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3129214401553476236309627 4693821602330214354464441)
    ·
      refine ⟨3520366201747660765848331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4693821602330214354464441 3520366201747660765848331)
      ·
        refine ⟨5280549302621491148772497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520366201747660765848331 5280549302621491148772497)
        ·
          refine ⟨3960411976966118361579373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5280549302621491148772497 3960411976966118361579373)
          ·
            refine ⟨1485154491362294385592265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3960411976966118361579373 1485154491362294385592265)
            ·
              refine ⟨1113865868521720789194199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485154491362294385592265 1113865868521720789194199)
              ·
                refine ⟨1670798802782581183791299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113865868521720789194199 1670798802782581183791299)
                ·
                  refine ⟨2506198204173871775686949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670798802782581183791299 2506198204173871775686949)
                  ·
                    refine ⟨469912163282600957941303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2506198204173871775686949 469912163282600957941303)
                    ·
                      rfl

theorem cell22_1372726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1372726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372726 prefixEnd_1372726 := by exact prefixLift 1372726
  have htrace : WordTrace (prefixWord ++ tailWord_1372726) baseStart_1372726 baseEnd_1372726 := by
    simpa [prefixWord, tailWord_1372726, baseEnd_1372726] using wordTrace_append hprefix tailTrace_1372726
  have hstable : (prefixWord ++ tailWord_1372726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372726).length < 2 ^ (prefixWord ++ tailWord_1372726).sum := by decide
  have hdescent : baseEnd_1372726 < baseStart_1372726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372801 : List Nat := [1, 2, 4, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1372801 : Nat := 118140960795 + 1372801 * 2 ^ 59
def prefixEnd_1372801 : Nat := 4983230072969 + 3 ^ 40 * 1372801 * 2
def baseEnd_1372801 : Nat := 469937837315325762316073

theorem tailTrace_1372801 : CollatzResearch.WordTrace tailWord_1372801 prefixEnd_1372801 469937837315325762316073 := by
  unfold tailWord_1372801
  simp only [CollatzResearch.WordTrace]
  refine ⟨50070165899583907589934257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33380110599722605059956171 50070165899583907589934257)
  ·
    refine ⟨37552624424687930692450693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50070165899583907589934257 37552624424687930692450693)
    ·
      refine ⟨7041117079628987004834505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37552624424687930692450693 7041117079628987004834505)
      ·
        refine ⟨5280837809721740253625879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7041117079628987004834505 5280837809721740253625879)
        ·
          refine ⟨7921256714582610380438819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280837809721740253625879 7921256714582610380438819)
          ·
            refine ⟨11881885071873915570658229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7921256714582610380438819 11881885071873915570658229)
            ·
              refine ⟨1113926725488179584749209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11881885071873915570658229 1113926725488179584749209)
              ·
                refine ⟨835445044116134688561907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113926725488179584749209 835445044116134688561907)
                ·
                  refine ⟨1253167566174202032842861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835445044116134688561907 1253167566174202032842861)
                  ·
                    refine ⟨469937837315325762316073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253167566174202032842861 469937837315325762316073)
                    ·
                      rfl

theorem cell22_1372801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1372801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372801 prefixEnd_1372801 := by exact prefixLift 1372801
  have htrace : WordTrace (prefixWord ++ tailWord_1372801) baseStart_1372801 baseEnd_1372801 := by
    simpa [prefixWord, tailWord_1372801, baseEnd_1372801] using wordTrace_append hprefix tailTrace_1372801
  have hstable : (prefixWord ++ tailWord_1372801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372801).length < 2 ^ (prefixWord ++ tailWord_1372801).sum := by decide
  have hdescent : baseEnd_1372801 < baseStart_1372801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372874 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_1372874 : Nat := 118140960795 + 1372874 * 2 ^ 59
def prefixEnd_1372874 : Nat := 4983230072969 + 3 ^ 40 * 1372874 * 2
def baseEnd_1372874 : Nat := 469962826707177905240849

theorem tailTrace_1372874 : CollatzResearch.WordTrace tailWord_1372874 prefixEnd_1372874 469962826707177905240849 := by
  unfold tailWord_1372874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518207107079860264335419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33381885618879627371561117 12518207107079860264335419)
  ·
    refine ⟨18777310660619790396503129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12518207107079860264335419 18777310660619790396503129)
    ·
      refine ⟨14082982995464842797377347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18777310660619790396503129 14082982995464842797377347)
      ·
        refine ⟨21124474493197264196066021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14082982995464842797377347 21124474493197264196066021)
        ·
          refine ⟨3960838967474487036762379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21124474493197264196066021 3960838967474487036762379)
          ·
            refine ⟨5941258451211730555143569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960838967474487036762379 5941258451211730555143569)
            ·
              refine ⟨4455943838408797916357677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5941258451211730555143569 4455943838408797916357677)
              ·
                refine ⟨1670978939403299218634129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4455943838408797916357677 1670978939403299218634129)
                ·
                  refine ⟨1253234204552474413975597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1670978939403299218634129 1253234204552474413975597)
                  ·
                    refine ⟨469962826707177905240849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253234204552474413975597 469962826707177905240849)
                    ·
                      rfl

theorem cell22_1372874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_1372874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372874 prefixEnd_1372874 := by exact prefixLift 1372874
  have htrace : WordTrace (prefixWord ++ tailWord_1372874) baseStart_1372874 baseEnd_1372874 := by
    simpa [prefixWord, tailWord_1372874, baseEnd_1372874] using wordTrace_append hprefix tailTrace_1372874
  have hstable : (prefixWord ++ tailWord_1372874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372874).length < 2 ^ (prefixWord ++ tailWord_1372874).sum := by decide
  have hdescent : baseEnd_1372874 < baseStart_1372874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372887 : List Nat := [1, 1, 3, 2, 1, 5, 3, 6]
def baseStart_1372887 : Nat := 118140960795 + 1372887 * 2 ^ 59
def prefixEnd_1372887 : Nat := 4983230072969 + 3 ^ 40 * 1372887 * 2
def baseEnd_1372887 : Nat := 52218586319205578296201

theorem tailTrace_1372887 : CollatzResearch.WordTrace tailWord_1372887 prefixEnd_1372887 52218586319205578296201 := by
  unfold tailWord_1372887
  simp only [CollatzResearch.WordTrace]
  refine ⟨50073302577272344277564915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33382201718181562851709943 50073302577272344277564915)
  ·
    refine ⟨75109953865908516416347373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50073302577272344277564915 75109953865908516416347373)
    ·
      refine ⟨28166232699715693656130265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75109953865908516416347373 28166232699715693656130265)
      ·
        refine ⟨21124674524786770242097699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28166232699715693656130265 21124674524786770242097699)
        ·
          refine ⟨31687011787180155363146549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21124674524786770242097699 31687011787180155363146549)
          ·
            refine ⟨2970657355048139565294989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31687011787180155363146549 2970657355048139565294989)
            ·
              refine ⟨1113996508143052336985621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2970657355048139565294989 1113996508143052336985621)
              ·
                refine ⟨52218586319205578296201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1113996508143052336985621 52218586319205578296201)
                ·
                  rfl

theorem cell22_1372887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 6].length) (baseStart_1372887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372887 prefixEnd_1372887 := by exact prefixLift 1372887
  have htrace : WordTrace (prefixWord ++ tailWord_1372887) baseStart_1372887 baseEnd_1372887 := by
    simpa [prefixWord, tailWord_1372887, baseEnd_1372887] using wordTrace_append hprefix tailTrace_1372887
  have hstable : (prefixWord ++ tailWord_1372887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372887).length < 2 ^ (prefixWord ++ tailWord_1372887).sum := by decide
  have hdescent : baseEnd_1372887 < baseStart_1372887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372970 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1372970 : Nat := 118140960795 + 1372970 * 2 ^ 59
def prefixEnd_1372970 : Nat := 4983230072969 + 3 ^ 40 * 1372970 * 2
def baseEnd_1372970 : Nat := 469995689469065654840555

theorem tailTrace_1372970 : CollatzResearch.WordTrace tailWord_1372970 prefixEnd_1372970 469995689469065654840555 := by
  unfold tailWord_1372970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519082458992912363209091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33384219890647766301890909 12519082458992912363209091)
  ·
    refine ⟨18778623688489368544813637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12519082458992912363209091 18778623688489368544813637)
    ·
      refine ⟨3520991941591756602152557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18778623688489368544813637 3520991941591756602152557)
      ·
        refine ⟨1320371978096908725807209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3520991941591756602152557 1320371978096908725807209)
        ·
          refine ⟨990278983572681544355407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320371978096908725807209 990278983572681544355407)
          ·
            refine ⟨1485418475359022316533111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990278983572681544355407 1485418475359022316533111)
            ·
              refine ⟨2228127713038533474799667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485418475359022316533111 2228127713038533474799667)
              ·
                refine ⟨3342191569557800212199501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228127713038533474799667 3342191569557800212199501)
                ·
                  refine ⟨1253321838584175079574813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3342191569557800212199501 1253321838584175079574813)
                  ·
                    refine ⟨469995689469065654840555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253321838584175079574813 469995689469065654840555)
                    ·
                      rfl

theorem cell22_1372970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1372970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372970 prefixEnd_1372970 := by exact prefixLift 1372970
  have htrace : WordTrace (prefixWord ++ tailWord_1372970) baseStart_1372970 baseEnd_1372970 := by
    simpa [prefixWord, tailWord_1372970, baseEnd_1372970] using wordTrace_append hprefix tailTrace_1372970
  have hstable : (prefixWord ++ tailWord_1372970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372970).length < 2 ^ (prefixWord ++ tailWord_1372970).sum := by decide
  have hdescent : baseEnd_1372970 < baseStart_1372970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1372975 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 9]
def baseStart_1372975 : Nat := 118140960795 + 1372975 * 2 ^ 59
def prefixEnd_1372975 : Nat := 4983230072969 + 3 ^ 40 * 1372975 * 2
def baseEnd_1372975 : Nat := 469997401071247308465539

theorem tailTrace_1372975 : CollatzResearch.WordTrace tailWord_1372975 prefixEnd_1372975 469997401071247308465539 := by
  unfold tailWord_1372975
  simp only [CollatzResearch.WordTrace]
  refine ⟨50076512200953535306768379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33384341467302356871178919 50076512200953535306768379)
  ·
    refine ⟨75114768301430302960152569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50076512200953535306768379 75114768301430302960152569)
    ·
      refine ⟨56336076226072727220114427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75114768301430302960152569 56336076226072727220114427)
      ·
        refine ⟨84504114339109090830171641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56336076226072727220114427 84504114339109090830171641)
        ·
          refine ⟨63378085754331818122628731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84504114339109090830171641 63378085754331818122628731)
          ·
            refine ⟨95067128631497727183943097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63378085754331818122628731 95067128631497727183943097)
            ·
              refine ⟨71300346473623295387957323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95067128631497727183943097 71300346473623295387957323)
              ·
                refine ⟨106950519710434943081935985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71300346473623295387957323 106950519710434943081935985)
                ·
                  refine ⟨80212889782826207311451989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106950519710434943081935985 80212889782826207311451989)
                  ·
                    refine ⟨469997401071247308465539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 80212889782826207311451989 469997401071247308465539)
                    ·
                      rfl

theorem cell22_1372975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_1372975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1372975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1372975 prefixEnd_1372975 := by exact prefixLift 1372975
  have htrace : WordTrace (prefixWord ++ tailWord_1372975) baseStart_1372975 baseEnd_1372975 := by
    simpa [prefixWord, tailWord_1372975, baseEnd_1372975] using wordTrace_append hprefix tailTrace_1372975
  have hstable : (prefixWord ++ tailWord_1372975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1372975).length < 2 ^ (prefixWord ++ tailWord_1372975).sum := by decide
  have hdescent : baseEnd_1372975 < baseStart_1372975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1372975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373009 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_1373009 : Nat := 118140960795 + 1373009 * 2 ^ 59
def prefixEnd_1373009 : Nat := 4983230072969 + 3 ^ 40 * 1373009 * 2
def baseEnd_1373009 : Nat := 470009039966082553115435

theorem tailTrace_1373009 : CollatzResearch.WordTrace tailWord_1373009 prefixEnd_1373009 470009039966082553115435 := by
  unfold tailWord_1373009
  simp only [CollatzResearch.WordTrace]
  refine ⟨50077752282830359113506081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33385168188553572742337387 50077752282830359113506081)
  ·
    refine ⟨37558314212122769335129561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50077752282830359113506081 37558314212122769335129561)
    ·
      refine ⟨28168735659092077001347171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37558314212122769335129561 28168735659092077001347171)
      ·
        refine ⟨42253103488638115502020757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28168735659092077001347171 42253103488638115502020757)
        ·
          refine ⟨1980614226029911664157223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42253103488638115502020757 1980614226029911664157223)
          ·
            refine ⟨2970921339044867496235835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980614226029911664157223 2970921339044867496235835)
            ·
              refine ⟨4456382008567301244353753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970921339044867496235835 4456382008567301244353753)
              ·
                refine ⟨3342286506425475933265315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4456382008567301244353753 3342286506425475933265315)
                ·
                  refine ⟨5013429759638213899897973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342286506425475933265315 5013429759638213899897973)
                  ·
                    refine ⟨470009039966082553115435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5013429759638213899897973 470009039966082553115435)
                    ·
                      rfl

theorem cell22_1373009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_1373009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373009 prefixEnd_1373009 := by exact prefixLift 1373009
  have htrace : WordTrace (prefixWord ++ tailWord_1373009) baseStart_1373009 baseEnd_1373009 := by
    simpa [prefixWord, tailWord_1373009, baseEnd_1373009] using wordTrace_append hprefix tailTrace_1373009
  have hstable : (prefixWord ++ tailWord_1373009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373009).length < 2 ^ (prefixWord ++ tailWord_1373009).sum := by decide
  have hdescent : baseEnd_1373009 < baseStart_1373009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373028 : List Nat := [2, 3, 1, 1, 4, 3, 2, 2, 4]
def baseStart_1373028 : Nat := 118140960795 + 1373028 * 2 ^ 59
def prefixEnd_1373028 : Nat := 4983230072969 + 3 ^ 40 * 1373028 * 2
def baseEnd_1373028 : Nat := 156671848018124278963459

theorem tailTrace_1373028 : CollatzResearch.WordTrace tailWord_1373028 prefixEnd_1373028 156671848018124278963459 := by
  unfold tailWord_1373028
  simp only [CollatzResearch.WordTrace]
  refine ⟨25039222634880762679223869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33385630179841016905631825 25039222634880762679223869)
  ·
    refine ⟨9389708488080286004708951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25039222634880762679223869 9389708488080286004708951)
    ·
      refine ⟨14084562732120429007063427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9389708488080286004708951 14084562732120429007063427)
      ·
        refine ⟨21126844098180643510595141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14084562732120429007063427 21126844098180643510595141)
        ·
          refine ⟨3961283268408870658236589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21126844098180643510595141 3961283268408870658236589)
          ·
            refine ⟨1485481225653326496838721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3961283268408870658236589 1485481225653326496838721)
            ·
              refine ⟨1114110919239994872629041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485481225653326496838721 1114110919239994872629041)
              ·
                refine ⟨835583189429996154471781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114110919239994872629041 835583189429996154471781)
                ·
                  refine ⟨156671848018124278963459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835583189429996154471781 156671848018124278963459)
                  ·
                    rfl

theorem cell22_1373028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_1373028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373028 prefixEnd_1373028 := by exact prefixLift 1373028
  have htrace : WordTrace (prefixWord ++ tailWord_1373028) baseStart_1373028 baseEnd_1373028 := by
    simpa [prefixWord, tailWord_1373028, baseEnd_1373028] using wordTrace_append hprefix tailTrace_1373028
  have hstable : (prefixWord ++ tailWord_1373028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373028).length < 2 ^ (prefixWord ++ tailWord_1373028).sum := by decide
  have hdescent : baseEnd_1373028 < baseStart_1373028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373037 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1373037 : Nat := 118140960795 + 1373037 * 2 ^ 59
def prefixEnd_1373037 : Nat := 4983230072969 + 3 ^ 40 * 1373037 * 2
def baseEnd_1373037 : Nat := 470018624938299813415349

theorem tailTrace_1373037 : CollatzResearch.WordTrace tailWord_1373037 prefixEnd_1373037 470018624938299813415349 := by
  unfold tailWord_1373037
  simp only [CollatzResearch.WordTrace]
  refine ⟨50078773526728919895525365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33385849017819279930350243 50078773526728919895525365)
  ·
    refine ⟨4694885018130836240205503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50078773526728919895525365 4694885018130836240205503)
    ·
      refine ⟨7042327527196254360308255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694885018130836240205503 7042327527196254360308255)
      ·
        refine ⟨10563491290794381540462383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7042327527196254360308255 10563491290794381540462383)
        ·
          refine ⟨15845236936191572310693575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10563491290794381540462383 15845236936191572310693575)
          ·
            refine ⟨23767855404287358466040363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15845236936191572310693575 23767855404287358466040363)
            ·
              refine ⟨35651783106431037699060545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23767855404287358466040363 35651783106431037699060545)
              ·
                refine ⟨26738837329823278274295409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35651783106431037699060545 26738837329823278274295409)
                ·
                  refine ⟨20054127997367458705721557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26738837329823278274295409 20054127997367458705721557)
                  ·
                    refine ⟨470018624938299813415349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20054127997367458705721557 470018624938299813415349)
                    ·
                      rfl

theorem cell22_1373037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1373037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373037 prefixEnd_1373037 := by exact prefixLift 1373037
  have htrace : WordTrace (prefixWord ++ tailWord_1373037) baseStart_1373037 baseEnd_1373037 := by
    simpa [prefixWord, tailWord_1373037, baseEnd_1373037] using wordTrace_append hprefix tailTrace_1373037
  have hstable : (prefixWord ++ tailWord_1373037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373037).length < 2 ^ (prefixWord ++ tailWord_1373037).sum := by decide
  have hdescent : baseEnd_1373037 < baseStart_1373037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373058 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1373058 : Nat := 118140960795 + 1373058 * 2 ^ 59
def prefixEnd_1373058 : Nat := 4983230072969 + 3 ^ 40 * 1373058 * 2
def baseEnd_1373058 : Nat := 470025813667462758640285

theorem tailTrace_1373058 : CollatzResearch.WordTrace tailWord_1373058 prefixEnd_1373058 470025813667462758640285 := by
  unfold tailWord_1373058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519884864913210120509957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33386359639768560321359885 12519884864913210120509957)
  ·
    refine ⟨2347478412171226897595617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12519884864913210120509957 2347478412171226897595617)
    ·
      refine ⟨1760608809128420173196713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2347478412171226897595617 1760608809128420173196713)
      ·
        refine ⟨1320456606846315129897535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1760608809128420173196713 1320456606846315129897535)
        ·
          refine ⟨1980684910269472694846303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320456606846315129897535 1980684910269472694846303)
          ·
            refine ⟨2971027365404209042269455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980684910269472694846303 2971027365404209042269455)
            ·
              refine ⟨4456541048106313563404183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971027365404209042269455 4456541048106313563404183)
              ·
                refine ⟨6684811572159470345106275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456541048106313563404183 6684811572159470345106275)
                ·
                  refine ⟨10027217358239205517659413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6684811572159470345106275 10027217358239205517659413)
                  ·
                    refine ⟨470025813667462758640285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10027217358239205517659413 470025813667462758640285)
                    ·
                      rfl

theorem cell22_1373058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1373058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373058 prefixEnd_1373058 := by exact prefixLift 1373058
  have htrace : WordTrace (prefixWord ++ tailWord_1373058) baseStart_1373058 baseEnd_1373058 := by
    simpa [prefixWord, tailWord_1373058, baseEnd_1373058] using wordTrace_append hprefix tailTrace_1373058
  have hstable : (prefixWord ++ tailWord_1373058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373058).length < 2 ^ (prefixWord ++ tailWord_1373058).sum := by decide
  have hdescent : baseEnd_1373058 < baseStart_1373058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373146 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_1373146 : Nat := 118140960795 + 1373146 * 2 ^ 59
def prefixEnd_1373146 : Nat := 4983230072969 + 3 ^ 40 * 1373146 * 2
def baseEnd_1373146 : Nat := 156685312621953287480005

theorem tailTrace_1373146 : CollatzResearch.WordTrace tailWord_1373146 prefixEnd_1373146 156685312621953287480005 := by
  unfold tailWord_1373146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12520687270833507877810823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33388499388889354340828861 12520687270833507877810823)
  ·
    refine ⟨18781030906250261816716235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12520687270833507877810823 18781030906250261816716235)
    ·
      refine ⟨28171546359375392725074353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18781030906250261816716235 28171546359375392725074353)
      ·
        refine ⟨21128659769531544543805765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28171546359375392725074353 21128659769531544543805765)
        ·
          refine ⟨3961623706787164601963581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21128659769531544543805765 3961623706787164601963581)
          ·
            refine ⟨1485608890045186725736343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3961623706787164601963581 1485608890045186725736343)
            ·
              refine ⟨2228413335067780088604515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485608890045186725736343 2228413335067780088604515)
              ·
                refine ⟨3342620002601670132906773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228413335067780088604515 3342620002601670132906773)
                ·
                  refine ⟨156685312621953287480005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3342620002601670132906773 156685312621953287480005)
                  ·
                    rfl

theorem cell22_1373146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_1373146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373146 prefixEnd_1373146 := by exact prefixLift 1373146
  have htrace : WordTrace (prefixWord ++ tailWord_1373146) baseStart_1373146 baseEnd_1373146 := by
    simpa [prefixWord, tailWord_1373146, baseEnd_1373146] using wordTrace_append hprefix tailTrace_1373146
  have hstable : (prefixWord ++ tailWord_1373146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373146).length < 2 ^ (prefixWord ++ tailWord_1373146).sum := by decide
  have hdescent : baseEnd_1373146 < baseStart_1373146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373223 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1373223 : Nat := 118140960795 + 1373223 * 2 ^ 59
def prefixEnd_1373223 : Nat := 4983230072969 + 3 ^ 40 * 1373223 * 2
def baseEnd_1373223 : Nat := 470082296539457328264779

theorem tailTrace_1373223 : CollatzResearch.WordTrace tailWord_1373223 prefixEnd_1373223 470082296539457328264779 := by
  unfold tailWord_1373223
  simp only [CollatzResearch.WordTrace]
  refine ⟨50085557504055073661796323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33390371669370049107864215 50085557504055073661796323)
  ·
    refine ⟨75128336256082610492694485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50085557504055073661796323 75128336256082610492694485)
    ·
      refine ⟨1760820381001936183422527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 75128336256082610492694485 1760820381001936183422527)
      ·
        refine ⟨2641230571502904275133791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760820381001936183422527 2641230571502904275133791)
        ·
          refine ⟨3961845857254356412700687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641230571502904275133791 3961845857254356412700687)
          ·
            refine ⟨5942768785881534619051031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961845857254356412700687 5942768785881534619051031)
            ·
              refine ⟨8914153178822301928576547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942768785881534619051031 8914153178822301928576547)
              ·
                refine ⟨13371229768233452892864821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8914153178822301928576547 13371229768233452892864821)
                ·
                  refine ⟨1253552790771886208706077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13371229768233452892864821 1253552790771886208706077)
                  ·
                    refine ⟨470082296539457328264779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253552790771886208706077 470082296539457328264779)
                    ·
                      rfl

theorem cell22_1373223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1373223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373223 prefixEnd_1373223 := by exact prefixLift 1373223
  have htrace : WordTrace (prefixWord ++ tailWord_1373223) baseStart_1373223 baseEnd_1373223 := by
    simpa [prefixWord, tailWord_1373223, baseEnd_1373223] using wordTrace_append hprefix tailTrace_1373223
  have hstable : (prefixWord ++ tailWord_1373223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373223).length < 2 ^ (prefixWord ++ tailWord_1373223).sum := by decide
  have hdescent : baseEnd_1373223 < baseStart_1373223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373234 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1373234 : Nat := 118140960795 + 1373234 * 2 ^ 59
def prefixEnd_1373234 : Nat := 4983230072969 + 3 ^ 40 * 1373234 * 2
def baseEnd_1373234 : Nat := 470086062064256966239745

theorem tailTrace_1373234 : CollatzResearch.WordTrace tailWord_1373234 prefixEnd_1373234 470086062064256966239745 := by
  unfold tailWord_1373234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12521489676753805635111689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33390639138010148360297837 12521489676753805635111689)
  ·
    refine ⟨9391117257565354226333767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12521489676753805635111689 9391117257565354226333767)
    ·
      refine ⟨14086675886348031339500651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9391117257565354226333767 14086675886348031339500651)
      ·
        refine ⟨21130013829522047009250977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14086675886348031339500651 21130013829522047009250977)
        ·
          refine ⟨15847510372141535256938233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21130013829522047009250977 15847510372141535256938233)
          ·
            refine ⟨11885632779106151442703675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15847510372141535256938233 11885632779106151442703675)
            ·
              refine ⟨17828449168659227164055513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11885632779106151442703675 17828449168659227164055513)
              ·
                refine ⟨13371336876494420373041635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17828449168659227164055513 13371336876494420373041635)
                ·
                  refine ⟨20057005314741630559562453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13371336876494420373041635 20057005314741630559562453)
                  ·
                    refine ⟨470086062064256966239745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20057005314741630559562453 470086062064256966239745)
                    ·
                      rfl

theorem cell22_1373234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1373234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373234 prefixEnd_1373234 := by exact prefixLift 1373234
  have htrace : WordTrace (prefixWord ++ tailWord_1373234) baseStart_1373234 baseEnd_1373234 := by
    simpa [prefixWord, tailWord_1373234, baseEnd_1373234] using wordTrace_append hprefix tailTrace_1373234
  have hstable : (prefixWord ++ tailWord_1373234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373234).length < 2 ^ (prefixWord ++ tailWord_1373234).sum := by decide
  have hdescent : baseEnd_1373234 < baseStart_1373234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373240 : List Nat := [2, 1, 2, 1, 5, 2, 2, 3, 1, 3]
def baseStart_1373240 : Nat := 118140960795 + 1373240 * 2 ^ 59
def prefixEnd_1373240 : Nat := 4983230072969 + 3 ^ 40 * 1373240 * 2
def baseEnd_1373240 : Nat := 470088115986874950589727

theorem tailTrace_1373240 : CollatzResearch.WordTrace tailWord_1373240 prefixEnd_1373240 470088115986874950589727 := by
  unfold tailWord_1373240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25043088772496742782582587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33390785029995657043443449 25043088772496742782582587)
  ·
    refine ⟨37564633158745114173873881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25043088772496742782582587 37564633158745114173873881)
    ·
      refine ⟨28173474869058835630405411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37564633158745114173873881 28173474869058835630405411)
      ·
        refine ⟨42260212303588253445608117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28173474869058835630405411 42260212303588253445608117)
        ·
          refine ⟨3961894903461398760525761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42260212303588253445608117 3961894903461398760525761)
          ·
            refine ⟨2971421177596049070394321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3961894903461398760525761 2971421177596049070394321)
            ·
              refine ⟨2228565883197036802795741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2971421177596049070394321 2228565883197036802795741)
              ·
                refine ⟨835712206198888801048403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2228565883197036802795741 835712206198888801048403)
                ·
                  refine ⟨1253568309298333201572605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835712206198888801048403 1253568309298333201572605)
                  ·
                    refine ⟨470088115986874950589727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253568309298333201572605 470088115986874950589727)
                    ·
                      rfl

theorem cell22_1373240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_1373240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373240 prefixEnd_1373240 := by exact prefixLift 1373240
  have htrace : WordTrace (prefixWord ++ tailWord_1373240) baseStart_1373240 baseEnd_1373240 := by
    simpa [prefixWord, tailWord_1373240, baseEnd_1373240] using wordTrace_append hprefix tailTrace_1373240
  have hstable : (prefixWord ++ tailWord_1373240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373240).length < 2 ^ (prefixWord ++ tailWord_1373240).sum := by decide
  have hdescent : baseEnd_1373240 < baseStart_1373240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373296 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 6, 3]
def baseStart_1373296 : Nat := 118140960795 + 1373296 * 2 ^ 59
def prefixEnd_1373296 : Nat := 4983230072969 + 3 ^ 40 * 1373296 * 2
def baseEnd_1373296 : Nat := 470107285931309471189555

theorem tailTrace_1373296 : CollatzResearch.WordTrace tailWord_1373296 prefixEnd_1373296 470107285931309471189555 := by
  unfold tailWord_1373296
  simp only [CollatzResearch.WordTrace]
  refine ⟨25044110016395303564601871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33392146688527071419469161 25044110016395303564601871)
  ·
    refine ⟨37566165024592955346902807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25044110016395303564601871 37566165024592955346902807)
    ·
      refine ⟨56349247536889433020354211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37566165024592955346902807 56349247536889433020354211)
      ·
        refine ⟨84523871305334149530531317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56349247536889433020354211 84523871305334149530531317)
        ·
          refine ⟨7924112934875076518487311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84523871305334149530531317 7924112934875076518487311)
          ·
            refine ⟨11886169402312614777730967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7924112934875076518487311 11886169402312614777730967)
            ·
              refine ⟨17829254103468922166596451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11886169402312614777730967 17829254103468922166596451)
              ·
                refine ⟨26743881155203383249894677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17829254103468922166596451 26743881155203383249894677)
                ·
                  refine ⟨1253619429150158589838813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26743881155203383249894677 1253619429150158589838813)
                  ·
                    refine ⟨470107285931309471189555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253619429150158589838813 470107285931309471189555)
                    ·
                      rfl

theorem cell22_1373296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_1373296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373296 prefixEnd_1373296 := by exact prefixLift 1373296
  have htrace : WordTrace (prefixWord ++ tailWord_1373296) baseStart_1373296 baseEnd_1373296 := by
    simpa [prefixWord, tailWord_1373296, baseEnd_1373296] using wordTrace_append hprefix tailTrace_1373296
  have hstable : (prefixWord ++ tailWord_1373296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373296).length < 2 ^ (prefixWord ++ tailWord_1373296).sum := by decide
  have hdescent : baseEnd_1373296 < baseStart_1373296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373313 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1373313 : Nat := 118140960795 + 1373313 * 2 ^ 59
def prefixEnd_1373313 : Nat := 4983230072969 + 3 ^ 40 * 1373313 * 2
def baseEnd_1373313 : Nat := 470113105378727093514503

theorem tailTrace_1373313 : CollatzResearch.WordTrace tailWord_1373313 prefixEnd_1373313 470113105378727093514503 := by
  unfold tailWord_1373313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50088840073729019032572593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33392560049152679355048395 50088840073729019032572593)
  ·
    refine ⟨37566630055296764274429445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50088840073729019032572593 37566630055296764274429445)
    ·
      refine ⟨7043743135368143301455521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37566630055296764274429445 7043743135368143301455521)
      ·
        refine ⟨5282807351526107476091641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7043743135368143301455521 5282807351526107476091641)
        ·
          refine ⟨3962105513644580607068731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5282807351526107476091641 3962105513644580607068731)
          ·
            refine ⟨5943158270466870910603097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962105513644580607068731 5943158270466870910603097)
            ·
              refine ⟨4457368702850153182952323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5943158270466870910603097 4457368702850153182952323)
              ·
                refine ⟨6686053054275229774428485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4457368702850153182952323 6686053054275229774428485)
                ·
                  refine ⟨1253634947676605582705341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6686053054275229774428485 1253634947676605582705341)
                  ·
                    refine ⟨470113105378727093514503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253634947676605582705341 470113105378727093514503)
                    ·
                      rfl

theorem cell22_1373313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1373313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373313 prefixEnd_1373313 := by exact prefixLift 1373313
  have htrace : WordTrace (prefixWord ++ tailWord_1373313) baseStart_1373313 baseEnd_1373313 := by
    simpa [prefixWord, tailWord_1373313, baseEnd_1373313] using wordTrace_append hprefix tailTrace_1373313
  have hstable : (prefixWord ++ tailWord_1373313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373313).length < 2 ^ (prefixWord ++ tailWord_1373313).sum := by decide
  have hdescent : baseEnd_1373313 < baseStart_1373313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373326 : List Nat := [4, 1, 1, 3, 2, 1, 1, 9]
def baseStart_1373326 : Nat := 118140960795 + 1373326 * 2 ^ 59
def prefixEnd_1373326 : Nat := 4983230072969 + 3 ^ 40 * 1373326 * 2
def baseEnd_1373326 : Nat := 52235283949377710326607

theorem tailTrace_1373326 : CollatzResearch.WordTrace tailWord_1373326 prefixEnd_1373326 52235283949377710326607 := by
  unfold tailWord_1373326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261164277835240281599479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33392876148454614835197221 6261164277835240281599479)
  ·
    refine ⟨9391746416752860422399219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6261164277835240281599479 9391746416752860422399219)
    ·
      refine ⟨14087619625129290633598829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9391746416752860422399219 14087619625129290633598829)
      ·
        refine ⟨5282857359423483987599561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14087619625129290633598829 5282857359423483987599561)
        ·
          refine ⟨3962143019567612990699671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5282857359423483987599561 3962143019567612990699671)
          ·
            refine ⟨5943214529351419486049507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962143019567612990699671 5943214529351419486049507)
            ·
              refine ⟨8914821794027129229074261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943214529351419486049507 8914821794027129229074261)
              ·
                refine ⟨52235283949377710326607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8914821794027129229074261 52235283949377710326607)
                ·
                  rfl

theorem cell22_1373326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_1373326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373326 prefixEnd_1373326 := by exact prefixLift 1373326
  have htrace : WordTrace (prefixWord ++ tailWord_1373326) baseStart_1373326 baseEnd_1373326 := by
    simpa [prefixWord, tailWord_1373326, baseEnd_1373326] using wordTrace_append hprefix tailTrace_1373326
  have hstable : (prefixWord ++ tailWord_1373326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373326).length < 2 ^ (prefixWord ++ tailWord_1373326).sum := by decide
  have hdescent : baseEnd_1373326 < baseStart_1373326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373330 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1373330 : Nat := 118140960795 + 1373330 * 2 ^ 59
def prefixEnd_1373330 : Nat := 4983230072969 + 3 ^ 40 * 1373330 * 2
def baseEnd_1373330 : Nat := 470118924826144715839451

theorem tailTrace_1373330 : CollatzResearch.WordTrace tailWord_1373330 prefixEnd_1373330 470118924826144715839451 := by
  unfold tailWord_1373330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522365028666857733985361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33392973409778287290627629 12522365028666857733985361)
  ·
    refine ⟨9391773771500143300489021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12522365028666857733985361 9391773771500143300489021)
    ·
      refine ⟨3521915164312553737683383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9391773771500143300489021 3521915164312553737683383)
      ·
        refine ⟨5282872746468830606525075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521915164312553737683383 5282872746468830606525075)
        ·
          refine ⟨7924309119703245909787613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282872746468830606525075 7924309119703245909787613)
          ·
            refine ⟨2971615919888717216170355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7924309119703245909787613 2971615919888717216170355)
            ·
              refine ⟨4457423879833075824255533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971615919888717216170355 4457423879833075824255533)
              ·
                refine ⟨1671533954937403434095825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4457423879833075824255533 1671533954937403434095825)
                ·
                  refine ⟨1253650466203052575571869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1671533954937403434095825 1253650466203052575571869)
                  ·
                    refine ⟨470118924826144715839451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253650466203052575571869 470118924826144715839451)
                    ·
                      rfl

theorem cell22_1373330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1373330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373330 prefixEnd_1373330 := by exact prefixLift 1373330
  have htrace : WordTrace (prefixWord ++ tailWord_1373330) baseStart_1373330 baseEnd_1373330 := by
    simpa [prefixWord, tailWord_1373330, baseEnd_1373330] using wordTrace_append hprefix tailTrace_1373330
  have hstable : (prefixWord ++ tailWord_1373330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373330).length < 2 ^ (prefixWord ++ tailWord_1373330).sum := by decide
  have hdescent : baseEnd_1373330 < baseStart_1373330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373366 : List Nat := [5, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1373366 : Nat := 118140960795 + 1373366 * 2 ^ 59
def prefixEnd_1373366 : Nat := 4983230072969 + 3 ^ 40 * 1373366 * 2
def baseEnd_1373366 : Nat := 156710416120617540646447

theorem tailTrace_1373366 : CollatzResearch.WordTrace tailWord_1373366 prefixEnd_1373366 156710416120617540646447 := by
  unfold tailWord_1373366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130673321408563067765747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33393848761691339389501301 3130673321408563067765747)
  ·
    refine ⟨4696009982112844601648621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3130673321408563067765747 4696009982112844601648621)
    ·
      refine ⟨1761003743292316725618233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4696009982112844601648621 1761003743292316725618233)
      ·
        refine ⟨1320752807469237544213675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1761003743292316725618233 1320752807469237544213675)
        ·
          refine ⟨1981129211203856316320513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320752807469237544213675 1981129211203856316320513)
          ·
            refine ⟨1485846908402892237240385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981129211203856316320513 1485846908402892237240385)
            ·
              refine ⟨1114385181302169177930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485846908402892237240385 1114385181302169177930289)
              ·
                refine ⟨835788885976626883447717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114385181302169177930289 835788885976626883447717)
                ·
                  refine ⟨156710416120617540646447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835788885976626883447717 156710416120617540646447)
                  ·
                    rfl

theorem cell22_1373366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1373366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373366 prefixEnd_1373366 := by exact prefixLift 1373366
  have htrace : WordTrace (prefixWord ++ tailWord_1373366) baseStart_1373366 baseEnd_1373366 := by
    simpa [prefixWord, tailWord_1373366, baseEnd_1373366] using wordTrace_append hprefix tailTrace_1373366
  have hstable : (prefixWord ++ tailWord_1373366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373366).length < 2 ^ (prefixWord ++ tailWord_1373366).sum := by decide
  have hdescent : baseEnd_1373366 < baseStart_1373366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373386 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_1373386 : Nat := 118140960795 + 1373386 * 2 ^ 59
def prefixEnd_1373386 : Nat := 4983230072969 + 3 ^ 40 * 1373386 * 2
def baseEnd_1373386 : Nat := 470138094770579236439279

theorem tailTrace_1373386 : CollatzResearch.WordTrace tailWord_1373386 prefixEnd_1373386 470138094770579236439279 := by
  unfold tailWord_1373386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522875650616138124995003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33394335068309701666653341 12522875650616138124995003)
  ·
    refine ⟨18784313475924207187492505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12522875650616138124995003 18784313475924207187492505)
    ·
      refine ⟨14088235106943155390619379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18784313475924207187492505 14088235106943155390619379)
      ·
        refine ⟨21132352660414733085929069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14088235106943155390619379 21132352660414733085929069)
        ·
          refine ⟨7924632247655524907223401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21132352660414733085929069 7924632247655524907223401)
          ·
            refine ⟨5943474185741643680417551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7924632247655524907223401 5943474185741643680417551)
            ·
              refine ⟨8915211278612465520626327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943474185741643680417551 8915211278612465520626327)
              ·
                refine ⟨13372816917918698280939491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8915211278612465520626327 13372816917918698280939491)
                ·
                  refine ⟨20059225376878047421409237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13372816917918698280939491 20059225376878047421409237)
                  ·
                    refine ⟨470138094770579236439279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20059225376878047421409237 470138094770579236439279)
                    ·
                      rfl

theorem cell22_1373386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_1373386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373386 prefixEnd_1373386 := by exact prefixLift 1373386
  have htrace : WordTrace (prefixWord ++ tailWord_1373386) baseStart_1373386 baseEnd_1373386 := by
    simpa [prefixWord, tailWord_1373386, baseEnd_1373386] using wordTrace_append hprefix tailTrace_1373386
  have hstable : (prefixWord ++ tailWord_1373386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373386).length < 2 ^ (prefixWord ++ tailWord_1373386).sum := by decide
  have hdescent : baseEnd_1373386 < baseStart_1373386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373416 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 8]
def baseStart_1373416 : Nat := 118140960795 + 1373416 * 2 ^ 59
def prefixEnd_1373416 : Nat := 4983230072969 + 3 ^ 40 * 1373416 * 2
def baseEnd_1373416 : Nat := 156716121461223052729729

theorem tailTrace_1373416 : CollatzResearch.WordTrace tailWord_1373416 prefixEnd_1373416 156716121461223052729729 := by
  unfold tailWord_1373416
  simp only [CollatzResearch.WordTrace]
  refine ⟨25046298396177933811786051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33395064528237245082381401 25046298396177933811786051)
  ·
    refine ⟨37569447594266900717679077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25046298396177933811786051 37569447594266900717679077)
    ·
      refine ⟨7044271423925043884564827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37569447594266900717679077 7044271423925043884564827)
      ·
        refine ⟨10566407135887565826847241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7044271423925043884564827 10566407135887565826847241)
        ·
          refine ⟨7924805351915674370135431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10566407135887565826847241 7924805351915674370135431)
          ·
            refine ⟨11887208027873511555203147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7924805351915674370135431 11887208027873511555203147)
            ·
              refine ⟨17830812041810267332804721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11887208027873511555203147 17830812041810267332804721)
              ·
                refine ⟨13373109031357700499603541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17830812041810267332804721 13373109031357700499603541)
                ·
                  refine ⟨156716121461223052729729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13373109031357700499603541 156716121461223052729729)
                  ·
                    rfl

theorem cell22_1373416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_1373416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373416 prefixEnd_1373416 := by exact prefixLift 1373416
  have htrace : WordTrace (prefixWord ++ tailWord_1373416) baseStart_1373416 baseEnd_1373416 := by
    simpa [prefixWord, tailWord_1373416, baseEnd_1373416] using wordTrace_append hprefix tailTrace_1373416
  have hstable : (prefixWord ++ tailWord_1373416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373416).length < 2 ^ (prefixWord ++ tailWord_1373416).sum := by decide
  have hdescent : baseEnd_1373416 < baseStart_1373416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373433 : List Nat := [1, 2, 1, 3, 1, 1, 3, 6, 4]
def baseStart_1373433 : Nat := 118140960795 + 1373433 * 2 ^ 59
def prefixEnd_1373433 : Nat := 4983230072969 + 3 ^ 40 * 1373433 * 2
def baseEnd_1373433 : Nat := 156718061277028926838045

theorem tailTrace_1373433 : CollatzResearch.WordTrace tailWord_1373433 prefixEnd_1373433 156718061277028926838045 := by
  unfold tailWord_1373433
  simp only [CollatzResearch.WordTrace]
  refine ⟨50093216833294279526940953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33395477888862853017960635 50093216833294279526940953)
  ·
    refine ⟨37569912624970709645205715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50093216833294279526940953 37569912624970709645205715)
    ·
      refine ⟨56354868937456064467808573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37569912624970709645205715 56354868937456064467808573)
      ·
        refine ⟨21133075851546024175428215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56354868937456064467808573 21133075851546024175428215)
        ·
          refine ⟨31699613777319036263142323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21133075851546024175428215 31699613777319036263142323)
          ·
            refine ⟨47549420665978554394713485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31699613777319036263142323 47549420665978554394713485)
            ·
              refine ⟨17831032749741957898017557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47549420665978554394713485 17831032749741957898017557)
              ·
                refine ⟨835829660144154276469573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17831032749741957898017557 835829660144154276469573)
                ·
                  refine ⟨156718061277028926838045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835829660144154276469573 156718061277028926838045)
                  ·
                    rfl

theorem cell22_1373433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_1373433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373433 prefixEnd_1373433 := by exact prefixLift 1373433
  have htrace : WordTrace (prefixWord ++ tailWord_1373433) baseStart_1373433 baseEnd_1373433 := by
    simpa [prefixWord, tailWord_1373433, baseEnd_1373433] using wordTrace_append hprefix tailTrace_1373433
  have hstable : (prefixWord ++ tailWord_1373433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373433).length < 2 ^ (prefixWord ++ tailWord_1373433).sum := by decide
  have hdescent : baseEnd_1373433 < baseStart_1373433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373463 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 2, 4]
def baseStart_1373463 : Nat := 118140960795 + 1373463 * 2 ^ 59
def prefixEnd_1373463 : Nat := 4983230072969 + 3 ^ 40 * 1373463 * 2
def baseEnd_1373463 : Nat := 470164453444176702264043

theorem tailTrace_1373463 : CollatzResearch.WordTrace tailWord_1373463 prefixEnd_1373463 470164453444176702264043 := by
  unfold tailWord_1373463
  simp only [CollatzResearch.WordTrace]
  refine ⟨50094311023185594650533043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33396207348790396433688695 50094311023185594650533043)
  ·
    refine ⟨75141466534778391975799565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50094311023185594650533043 75141466534778391975799565)
    ·
      refine ⟨28178049950541896990924837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75141466534778391975799565 28178049950541896990924837)
      ·
        refine ⟨5283384365726605685798407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28178049950541896990924837 5283384365726605685798407)
        ·
          refine ⟨7925076548589908528697611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283384365726605685798407 7925076548589908528697611)
          ·
            refine ⟨11887614822884862793046417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7925076548589908528697611 11887614822884862793046417)
            ·
              refine ⟨8915711117163647094784813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11887614822884862793046417 8915711117163647094784813)
              ·
                refine ⟨3343391668936367660544305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8915711117163647094784813 3343391668936367660544305)
                ·
                  refine ⟨2507543751702275745408229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343391668936367660544305 2507543751702275745408229)
                  ·
                    refine ⟨470164453444176702264043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2507543751702275745408229 470164453444176702264043)
                    ·
                      rfl

theorem cell22_1373463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_1373463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373463 prefixEnd_1373463 := by exact prefixLift 1373463
  have htrace : WordTrace (prefixWord ++ tailWord_1373463) baseStart_1373463 baseEnd_1373463 := by
    simpa [prefixWord, tailWord_1373463, baseEnd_1373463] using wordTrace_append hprefix tailTrace_1373463
  have hstable : (prefixWord ++ tailWord_1373463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373463).length < 2 ^ (prefixWord ++ tailWord_1373463).sum := by decide
  have hdescent : baseEnd_1373463 < baseStart_1373463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373480 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1373480 : Nat := 118140960795 + 1373480 * 2 ^ 59
def prefixEnd_1373480 : Nat := 4983230072969 + 3 ^ 40 * 1373480 * 2
def baseEnd_1373480 : Nat := 470170272891594324588991

theorem tailTrace_1373480 : CollatzResearch.WordTrace tailWord_1373480 prefixEnd_1373480 470170272891594324588991 := by
  unfold tailWord_1373480
  simp only [CollatzResearch.WordTrace]
  refine ⟨25047465532062003276950947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33396620709416004369267929 25047465532062003276950947)
  ·
    refine ⟨37571198298093004915426421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25047465532062003276950947 37571198298093004915426421)
    ·
      refine ⟨3522299840446219210821227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37571198298093004915426421 3522299840446219210821227)
      ·
        refine ⟨5283449760669328816231841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3522299840446219210821227 5283449760669328816231841)
        ·
          refine ⟨3962587320501996612173881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5283449760669328816231841 3962587320501996612173881)
          ·
            refine ⟨2971940490376497459130411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3962587320501996612173881 2971940490376497459130411)
            ·
              refine ⟨4457910735564746188695617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971940490376497459130411 4457910735564746188695617)
              ·
                refine ⟨3343433051673559641521713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4457910735564746188695617 3343433051673559641521713)
                ·
                  refine ⟨2507574788755169731141285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343433051673559641521713 2507574788755169731141285)
                  ·
                    refine ⟨470170272891594324588991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2507574788755169731141285 470170272891594324588991)
                    ·
                      rfl

theorem cell22_1373480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1373480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373480 prefixEnd_1373480 := by exact prefixLift 1373480
  have htrace : WordTrace (prefixWord ++ tailWord_1373480) baseStart_1373480 baseEnd_1373480 := by
    simpa [prefixWord, tailWord_1373480, baseEnd_1373480] using wordTrace_append hprefix tailTrace_1373480
  have hstable : (prefixWord ++ tailWord_1373480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373480).length < 2 ^ (prefixWord ++ tailWord_1373480).sum := by decide
  have hdescent : baseEnd_1373480 < baseStart_1373480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373540 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1373540 : Nat := 118140960795 + 1373540 * 2 ^ 59
def prefixEnd_1373540 : Nat := 4983230072969 + 3 ^ 40 * 1373540 * 2
def baseEnd_1373540 : Nat := 156730270705924722696269

theorem tailTrace_1373540 : CollatzResearch.WordTrace tailWord_1373540 prefixEnd_1373540 156730270705924722696269 := by
  unfold tailWord_1373540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25048559721953318400543037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33398079629271091200724049 25048559721953318400543037)
  ·
    refine ⟨9393209895732494400203639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25048559721953318400543037 9393209895732494400203639)
    ·
      refine ⟨14089814843598741600305459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9393209895732494400203639 14089814843598741600305459)
      ·
        refine ⟨21134722265398112400458189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14089814843598741600305459 21134722265398112400458189)
        ·
          refine ⟨7925520849524292150171821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21134722265398112400458189 7925520849524292150171821)
          ·
            refine ⟨2972070318571609556314433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7925520849524292150171821 2972070318571609556314433)
            ·
              refine ⟨2229052738928707167235825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2972070318571609556314433 2229052738928707167235825)
              ·
                refine ⟨1671789554196530375426869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2229052738928707167235825 1671789554196530375426869)
                ·
                  refine ⟨156730270705924722696269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1671789554196530375426869 156730270705924722696269)
                  ·
                    rfl

theorem cell22_1373540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1373540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373540 prefixEnd_1373540 := by exact prefixLift 1373540
  have htrace : WordTrace (prefixWord ++ tailWord_1373540) baseStart_1373540 baseEnd_1373540 := by
    simpa [prefixWord, tailWord_1373540, baseEnd_1373540] using wordTrace_append hprefix tailTrace_1373540
  have hstable : (prefixWord ++ tailWord_1373540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373540).length < 2 ^ (prefixWord ++ tailWord_1373540).sum := by decide
  have hdescent : baseEnd_1373540 < baseStart_1373540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373544 : List Nat := [2, 1, 4, 2, 3, 1, 1, 4, 1, 3]
def baseStart_1373544 : Nat := 118140960795 + 1373544 * 2 ^ 59
def prefixEnd_1373544 : Nat := 4983230072969 + 3 ^ 40 * 1373544 * 2
def baseEnd_1373544 : Nat := 470192181399519490988795

theorem tailTrace_1373544 : CollatzResearch.WordTrace tailWord_1373544 prefixEnd_1373544 470192181399519490988795 := by
  unfold tailWord_1373544
  simp only [CollatzResearch.WordTrace]
  refine ⟨25048632667946072742115843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33398176890594763656154457 25048632667946072742115843)
  ·
    refine ⟨37572949001919109113173765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25048632667946072742115843 37572949001919109113173765)
    ·
      refine ⟨7044927937859832958720081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37572949001919109113173765 7044927937859832958720081)
      ·
        refine ⟨5283695953394874719040061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7044927937859832958720081 5283695953394874719040061)
        ·
          refine ⟨1981385982523078019640023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5283695953394874719040061 1981385982523078019640023)
          ·
            refine ⟨2972078973784617029460035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981385982523078019640023 2972078973784617029460035)
            ·
              refine ⟨4458118460676925544190053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972078973784617029460035 4458118460676925544190053)
              ·
                refine ⟨835897211376923539535635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4458118460676925544190053 835897211376923539535635)
                ·
                  refine ⟨1253845817065385309303453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835897211376923539535635 1253845817065385309303453)
                  ·
                    refine ⟨470192181399519490988795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253845817065385309303453 470192181399519490988795)
                    ·
                      rfl

theorem cell22_1373544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_1373544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373544 prefixEnd_1373544 := by exact prefixLift 1373544
  have htrace : WordTrace (prefixWord ++ tailWord_1373544) baseStart_1373544 baseEnd_1373544 := by
    simpa [prefixWord, tailWord_1373544, baseEnd_1373544] using wordTrace_append hprefix tailTrace_1373544
  have hstable : (prefixWord ++ tailWord_1373544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373544).length < 2 ^ (prefixWord ++ tailWord_1373544).sum := by decide
  have hdescent : baseEnd_1373544 < baseStart_1373544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373553 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_1373553 : Nat := 118140960795 + 1373553 * 2 ^ 59
def prefixEnd_1373553 : Nat := 4983230072969 + 3 ^ 40 * 1373553 * 2
def baseEnd_1373553 : Nat := 470195262283446467513767

theorem tailTrace_1373553 : CollatzResearch.WordTrace tailWord_1373553 prefixEnd_1373553 470195262283446467513767 := by
  unfold tailWord_1373553
  simp only [CollatzResearch.WordTrace]
  refine ⟨50097593592859540021309313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33398395728573026680872875 50097593592859540021309313)
  ·
    refine ⟨37573195194644655015981985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50097593592859540021309313 37573195194644655015981985)
    ·
      refine ⟨28179896395983491261986489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37573195194644655015981985 28179896395983491261986489)
      ·
        refine ⟨21134922296987618446489867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28179896395983491261986489 21134922296987618446489867)
        ·
          refine ⟨31702383445481427669734801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21134922296987618446489867 31702383445481427669734801)
          ·
            refine ⟨23776787584111070752301101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31702383445481427669734801 23776787584111070752301101)
            ·
              refine ⟨8916295344041651532112913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23776787584111070752301101 8916295344041651532112913)
              ·
                refine ⟨6687221508031238649084685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8916295344041651532112913 6687221508031238649084685)
                ·
                  refine ⟨2507708065511714493406757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6687221508031238649084685 2507708065511714493406757)
                  ·
                    refine ⟨470195262283446467513767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2507708065511714493406757 470195262283446467513767)
                    ·
                      rfl

theorem cell22_1373553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_1373553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373553 prefixEnd_1373553 := by exact prefixLift 1373553
  have htrace : WordTrace (prefixWord ++ tailWord_1373553) baseStart_1373553 baseEnd_1373553 := by
    simpa [prefixWord, tailWord_1373553, baseEnd_1373553] using wordTrace_append hprefix tailTrace_1373553
  have hstable : (prefixWord ++ tailWord_1373553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373553).length < 2 ^ (prefixWord ++ tailWord_1373553).sum := by decide
  have hdescent : baseEnd_1373553 < baseStart_1373553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373600 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 4, 3]
def baseStart_1373600 : Nat := 118140960795 + 1373600 * 2 ^ 59
def prefixEnd_1373600 : Nat := 4983230072969 + 3 ^ 40 * 1373600 * 2
def baseEnd_1373600 : Nat := 470211351343954011588623

theorem tailTrace_1373600 : CollatzResearch.WordTrace tailWord_1373600 prefixEnd_1373600 470211351343954011588623 := by
  unfold tailWord_1373600
  simp only [CollatzResearch.WordTrace]
  refine ⟨25049653911844633524135127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33399538549126178032180169 25049653911844633524135127)
  ·
    refine ⟨37574480867766950286202691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25049653911844633524135127 37574480867766950286202691)
    ·
      refine ⟨56361721301650425429304037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37574480867766950286202691 56361721301650425429304037)
      ·
        refine ⟨10567822744059454767994507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56361721301650425429304037 10567822744059454767994507)
        ·
          refine ⟨15851734116089182151991761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10567822744059454767994507 15851734116089182151991761)
          ·
            refine ⟨11888800587066886613993821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15851734116089182151991761 11888800587066886613993821)
            ·
              refine ⟨4458300220150082480247683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11888800587066886613993821 4458300220150082480247683)
              ·
                refine ⟨6687450330225123720371525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458300220150082480247683 6687450330225123720371525)
                ·
                  refine ⟨1253896936917210697569661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6687450330225123720371525 1253896936917210697569661)
                  ·
                    refine ⟨470211351343954011588623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253896936917210697569661 470211351343954011588623)
                    ·
                      rfl

theorem cell22_1373600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_1373600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373600 prefixEnd_1373600 := by exact prefixLift 1373600
  have htrace : WordTrace (prefixWord ++ tailWord_1373600) baseStart_1373600 baseEnd_1373600 := by
    simpa [prefixWord, tailWord_1373600, baseEnd_1373600] using wordTrace_append hprefix tailTrace_1373600
  have hstable : (prefixWord ++ tailWord_1373600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373600).length < 2 ^ (prefixWord ++ tailWord_1373600).sum := by decide
  have hdescent : baseEnd_1373600 < baseStart_1373600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373602 : List Nat := [3, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1373602 : Nat := 118140960795 + 1373602 * 2 ^ 59
def prefixEnd_1373602 : Nat := 4983230072969 + 3 ^ 40 * 1373602 * 2
def baseEnd_1373602 : Nat := 156737345328275557679539

theorem tailTrace_1373602 : CollatzResearch.WordTrace tailWord_1373602 prefixEnd_1373602 156737345328275557679539 := by
  unfold tailWord_1373602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12524845192420505347460765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33399587179788014259895373 12524845192420505347460765)
  ·
    refine ⟨4696816947157689505297787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12524845192420505347460765 4696816947157689505297787)
    ·
      refine ⟨7045225420736534257946681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4696816947157689505297787 7045225420736534257946681)
      ·
        refine ⟨5283919065552400693460011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7045225420736534257946681 5283919065552400693460011)
        ·
          refine ⟨7925878598328601040190017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283919065552400693460011 7925878598328601040190017)
          ·
            refine ⟨5944408948746450780142513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925878598328601040190017 5944408948746450780142513)
            ·
              refine ⟨4458306711559838085106885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5944408948746450780142513 4458306711559838085106885)
              ·
                refine ⟨835932508417469640957541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4458306711559838085106885 835932508417469640957541)
                ·
                  refine ⟨156737345328275557679539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 835932508417469640957541 156737345328275557679539)
                  ·
                    rfl

theorem cell22_1373602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1373602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373602 prefixEnd_1373602 := by exact prefixLift 1373602
  have htrace : WordTrace (prefixWord ++ tailWord_1373602) baseStart_1373602 baseEnd_1373602 := by
    simpa [prefixWord, tailWord_1373602, baseEnd_1373602] using wordTrace_append hprefix tailTrace_1373602
  have hstable : (prefixWord ++ tailWord_1373602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373602).length < 2 ^ (prefixWord ++ tailWord_1373602).sum := by decide
  have hdescent : baseEnd_1373602 < baseStart_1373602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373673 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_1373673 : Nat := 118140960795 + 1373673 * 2 ^ 59
def prefixEnd_1373673 : Nat := 4983230072969 + 3 ^ 40 * 1373673 * 2
def baseEnd_1373673 : Nat := 470236340735806154513399

theorem tailTrace_1373673 : CollatzResearch.WordTrace tailWord_1373673 prefixEnd_1373673 470236340735806154513399 := by
  unfold tailWord_1373673
  simp only [CollatzResearch.WordTrace]
  refine ⟨50101970352424800515677673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33401313568283200343785115 50101970352424800515677673)
  ·
    refine ⟨37576477764318600386758255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50101970352424800515677673 37576477764318600386758255)
    ·
      refine ⟨56364716646477900580137383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37576477764318600386758255 56364716646477900580137383)
      ·
        refine ⟨84547074969716850870206075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56364716646477900580137383 84547074969716850870206075)
        ·
          refine ⟨126820612454575276305309113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84547074969716850870206075 126820612454575276305309113)
          ·
            refine ⟨95115459340931457228981835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126820612454575276305309113 95115459340931457228981835)
            ·
              refine ⟨142673189011397185843472753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95115459340931457228981835 142673189011397185843472753)
              ·
                refine ⟨107004891758547889382604565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142673189011397185843472753 107004891758547889382604565)
                ·
                  refine ⟨5015854301181932314809589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107004891758547889382604565 5015854301181932314809589)
                  ·
                    refine ⟨470236340735806154513399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5015854301181932314809589 470236340735806154513399)
                    ·
                      rfl

theorem cell22_1373673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_1373673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373673 prefixEnd_1373673 := by exact prefixLift 1373673
  have htrace : WordTrace (prefixWord ++ tailWord_1373673) baseStart_1373673 baseEnd_1373673 := by
    simpa [prefixWord, tailWord_1373673, baseEnd_1373673] using wordTrace_append hprefix tailTrace_1373673
  have hstable : (prefixWord ++ tailWord_1373673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373673).length < 2 ^ (prefixWord ++ tailWord_1373673).sum := by decide
  have hdescent : baseEnd_1373673 < baseStart_1373673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373756 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_1373756 : Nat := 118140960795 + 1373756 * 2 ^ 59
def prefixEnd_1373756 : Nat := 4983230072969 + 3 ^ 40 * 1373756 * 2
def baseEnd_1373756 : Nat := 470264753332021604688145

theorem tailTrace_1373756 : CollatzResearch.WordTrace tailWord_1373756 prefixEnd_1373756 470264753332021604688145 := by
  unfold tailWord_1373756
  simp only [CollatzResearch.WordTrace]
  refine ⟨25052498805562052845474561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33403331740749403793966081 25052498805562052845474561)
  ·
    refine ⟨18789374104171539634105921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25052498805562052845474561 18789374104171539634105921)
    ·
      refine ⟨14092030578128654725579441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18789374104171539634105921 14092030578128654725579441)
      ·
        refine ⟨10569022933596491044184581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14092030578128654725579441 10569022933596491044184581)
        ·
          refine ⟨1981691800049342070784609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10569022933596491044184581 1981691800049342070784609)
          ·
            refine ⟨1486268850037006553088457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981691800049342070784609 1486268850037006553088457)
            ·
              refine ⟨1114701637527754914816343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486268850037006553088457 1114701637527754914816343)
              ·
                refine ⟨1672052456291632372224515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114701637527754914816343 1672052456291632372224515)
                ·
                  refine ⟨2508078684437448558336773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672052456291632372224515 2508078684437448558336773)
                  ·
                    refine ⟨470264753332021604688145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508078684437448558336773 470264753332021604688145)
                    ·
                      rfl

theorem cell22_1373756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_1373756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373756 prefixEnd_1373756 := by exact prefixLift 1373756
  have htrace : WordTrace (prefixWord ++ tailWord_1373756) baseStart_1373756 baseEnd_1373756 := by
    simpa [prefixWord, tailWord_1373756, baseEnd_1373756] using wordTrace_append hprefix tailTrace_1373756
  have hstable : (prefixWord ++ tailWord_1373756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373756).length < 2 ^ (prefixWord ++ tailWord_1373756).sum := by decide
  have hdescent : baseEnd_1373756 < baseStart_1373756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1373902 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1373902 : Nat := 118140960795 + 1373902 * 2 ^ 59
def prefixEnd_1373902 : Nat := 4983230072969 + 3 ^ 40 * 1373902 * 2
def baseEnd_1373902 : Nat := 470314732115725890537697

theorem tailTrace_1373902 : CollatzResearch.WordTrace tailWord_1373902 prefixEnd_1373902 470314732115725890537697 := by
  unfold tailWord_1373902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6263790333574396578220495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33406881779063448417175973 6263790333574396578220495)
  ·
    refine ⟨9395685500361594867330743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6263790333574396578220495 9395685500361594867330743)
    ·
      refine ⟨14093528250542392300996115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395685500361594867330743 14093528250542392300996115)
      ·
        refine ⟨21140292375813588451494173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14093528250542392300996115 21140292375813588451494173)
        ·
          refine ⟨7927609640930095669310315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21140292375813588451494173 7927609640930095669310315)
          ·
            refine ⟨11891414461395143503965473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7927609640930095669310315 11891414461395143503965473)
            ·
              refine ⟨8918560846046357627974105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11891414461395143503965473 8918560846046357627974105)
              ·
                refine ⟨6688920634534768220980579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8918560846046357627974105 6688920634534768220980579)
                ·
                  refine ⟨10033380951802152331470869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6688920634534768220980579 10033380951802152331470869)
                  ·
                    refine ⟨470314732115725890537697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10033380951802152331470869 470314732115725890537697)
                    ·
                      rfl

theorem cell22_1373902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1373902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1373902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1373902 prefixEnd_1373902 := by exact prefixLift 1373902
  have htrace : WordTrace (prefixWord ++ tailWord_1373902) baseStart_1373902 baseEnd_1373902 := by
    simpa [prefixWord, tailWord_1373902, baseEnd_1373902] using wordTrace_append hprefix tailTrace_1373902
  have hstable : (prefixWord ++ tailWord_1373902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1373902).length < 2 ^ (prefixWord ++ tailWord_1373902).sum := by decide
  have hdescent : baseEnd_1373902 < baseStart_1373902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1373902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374007 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 6]
def baseStart_1374007 : Nat := 118140960795 + 1374007 * 2 ^ 59
def prefixEnd_1374007 : Nat := 4983230072969 + 3 ^ 40 * 1374007 * 2
def baseEnd_1374007 : Nat := 156783558587180205554125

theorem tailTrace_1374007 : CollatzResearch.WordTrace tailWord_1374007 prefixEnd_1374007 156783558587180205554125 := by
  unfold tailWord_1374007
  simp only [CollatzResearch.WordTrace]
  refine ⟨50114152333214775558336275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33409434888809850372224183 50114152333214775558336275)
  ·
    refine ⟨75171228499822163337504413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50114152333214775558336275 75171228499822163337504413)
    ·
      refine ⟨28189210687433311251564155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75171228499822163337504413 28189210687433311251564155)
      ·
        refine ⟨42283816031149966877346233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28189210687433311251564155 42283816031149966877346233)
        ·
          refine ⟨31712862023362475158009675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42283816031149966877346233 31712862023362475158009675)
          ·
            refine ⟨47569293035043712737014513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31712862023362475158009675 47569293035043712737014513)
            ·
              refine ⟨35676969776282784552760885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47569293035043712737014513 35676969776282784552760885)
              ·
                refine ⟨3344715916526511051821333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35676969776282784552760885 3344715916526511051821333)
                ·
                  refine ⟨156783558587180205554125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3344715916526511051821333 156783558587180205554125)
                  ·
                    rfl

theorem cell22_1374007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 6].length) (baseStart_1374007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374007 prefixEnd_1374007 := by exact prefixLift 1374007
  have htrace : WordTrace (prefixWord ++ tailWord_1374007) baseStart_1374007 baseEnd_1374007 := by
    simpa [prefixWord, tailWord_1374007, baseEnd_1374007] using wordTrace_append hprefix tailTrace_1374007
  have hstable : (prefixWord ++ tailWord_1374007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374007).length < 2 ^ (prefixWord ++ tailWord_1374007).sum := by decide
  have hdescent : baseEnd_1374007 < baseStart_1374007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374013 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 5]
def baseStart_1374013 : Nat := 118140960795 + 1374013 * 2 ^ 59
def prefixEnd_1374013 : Nat := 4983230072969 + 3 ^ 40 * 1374013 * 2
def baseEnd_1374013 : Nat := 156784243228052867004119

theorem tailTrace_1374013 : CollatzResearch.WordTrace tailWord_1374013 prefixEnd_1374013 156784243228052867004119 := by
  unfold tailWord_1374013
  simp only [CollatzResearch.WordTrace]
  refine ⟨50114371171193038583054693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33409580780795359055369795 50114371171193038583054693)
  ·
    refine ⟨9396444594598694734322755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50114371171193038583054693 9396444594598694734322755)
    ·
      refine ⟨14094666891898042101484133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396444594598694734322755 14094666891898042101484133)
      ·
        refine ⟨2642750042230882894028275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14094666891898042101484133 2642750042230882894028275)
        ·
          refine ⟨3964125063346324341042413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642750042230882894028275 3964125063346324341042413)
          ·
            refine ⟨1486546898754871627890905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3964125063346324341042413 1486546898754871627890905)
            ·
              refine ⟨1114910174066153720918179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486546898754871627890905 1114910174066153720918179)
              ·
                refine ⟨1672365261099230581377269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114910174066153720918179 1672365261099230581377269)
                ·
                  refine ⟨156784243228052867004119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1672365261099230581377269 156784243228052867004119)
                  ·
                    rfl

theorem cell22_1374013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_1374013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374013 prefixEnd_1374013 := by exact prefixLift 1374013
  have htrace : WordTrace (prefixWord ++ tailWord_1374013) baseStart_1374013 baseEnd_1374013 := by
    simpa [prefixWord, tailWord_1374013, baseEnd_1374013] using wordTrace_append hprefix tailTrace_1374013
  have hstable : (prefixWord ++ tailWord_1374013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374013).length < 2 ^ (prefixWord ++ tailWord_1374013).sum := by decide
  have hdescent : baseEnd_1374013 < baseStart_1374013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374052 : List Nat := [2, 3, 1, 1, 15]
def baseStart_1374052 : Nat := 118140960795 + 1374052 * 2 ^ 59
def prefixEnd_1374052 : Nat := 4983230072969 + 3 ^ 40 * 1374052 * 2
def baseEnd_1374052 : Nat := 1935662881404014400359

theorem tailTrace_1374052 : CollatzResearch.WordTrace tailWord_1374052 prefixEnd_1374052 1935662881404014400359 := by
  unfold tailWord_1374052
  simp only [CollatzResearch.WordTrace]
  refine ⟨25057896809025874121862205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33410529078701165495816273 25057896809025874121862205)
  ·
    refine ⟨9396711303384702795698327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25057896809025874121862205 9396711303384702795698327)
    ·
      refine ⟨14095066955077054193547491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9396711303384702795698327 14095066955077054193547491)
      ·
        refine ⟨21142600432615581290321237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14095066955077054193547491 21142600432615581290321237)
        ·
          refine ⟨1935662881404014400359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 21142600432615581290321237 1935662881404014400359)
          ·
            rfl

theorem cell22_1374052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 15].length) (baseStart_1374052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374052 prefixEnd_1374052 := by exact prefixLift 1374052
  have htrace : WordTrace (prefixWord ++ tailWord_1374052) baseStart_1374052 baseEnd_1374052 := by
    simpa [prefixWord, tailWord_1374052, baseEnd_1374052] using wordTrace_append hprefix tailTrace_1374052
  have hstable : (prefixWord ++ tailWord_1374052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374052).length < 2 ^ (prefixWord ++ tailWord_1374052).sum := by decide
  have hdescent : baseEnd_1374052 < baseStart_1374052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374067 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 2, 7]
def baseStart_1374067 : Nat := 118140960795 + 1374067 * 2 ^ 59
def prefixEnd_1374067 : Nat := 4983230072969 + 3 ^ 40 * 1374067 * 2
def baseEnd_1374067 : Nat := 470371214987720460162191

theorem tailTrace_1374067 : CollatzResearch.WordTrace tailWord_1374067 prefixEnd_1374067 470371214987720460162191 := by
  unfold tailWord_1374067
  simp only [CollatzResearch.WordTrace]
  refine ⟨50116340712997405805520455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33410893808664937203680303 50116340712997405805520455)
  ·
    refine ⟨75174511069496108708280683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50116340712997405805520455 75174511069496108708280683)
    ·
      refine ⟨112761766604244163062421025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75174511069496108708280683 112761766604244163062421025)
      ·
        refine ⟨84571324953183122296815769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112761766604244163062421025 84571324953183122296815769)
        ·
          refine ⟨63428493714887341722611827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84571324953183122296815769 63428493714887341722611827)
          ·
            refine ⟨95142740572331012583917741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63428493714887341722611827 95142740572331012583917741)
            ·
              refine ⟨35678527714624129718969153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95142740572331012583917741 35678527714624129718969153)
              ·
                refine ⟨26758895785968097289226865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35678527714624129718969153 26758895785968097289226865)
                ·
                  refine ⟨20069171839476072966920149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26758895785968097289226865 20069171839476072966920149)
                  ·
                    refine ⟨470371214987720460162191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20069171839476072966920149 470371214987720460162191)
                    ·
                      rfl

theorem cell22_1374067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_1374067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374067 prefixEnd_1374067 := by exact prefixLift 1374067
  have htrace : WordTrace (prefixWord ++ tailWord_1374067) baseStart_1374067 baseEnd_1374067 := by
    simpa [prefixWord, tailWord_1374067, baseEnd_1374067] using wordTrace_append hprefix tailTrace_1374067
  have hstable : (prefixWord ++ tailWord_1374067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374067).length < 2 ^ (prefixWord ++ tailWord_1374067).sum := by decide
  have hdescent : baseEnd_1374067 < baseStart_1374067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374088 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 2, 4]
def baseStart_1374088 : Nat := 118140960795 + 1374088 * 2 ^ 59
def prefixEnd_1374088 : Nat := 4983230072969 + 3 ^ 40 * 1374088 * 2
def baseEnd_1374088 : Nat := 470378403716883405387127

theorem tailTrace_1374088 : CollatzResearch.WordTrace tailWord_1374088 prefixEnd_1374088 470378403716883405387127 := by
  unfold tailWord_1374088
  simp only [CollatzResearch.WordTrace]
  refine ⟨25058553322960663196017459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33411404430614217594689945 25058553322960663196017459)
  ·
    refine ⟨37587829984440994794026189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25058553322960663196017459 37587829984440994794026189)
    ·
      refine ⟨14095436244165373047759821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37587829984440994794026189 14095436244165373047759821)
      ·
        refine ⟨5285788591562014892909933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14095436244165373047759821 5285788591562014892909933)
        ·
          refine ⟨1982170721835755584841225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5285788591562014892909933 1982170721835755584841225)
          ·
            refine ⟨1486628041376816688630919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982170721835755584841225 1486628041376816688630919)
            ·
              refine ⟨2229942062065225032946379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486628041376816688630919 2229942062065225032946379)
              ·
                refine ⟨3344913093097837549419569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229942062065225032946379 3344913093097837549419569)
                ·
                  refine ⟨2508684819823378162064677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3344913093097837549419569 2508684819823378162064677)
                  ·
                    refine ⟨470378403716883405387127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508684819823378162064677 470378403716883405387127)
                    ·
                      rfl

theorem cell22_1374088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_1374088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374088 prefixEnd_1374088 := by exact prefixLift 1374088
  have htrace : WordTrace (prefixWord ++ tailWord_1374088) baseStart_1374088 baseEnd_1374088 := by
    simpa [prefixWord, tailWord_1374088, baseEnd_1374088] using wordTrace_append hprefix tailTrace_1374088
  have hstable : (prefixWord ++ tailWord_1374088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374088).length < 2 ^ (prefixWord ++ tailWord_1374088).sum := by decide
  have hdescent : baseEnd_1374088 < baseStart_1374088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374131 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 5]
def baseStart_1374131 : Nat := 118140960795 + 1374131 * 2 ^ 59
def prefixEnd_1374131 : Nat := 4983230072969 + 3 ^ 40 * 1374131 * 2
def baseEnd_1374131 : Nat := 156797707831881875520665

theorem tailTrace_1374131 : CollatzResearch.WordTrace tailWord_1374131 prefixEnd_1374131 156797707831881875520665 := by
  unfold tailWord_1374131
  simp only [CollatzResearch.WordTrace]
  refine ⟨50118674984765544735850247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33412449989843696490566831 50118674984765544735850247)
  ·
    refine ⟨75178012477148317103775371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50118674984765544735850247 75178012477148317103775371)
    ·
      refine ⟨112767018715722475655663057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75178012477148317103775371 112767018715722475655663057)
      ·
        refine ⟨84575264036791856741747293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112767018715722475655663057 84575264036791856741747293)
        ·
          refine ⟨31715724013796946278155235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84575264036791856741747293 31715724013796946278155235)
          ·
            refine ⟨47573586020695419417232853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31715724013796946278155235 47573586020695419417232853)
            ·
              refine ⟨1115005922360048892591395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 47573586020695419417232853 1115005922360048892591395)
              ·
                refine ⟨1672508883540073338887093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115005922360048892591395 1672508883540073338887093)
                ·
                  refine ⟨156797707831881875520665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1672508883540073338887093 156797707831881875520665)
                  ·
                    rfl

theorem cell22_1374131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 5].length) (baseStart_1374131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374131 prefixEnd_1374131 := by exact prefixLift 1374131
  have htrace : WordTrace (prefixWord ++ tailWord_1374131) baseStart_1374131 baseEnd_1374131 := by
    simpa [prefixWord, tailWord_1374131, baseEnd_1374131] using wordTrace_append hprefix tailTrace_1374131
  have hstable : (prefixWord ++ tailWord_1374131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374131).length < 2 ^ (prefixWord ++ tailWord_1374131).sum := by decide
  have hdescent : baseEnd_1374131 < baseStart_1374131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374176 : List Nat := [2, 1, 1, 3, 1, 1, 1, 8, 4]
def baseStart_1374176 : Nat := 118140960795 + 1374176 * 2 ^ 59
def prefixEnd_1374176 : Nat := 4983230072969 + 3 ^ 40 * 1374176 * 2
def baseEnd_1374176 : Nat := 156802842638426836395619

theorem tailTrace_1374176 : CollatzResearch.WordTrace tailWord_1374176 prefixEnd_1374176 156802842638426836395619 := by
  unfold tailWord_1374176
  simp only [CollatzResearch.WordTrace]
  refine ⟨25060158134801258710619191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33413544179735011614158921 25060158134801258710619191)
  ·
    refine ⟨37590237202201888065928787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25060158134801258710619191 37590237202201888065928787)
    ·
      refine ⟨56385355803302832098893181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37590237202201888065928787 56385355803302832098893181)
      ·
        refine ⟨21144508426238562037084943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56385355803302832098893181 21144508426238562037084943)
        ·
          refine ⟨31716762639357843055627415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21144508426238562037084943 31716762639357843055627415)
          ·
            refine ⟨47575143959036764583441123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31716762639357843055627415 47575143959036764583441123)
            ·
              refine ⟨71362715938555146875161685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47575143959036764583441123 71362715938555146875161685)
              ·
                refine ⟨836281827404943127443301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 71362715938555146875161685 836281827404943127443301)
                ·
                  refine ⟨156802842638426836395619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836281827404943127443301 156802842638426836395619)
                  ·
                    rfl

theorem cell22_1374176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_1374176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374176 prefixEnd_1374176 := by exact prefixLift 1374176
  have htrace : WordTrace (prefixWord ++ tailWord_1374176) baseStart_1374176 baseEnd_1374176 := by
    simpa [prefixWord, tailWord_1374176, baseEnd_1374176] using wordTrace_append hprefix tailTrace_1374176
  have hstable : (prefixWord ++ tailWord_1374176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374176).length < 2 ^ (prefixWord ++ tailWord_1374176).sum := by decide
  have hdescent : baseEnd_1374176 < baseStart_1374176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374204 : List Nat := [2, 2, 2, 1, 2, 2, 1, 10]
def baseStart_1374204 : Nat := 118140960795 + 1374204 * 2 ^ 59
def prefixEnd_1374204 : Nat := 4983230072969 + 3 ^ 40 * 1374204 * 2
def baseEnd_1374204 : Nat := 52268679209721974387419

theorem tailTrace_1374204 : CollatzResearch.WordTrace tailWord_1374204 prefixEnd_1374204 52268679209721974387419 := by
  unfold tailWord_1374204
  simp only [CollatzResearch.WordTrace]
  refine ⟨25060668756750539101628833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33414225009000718802171777 25060668756750539101628833)
  ·
    refine ⟨18795501567562904326221625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25060668756750539101628833 18795501567562904326221625)
    ·
      refine ⟨14096626175672178244666219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18795501567562904326221625 14096626175672178244666219)
      ·
        refine ⟨21144939263508267366999329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14096626175672178244666219 21144939263508267366999329)
        ·
          refine ⟨15858704447631200525249497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21144939263508267366999329 15858704447631200525249497)
          ·
            refine ⟨11894028335723400393937123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15858704447631200525249497 11894028335723400393937123)
            ·
              refine ⟨17841042503585100590905685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11894028335723400393937123 17841042503585100590905685)
              ·
                refine ⟨52268679209721974387419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17841042503585100590905685 52268679209721974387419)
                ·
                  rfl

theorem cell22_1374204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 10].length) (baseStart_1374204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374204 prefixEnd_1374204 := by exact prefixLift 1374204
  have htrace : WordTrace (prefixWord ++ tailWord_1374204) baseStart_1374204 baseEnd_1374204 := by
    simpa [prefixWord, tailWord_1374204, baseEnd_1374204] using wordTrace_append hprefix tailTrace_1374204
  have hstable : (prefixWord ++ tailWord_1374204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374204).length < 2 ^ (prefixWord ++ tailWord_1374204).sum := by decide
  have hdescent : baseEnd_1374204 < baseStart_1374204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374212 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_1374212 : Nat := 118140960795 + 1374212 * 2 ^ 59
def prefixEnd_1374212 : Nat := 4983230072969 + 3 ^ 40 * 1374212 * 2
def baseEnd_1374212 : Nat := 470420851450988415286747

theorem tailTrace_1374212 : CollatzResearch.WordTrace tailWord_1374212 prefixEnd_1374212 470420851450988415286747 := by
  unfold tailWord_1374212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25060814648736047784774445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33414419531648063713032593 25060814648736047784774445)
  ·
    refine ⟨9397805493276017919290417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25060814648736047784774445 9397805493276017919290417)
    ·
      refine ⟨7048354119957013439467813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9397805493276017919290417 7048354119957013439467813)
      ·
        refine ⟨1321566397491940019900215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7048354119957013439467813 1321566397491940019900215)
        ·
          refine ⟨1982349596237910029850323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321566397491940019900215 1982349596237910029850323)
          ·
            refine ⟨2973524394356865044775485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982349596237910029850323 2973524394356865044775485)
            ·
              refine ⟨1115071647883824391790807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2973524394356865044775485 1115071647883824391790807)
              ·
                refine ⟨1672607471825736587686211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115071647883824391790807 1672607471825736587686211)
                ·
                  refine ⟨2508911207738604881529317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672607471825736587686211 2508911207738604881529317)
                  ·
                    refine ⟨470420851450988415286747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508911207738604881529317 470420851450988415286747)
                    ·
                      rfl

theorem cell22_1374212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_1374212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374212 prefixEnd_1374212 := by exact prefixLift 1374212
  have htrace : WordTrace (prefixWord ++ tailWord_1374212) baseStart_1374212 baseEnd_1374212 := by
    simpa [prefixWord, tailWord_1374212, baseEnd_1374212] using wordTrace_append hprefix tailTrace_1374212
  have hstable : (prefixWord ++ tailWord_1374212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374212).length < 2 ^ (prefixWord ++ tailWord_1374212).sum := by decide
  have hdescent : baseEnd_1374212 < baseStart_1374212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374300 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 5]
def baseStart_1374300 : Nat := 118140960795 + 1374300 * 2 ^ 59
def prefixEnd_1374300 : Nat := 4983230072969 + 3 ^ 40 * 1374300 * 2
def baseEnd_1374300 : Nat := 156816991883128506362159

theorem tailTrace_1374300 : CollatzResearch.WordTrace tailWord_1374300 prefixEnd_1374300 156816991883128506362159 := by
  unfold tailWord_1374300
  simp only [CollatzResearch.WordTrace]
  refine ⟨25062419460576643299376177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33416559280768857732501569 25062419460576643299376177)
  ·
    refine ⟨18796814595432482474532133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25062419460576643299376177 18796814595432482474532133)
    ·
      refine ⟨3524402736643590463974775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18796814595432482474532133 3524402736643590463974775)
      ·
        refine ⟨5286604104965385695962163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524402736643590463974775 5286604104965385695962163)
        ·
          refine ⟨7929906157448078543943245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5286604104965385695962163 7929906157448078543943245)
          ·
            refine ⟨2973714809043029453978717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7929906157448078543943245 2973714809043029453978717)
            ·
              refine ⟨1115143053391136045242019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2973714809043029453978717 1115143053391136045242019)
              ·
                refine ⟨1672714580086704067863029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115143053391136045242019 1672714580086704067863029)
                ·
                  refine ⟨156816991883128506362159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1672714580086704067863029 156816991883128506362159)
                  ·
                    rfl

theorem cell22_1374300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_1374300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374300 prefixEnd_1374300 := by exact prefixLift 1374300
  have htrace : WordTrace (prefixWord ++ tailWord_1374300) baseStart_1374300 baseEnd_1374300 := by
    simpa [prefixWord, tailWord_1374300, baseEnd_1374300] using wordTrace_append hprefix tailTrace_1374300
  have hstable : (prefixWord ++ tailWord_1374300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374300).length < 2 ^ (prefixWord ++ tailWord_1374300).sum := by decide
  have hdescent : baseEnd_1374300 < baseStart_1374300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374311 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 6]
def baseStart_1374311 : Nat := 118140960795 + 1374311 * 2 ^ 59
def prefixEnd_1374311 : Nat := 4983230072969 + 3 ^ 40 * 1374311 * 2
def baseEnd_1374311 : Nat := 156818247058061719020481

theorem tailTrace_1374311 : CollatzResearch.WordTrace tailWord_1374311 prefixEnd_1374311 156818247058061719020481 := by
  unfold tailWord_1374311
  simp only [CollatzResearch.WordTrace]
  refine ⟨50125240124113435477402787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33416826749408956984935191 50125240124113435477402787)
  ·
    refine ⟨75187860186170153216104181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50125240124113435477402787 75187860186170153216104181)
    ·
      refine ⟨7048861892453451864009767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75187860186170153216104181 7048861892453451864009767)
      ·
        refine ⟨10573292838680177796014651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7048861892453451864009767 10573292838680177796014651)
        ·
          refine ⟨15859939258020266694021977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573292838680177796014651 15859939258020266694021977)
          ·
            refine ⟨11894954443515200020516483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15859939258020266694021977 11894954443515200020516483)
            ·
              refine ⟨17842431665272800030774725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11894954443515200020516483 17842431665272800030774725)
              ·
                refine ⟨3345455937238650005770261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17842431665272800030774725 3345455937238650005770261)
                ·
                  refine ⟨156818247058061719020481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3345455937238650005770261 156818247058061719020481)
                  ·
                    rfl

theorem cell22_1374311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 6].length) (baseStart_1374311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374311 prefixEnd_1374311 := by exact prefixLift 1374311
  have htrace : WordTrace (prefixWord ++ tailWord_1374311) baseStart_1374311 baseEnd_1374311 := by
    simpa [prefixWord, tailWord_1374311, baseEnd_1374311] using wordTrace_append hprefix tailTrace_1374311
  have hstable : (prefixWord ++ tailWord_1374311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374311).length < 2 ^ (prefixWord ++ tailWord_1374311).sum := by decide
  have hdescent : baseEnd_1374311 < baseStart_1374311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374313 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_1374313 : Nat := 118140960795 + 1374313 * 2 ^ 59
def prefixEnd_1374313 : Nat := 4983230072969 + 3 ^ 40 * 1374313 * 2
def baseEnd_1374313 : Nat := 470455425815057818511437

theorem tailTrace_1374313 : CollatzResearch.WordTrace tailWord_1374313 prefixEnd_1374313 470455425815057818511437 := by
  unfold tailWord_1374313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50125313070106189818975593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33416875380070793212650395 50125313070106189818975593)
  ·
    refine ⟨37593984802579642364231695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50125313070106189818975593 37593984802579642364231695)
    ·
      refine ⟨56390977203869463546347543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37593984802579642364231695 56390977203869463546347543)
      ·
        refine ⟨84586465805804195319521315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56390977203869463546347543 84586465805804195319521315)
        ·
          refine ⟨126879698708706292979281973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84586465805804195319521315 126879698708706292979281973)
          ·
            refine ⟨11894971753941214966807685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126879698708706292979281973 11894971753941214966807685)
            ·
              refine ⟨2230307203863977806276441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11894971753941214966807685 2230307203863977806276441)
              ·
                refine ⟨1672730402897983354707331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2230307203863977806276441 1672730402897983354707331)
                ·
                  refine ⟨2509095604346975032060997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672730402897983354707331 2509095604346975032060997)
                  ·
                    refine ⟨470455425815057818511437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2509095604346975032060997 470455425815057818511437)
                    ·
                      rfl

theorem cell22_1374313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_1374313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374313 prefixEnd_1374313 := by exact prefixLift 1374313
  have htrace : WordTrace (prefixWord ++ tailWord_1374313) baseStart_1374313 baseEnd_1374313 := by
    simpa [prefixWord, tailWord_1374313, baseEnd_1374313] using wordTrace_append hprefix tailTrace_1374313
  have hstable : (prefixWord ++ tailWord_1374313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374313).length < 2 ^ (prefixWord ++ tailWord_1374313).sum := by decide
  have hdescent : baseEnd_1374313 < baseStart_1374313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374343 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1374343 : Nat := 118140960795 + 1374343 * 2 ^ 59
def prefixEnd_1374343 : Nat := 4983230072969 + 3 ^ 40 * 1374343 * 2
def baseEnd_1374343 : Nat := 470465695428147740261345

theorem tailTrace_1374343 : CollatzResearch.WordTrace tailWord_1374343 prefixEnd_1374343 470465695428147740261345 := by
  unfold tailWord_1374343
  simp only [CollatzResearch.WordTrace]
  refine ⟨50126407259997504942567683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33417604839998336628378455 50126407259997504942567683)
  ·
    refine ⟨75189610889996257413851525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50126407259997504942567683 75189610889996257413851525)
    ·
      refine ⟨14098052041874298265097161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75189610889996257413851525 14098052041874298265097161)
      ·
        refine ⟨10573539031405723698822871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14098052041874298265097161 10573539031405723698822871)
        ·
          refine ⟨15860308547108585548234307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573539031405723698822871 15860308547108585548234307)
          ·
            refine ⟨23790462820662878322351461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15860308547108585548234307 23790462820662878322351461)
            ·
              refine ⟨4460711778874289685440899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23790462820662878322351461 4460711778874289685440899)
              ·
                refine ⟨6691067668311434528161349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460711778874289685440899 6691067668311434528161349)
                ·
                  refine ⟨1254575187808393974030253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6691067668311434528161349 1254575187808393974030253)
                  ·
                    refine ⟨470465695428147740261345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254575187808393974030253 470465695428147740261345)
                    ·
                      rfl

theorem cell22_1374343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1374343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374343 prefixEnd_1374343 := by exact prefixLift 1374343
  have htrace : WordTrace (prefixWord ++ tailWord_1374343) baseStart_1374343 baseEnd_1374343 := by
    simpa [prefixWord, tailWord_1374343, baseEnd_1374343] using wordTrace_append hprefix tailTrace_1374343
  have hstable : (prefixWord ++ tailWord_1374343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374343).length < 2 ^ (prefixWord ++ tailWord_1374343).sum := by decide
  have hdescent : baseEnd_1374343 < baseStart_1374343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374345 : List Nat := [1, 2, 1, 1, 4, 2, 5, 2, 4]
def baseStart_1374345 : Nat := 118140960795 + 1374345 * 2 ^ 59
def prefixEnd_1374345 : Nat := 4983230072969 + 3 ^ 40 * 1374345 * 2
def baseEnd_1374345 : Nat := 156822126689673467237113

theorem tailTrace_1374345 : CollatzResearch.WordTrace tailWord_1374345 prefixEnd_1374345 156822126689673467237113 := by
  unfold tailWord_1374345
  simp only [CollatzResearch.WordTrace]
  refine ⟨50126480205990259284140489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33417653470660172856093659 50126480205990259284140489)
  ·
    refine ⟨37594860154492694463105367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50126480205990259284140489 37594860154492694463105367)
    ·
      refine ⟨56392290231739041694658051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37594860154492694463105367 56392290231739041694658051)
      ·
        refine ⟨84588435347608562541987077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56392290231739041694658051 84588435347608562541987077)
        ·
          refine ⟨15860331627676605476622577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84588435347608562541987077 15860331627676605476622577)
          ·
            refine ⟨11895248720757454107466933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15860331627676605476622577 11895248720757454107466933)
            ·
              refine ⟨1115179567571011322575025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11895248720757454107466933 1115179567571011322575025)
              ·
                refine ⟨836384675678258491931269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115179567571011322575025 836384675678258491931269)
                ·
                  refine ⟨156822126689673467237113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836384675678258491931269 156822126689673467237113)
                  ·
                    rfl

theorem cell22_1374345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_1374345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374345 prefixEnd_1374345 := by exact prefixLift 1374345
  have htrace : WordTrace (prefixWord ++ tailWord_1374345) baseStart_1374345 baseEnd_1374345 := by
    simpa [prefixWord, tailWord_1374345, baseEnd_1374345] using wordTrace_append hprefix tailTrace_1374345
  have hstable : (prefixWord ++ tailWord_1374345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374345).length < 2 ^ (prefixWord ++ tailWord_1374345).sum := by decide
  have hdescent : baseEnd_1374345 < baseStart_1374345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374422 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1374422 : Nat := 118140960795 + 1374422 * 2 ^ 59
def prefixEnd_1374422 : Nat := 4983230072969 + 3 ^ 40 * 1374422 * 2
def baseEnd_1374422 : Nat := 470492738742617867536103

theorem tailTrace_1374422 : CollatzResearch.WordTrace tailWord_1374422 prefixEnd_1374422 470492738742617867536103 := by
  unfold tailWord_1374422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133080539169456339668345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33419525751140867623129013 3133080539169456339668345)
  ·
    refine ⟨2349810404377092254751259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3133080539169456339668345 2349810404377092254751259)
    ·
      refine ⟨3524715606565638382126889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349810404377092254751259 3524715606565638382126889)
      ·
        refine ⟨2643536704924228786595167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3524715606565638382126889 2643536704924228786595167)
        ·
          refine ⟨3965305057386343179892751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643536704924228786595167 3965305057386343179892751)
          ·
            refine ⟨5947957586079514769839127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965305057386343179892751 5947957586079514769839127)
            ·
              refine ⟨8921936379119272154758691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947957586079514769839127 8921936379119272154758691)
              ·
                refine ⟨13382904568678908232138037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8921936379119272154758691 13382904568678908232138037)
                ·
                  refine ⟨1254647303313647646762941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13382904568678908232138037 1254647303313647646762941)
                  ·
                    refine ⟨470492738742617867536103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254647303313647646762941 470492738742617867536103)
                    ·
                      rfl

theorem cell22_1374422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1374422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374422 prefixEnd_1374422 := by exact prefixLift 1374422
  have htrace : WordTrace (prefixWord ++ tailWord_1374422) baseStart_1374422 baseEnd_1374422 := by
    simpa [prefixWord, tailWord_1374422, baseEnd_1374422] using wordTrace_append hprefix tailTrace_1374422
  have hstable : (prefixWord ++ tailWord_1374422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374422).length < 2 ^ (prefixWord ++ tailWord_1374422).sum := by decide
  have hdescent : baseEnd_1374422 < baseStart_1374422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374439 : List Nat := [1, 1, 5, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1374439 : Nat := 118140960795 + 1374439 * 2 ^ 59
def prefixEnd_1374439 : Nat := 4983230072969 + 3 ^ 40 * 1374439 * 2
def baseEnd_1374439 : Nat := 470498558190035489861051

theorem tailTrace_1374439 : CollatzResearch.WordTrace tailWord_1374439 prefixEnd_1374439 470498558190035489861051 := by
  unfold tailWord_1374439
  simp only [CollatzResearch.WordTrace]
  refine ⟨50129908667649713338062371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33419939111766475558708247 50129908667649713338062371)
  ·
    refine ⟨75194863001474570007093557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50129908667649713338062371 75194863001474570007093557)
    ·
      refine ⟨7049518406388240938165021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75194863001474570007093557 7049518406388240938165021)
      ·
        refine ⟨2643569402395590351811883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7049518406388240938165021 2643569402395590351811883)
        ·
          refine ⟨3965354103593385527717825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643569402395590351811883 3965354103593385527717825)
          ·
            refine ⟨2974015577695039145788369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3965354103593385527717825 2974015577695039145788369)
            ·
              refine ⟨2230511683271279359341277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2974015577695039145788369 2230511683271279359341277)
              ·
                refine ⟨836441881226729759752979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2230511683271279359341277 836441881226729759752979)
                ·
                  refine ⟨1254662821840094639629469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836441881226729759752979 1254662821840094639629469)
                  ·
                    refine ⟨470498558190035489861051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254662821840094639629469 470498558190035489861051)
                    ·
                      rfl

theorem cell22_1374439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1374439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374439 prefixEnd_1374439 := by exact prefixLift 1374439
  have htrace : WordTrace (prefixWord ++ tailWord_1374439) baseStart_1374439 baseEnd_1374439 := by
    simpa [prefixWord, tailWord_1374439, baseEnd_1374439] using wordTrace_append hprefix tailTrace_1374439
  have hstable : (prefixWord ++ tailWord_1374439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374439).length < 2 ^ (prefixWord ++ tailWord_1374439).sum := by decide
  have hdescent : baseEnd_1374439 < baseStart_1374439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374463 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 6]
def baseStart_1374463 : Nat := 118140960795 + 1374463 * 2 ^ 59
def prefixEnd_1374463 : Nat := 4983230072969 + 3 ^ 40 * 1374463 * 2
def baseEnd_1374463 : Nat := 156835591293502475753659

theorem tailTrace_1374463 : CollatzResearch.WordTrace tailWord_1374463 prefixEnd_1374463 156835591293502475753659 := by
  unfold tailWord_1374463
  simp only [CollatzResearch.WordTrace]
  refine ⟨50130784019562765436936043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33420522679708510291290695 50130784019562765436936043)
  ·
    refine ⟨75196176029344148155404065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50130784019562765436936043 75196176029344148155404065)
    ·
      refine ⟨56397132022008111116553049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75196176029344148155404065 56397132022008111116553049)
      ·
        refine ⟨42297849016506083337414787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56397132022008111116553049 42297849016506083337414787)
        ·
          refine ⟨63446773524759125006122181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42297849016506083337414787 63446773524759125006122181)
          ·
            refine ⟨11896270035892335938647909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63446773524759125006122181 11896270035892335938647909)
            ·
              refine ⟨2230550631729812988496483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11896270035892335938647909 2230550631729812988496483)
              ·
                refine ⟨3345825947594719482744725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230550631729812988496483 3345825947594719482744725)
                ·
                  refine ⟨156835591293502475753659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3345825947594719482744725 156835591293502475753659)
                  ·
                    rfl

theorem cell22_1374463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 6].length) (baseStart_1374463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374463 prefixEnd_1374463 := by exact prefixLift 1374463
  have htrace : WordTrace (prefixWord ++ tailWord_1374463) baseStart_1374463 baseEnd_1374463 := by
    simpa [prefixWord, tailWord_1374463, baseEnd_1374463] using wordTrace_append hprefix tailTrace_1374463
  have hstable : (prefixWord ++ tailWord_1374463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374463).length < 2 ^ (prefixWord ++ tailWord_1374463).sum := by decide
  have hdescent : baseEnd_1374463 < baseStart_1374463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374495 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 4, 3]
def baseStart_1374495 : Nat := 118140960795 + 1374495 * 2 ^ 59
def prefixEnd_1374495 : Nat := 4983230072969 + 3 ^ 40 * 1374495 * 2
def baseEnd_1374495 : Nat := 470517728134470010460879

theorem tailTrace_1374495 : CollatzResearch.WordTrace tailWord_1374495 prefixEnd_1374495 470517728134470010460879 := by
  unfold tailWord_1374495
  simp only [CollatzResearch.WordTrace]
  refine ⟨50131951155446834902100939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33421300770297889934733959 50131951155446834902100939)
  ·
    refine ⟨75197926733170252353151409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50131951155446834902100939 75197926733170252353151409)
    ·
      refine ⟨56398445049877689264863557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75197926733170252353151409 56398445049877689264863557)
      ·
        refine ⟨10574708446852066737161917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56398445049877689264863557 10574708446852066737161917)
        ·
          refine ⟨3965515667569525026435719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10574708446852066737161917 3965515667569525026435719)
          ·
            refine ⟨5948273501354287539653579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965515667569525026435719 5948273501354287539653579)
            ·
              refine ⟨8922410252031431309480369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948273501354287539653579 8922410252031431309480369)
              ·
                refine ⟨6691807689023573482110277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8922410252031431309480369 6691807689023573482110277)
                ·
                  refine ⟨1254713941691920027895677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6691807689023573482110277 1254713941691920027895677)
                  ·
                    refine ⟨470517728134470010460879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254713941691920027895677 470517728134470010460879)
                    ·
                      rfl

theorem cell22_1374495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_1374495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374495 prefixEnd_1374495 := by exact prefixLift 1374495
  have htrace : WordTrace (prefixWord ++ tailWord_1374495) baseStart_1374495 baseEnd_1374495 := by
    simpa [prefixWord, tailWord_1374495, baseEnd_1374495] using wordTrace_append hprefix tailTrace_1374495
  have hstable : (prefixWord ++ tailWord_1374495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374495).length < 2 ^ (prefixWord ++ tailWord_1374495).sum := by decide
  have hdescent : baseEnd_1374495 < baseStart_1374495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374514 : List Nat := [3, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1374514 : Nat := 118140960795 + 1374514 * 2 ^ 59
def prefixEnd_1374514 : Nat := 4983230072969 + 3 ^ 40 * 1374514 * 2
def baseEnd_1374514 : Nat := 156841410740920098078607

theorem tailTrace_1374514 : CollatzResearch.WordTrace tailWord_1374514 prefixEnd_1374514 156841410740920098078607 := by
  unfold tailWord_1374514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533161035594500286760649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33421762761585334098028397 12533161035594500286760649)
  ·
    refine ⟨9399870776695875215070487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12533161035594500286760649 9399870776695875215070487)
    ·
      refine ⟨14099806165043812822605731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9399870776695875215070487 14099806165043812822605731)
      ·
        refine ⟨21149709247565719233908597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14099806165043812822605731 21149709247565719233908597)
        ·
          refine ⟨1982785241959286178178931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21149709247565719233908597 1982785241959286178178931)
          ·
            refine ⟨2974177862938929267268397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982785241959286178178931 2974177862938929267268397)
            ·
              refine ⟨1115316698602098475225649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2974177862938929267268397 1115316698602098475225649)
              ·
                refine ⟨836487523951573856419237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115316698602098475225649 836487523951573856419237)
                ·
                  refine ⟨156841410740920098078607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836487523951573856419237 156841410740920098078607)
                  ·
                    rfl

theorem cell22_1374514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1374514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374514 prefixEnd_1374514 := by exact prefixLift 1374514
  have htrace : WordTrace (prefixWord ++ tailWord_1374514) baseStart_1374514 baseEnd_1374514 := by
    simpa [prefixWord, tailWord_1374514, baseEnd_1374514] using wordTrace_append hprefix tailTrace_1374514
  have hstable : (prefixWord ++ tailWord_1374514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374514).length < 2 ^ (prefixWord ++ tailWord_1374514).sum := by decide
  have hdescent : baseEnd_1374514 < baseStart_1374514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374529 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1374529 : Nat := 118140960795 + 1374529 * 2 ^ 59
def prefixEnd_1374529 : Nat := 4983230072969 + 3 ^ 40 * 1374529 * 2
def baseEnd_1374529 : Nat := 470529367029305255110775

theorem tailTrace_1374529 : CollatzResearch.WordTrace tailWord_1374529 prefixEnd_1374529 470529367029305255110775 := by
  unfold tailWord_1374529
  simp only [CollatzResearch.WordTrace]
  refine ⟨50133191237323658708838641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33422127491549105805892427 50133191237323658708838641)
  ·
    refine ⟨37599893427992744031628981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50133191237323658708838641 37599893427992744031628981)
    ·
      refine ⟨3524990008874319752965217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37599893427992744031628981 3524990008874319752965217)
      ·
        refine ⟨2643742506655739814723913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3524990008874319752965217 2643742506655739814723913)
        ·
          refine ⟨1982806879991804861042935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643742506655739814723913 1982806879991804861042935)
          ·
            refine ⟨2974210319987707291564403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982806879991804861042935 2974210319987707291564403)
            ·
              refine ⟨4461315479981560937346605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974210319987707291564403 4461315479981560937346605)
              ·
                refine ⟨1672993304993085351504977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4461315479981560937346605 1672993304993085351504977)
                ·
                  refine ⟨1254744978744814013628733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1672993304993085351504977 1254744978744814013628733)
                  ·
                    refine ⟨470529367029305255110775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254744978744814013628733 470529367029305255110775)
                    ·
                      rfl

theorem cell22_1374529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1374529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374529 prefixEnd_1374529 := by exact prefixLift 1374529
  have htrace : WordTrace (prefixWord ++ tailWord_1374529) baseStart_1374529 baseEnd_1374529 := by
    simpa [prefixWord, tailWord_1374529, baseEnd_1374529] using wordTrace_append hprefix tailTrace_1374529
  have hstable : (prefixWord ++ tailWord_1374529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374529).length < 2 ^ (prefixWord ++ tailWord_1374529).sum := by decide
  have hdescent : baseEnd_1374529 < baseStart_1374529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374540 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_1374540 : Nat := 118140960795 + 1374540 * 2 ^ 59
def prefixEnd_1374540 : Nat := 4983230072969 + 3 ^ 40 * 1374540 * 2
def baseEnd_1374540 : Nat := 470533132554104893085741

theorem tailTrace_1374540 : CollatzResearch.WordTrace tailWord_1374540 prefixEnd_1374540 470533132554104893085741 := by
  unfold tailWord_1374540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25066796220141903793744537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33422394960189205058326049 25066796220141903793744537)
  ·
    refine ⟨18800097165106427845308403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25066796220141903793744537 18800097165106427845308403)
    ·
      refine ⟨28200145747659641767962605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18800097165106427845308403 28200145747659641767962605)
      ·
        refine ⟨10575054655372365662985977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28200145747659641767962605 10575054655372365662985977)
        ·
          refine ⟨7931290991529274247239483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10575054655372365662985977 7931290991529274247239483)
          ·
            refine ⟨11896936487293911370859225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7931290991529274247239483 11896936487293911370859225)
            ·
              refine ⟨8922702365470433528144419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11896936487293911370859225 8922702365470433528144419)
              ·
                refine ⟨13384053548205650292216629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8922702365470433528144419 13384053548205650292216629)
                ·
                  refine ⟨1254755020144279714895309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13384053548205650292216629 1254755020144279714895309)
                  ·
                    refine ⟨470533132554104893085741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254755020144279714895309 470533132554104893085741)
                    ·
                      rfl

theorem cell22_1374540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_1374540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374540 prefixEnd_1374540 := by exact prefixLift 1374540
  have htrace : WordTrace (prefixWord ++ tailWord_1374540) baseStart_1374540 baseEnd_1374540 := by
    simpa [prefixWord, tailWord_1374540, baseEnd_1374540] using wordTrace_append hprefix tailTrace_1374540
  have hstable : (prefixWord ++ tailWord_1374540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374540).length < 2 ^ (prefixWord ++ tailWord_1374540).sum := by decide
  have hdescent : baseEnd_1374540 < baseStart_1374540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374600 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1374600 : Nat := 118140960795 + 1374600 * 2 ^ 59
def prefixEnd_1374600 : Nat := 4983230072969 + 3 ^ 40 * 1374600 * 2
def baseEnd_1374600 : Nat := 470553671780284736585557

theorem tailTrace_1374600 : CollatzResearch.WordTrace tailWord_1374600 prefixEnd_1374600 470553671780284736585557 := by
  unfold tailWord_1374600
  simp only [CollatzResearch.WordTrace]
  refine ⟨25067890410033218917336627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33423853880044291889782169 25067890410033218917336627)
  ·
    refine ⟨37601835615049828376004941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25067890410033218917336627 37601835615049828376004941)
    ·
      refine ⟨14100688355643685641001853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37601835615049828376004941 14100688355643685641001853)
      ·
        refine ⟨5287758133366382115375695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14100688355643685641001853 5287758133366382115375695)
        ·
          refine ⟨7931637200049573173063543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5287758133366382115375695 7931637200049573173063543)
          ·
            refine ⟨11897455800074359759595315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7931637200049573173063543 11897455800074359759595315)
            ·
              refine ⟨17846183700111539639392973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11897455800074359759595315 17846183700111539639392973)
              ·
                refine ⟨6692318887541827364772365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17846183700111539639392973 6692318887541827364772365)
                ·
                  refine ⟨2509619582828185261789637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6692318887541827364772365 2509619582828185261789637)
                  ·
                    refine ⟨470553671780284736585557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2509619582828185261789637 470553671780284736585557)
                    ·
                      rfl

theorem cell22_1374600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1374600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374600 prefixEnd_1374600 := by exact prefixLift 1374600
  have htrace : WordTrace (prefixWord ++ tailWord_1374600) baseStart_1374600 baseEnd_1374600 := by
    simpa [prefixWord, tailWord_1374600, baseEnd_1374600] using wordTrace_append hprefix tailTrace_1374600
  have hstable : (prefixWord ++ tailWord_1374600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374600).length < 2 ^ (prefixWord ++ tailWord_1374600).sum := by decide
  have hdescent : baseEnd_1374600 < baseStart_1374600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374632 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 6]
def baseStart_1374632 : Nat := 118140960795 + 1374632 * 2 ^ 59
def prefixEnd_1374632 : Nat := 4983230072969 + 3 ^ 40 * 1374632 * 2
def baseEnd_1374632 : Nat := 156854875344749106595153

theorem tailTrace_1374632 : CollatzResearch.WordTrace tailWord_1374632 prefixEnd_1374632 156854875344749106595153 := by
  unfold tailWord_1374632
  simp only [CollatzResearch.WordTrace]
  refine ⟨25068473977975253649919075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33424631970633671533225433 25068473977975253649919075)
  ·
    refine ⟨37602710966962880474878613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25068473977975253649919075 37602710966962880474878613)
    ·
      refine ⟨1762627076576385022259935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37602710966962880474878613 1762627076576385022259935)
      ·
        refine ⟨2643940614864577533389903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762627076576385022259935 2643940614864577533389903)
        ·
          refine ⟨3965910922296866300084855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643940614864577533389903 3965910922296866300084855)
          ·
            refine ⟨5948866383445299450127283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965910922296866300084855 5948866383445299450127283)
            ·
              refine ⟨8923299575167949175190925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948866383445299450127283 8923299575167949175190925)
              ·
                refine ⟨3346237340687980940696597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8923299575167949175190925 3346237340687980940696597)
                ·
                  refine ⟨156854875344749106595153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3346237340687980940696597 156854875344749106595153)
                  ·
                    rfl

theorem cell22_1374632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_1374632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374632 prefixEnd_1374632 := by exact prefixLift 1374632
  have htrace : WordTrace (prefixWord ++ tailWord_1374632) baseStart_1374632 baseEnd_1374632 := by
    simpa [prefixWord, tailWord_1374632, baseEnd_1374632] using wordTrace_append hprefix tailTrace_1374632
  have hstable : (prefixWord ++ tailWord_1374632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374632).length < 2 ^ (prefixWord ++ tailWord_1374632).sum := by decide
  have hdescent : baseEnd_1374632 < baseStart_1374632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374647 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 1, 5]
def baseStart_1374647 : Nat := 118140960795 + 1374647 * 2 ^ 59
def prefixEnd_1374647 : Nat := 4983230072969 + 3 ^ 40 * 1374647 * 2
def baseEnd_1374647 : Nat := 470569760840792280660413

theorem tailTrace_1374647 : CollatzResearch.WordTrace tailWord_1374647 prefixEnd_1374647 470569760840792280660413 := by
  unfold tailWord_1374647
  simp only [CollatzResearch.WordTrace]
  refine ⟨50137495050896164861634195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33424996700597443241089463 50137495050896164861634195)
  ·
    refine ⟨75206242576344247292451293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50137495050896164861634195 75206242576344247292451293)
    ·
      refine ⟨28202340966129092734669235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75206242576344247292451293 28202340966129092734669235)
      ·
        refine ⟨42303511449193639102003853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28202340966129092734669235 42303511449193639102003853)
        ·
          refine ⟨15863816793447614663251445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42303511449193639102003853 15863816793447614663251445)
          ·
            refine ⟨1487232824385713874679823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15863816793447614663251445 1487232824385713874679823)
            ·
              refine ⟨2230849236578570812019735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487232824385713874679823 2230849236578570812019735)
              ·
                refine ⟨3346273854867856218029603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230849236578570812019735 3346273854867856218029603)
                ·
                  refine ⟨5019410782301784327044405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3346273854867856218029603 5019410782301784327044405)
                  ·
                    refine ⟨470569760840792280660413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5019410782301784327044405 470569760840792280660413)
                    ·
                      rfl

theorem cell22_1374647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_1374647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374647 prefixEnd_1374647 := by exact prefixLift 1374647
  have htrace : WordTrace (prefixWord ++ tailWord_1374647) baseStart_1374647 baseEnd_1374647 := by
    simpa [prefixWord, tailWord_1374647, baseEnd_1374647] using wordTrace_append hprefix tailTrace_1374647
  have hstable : (prefixWord ++ tailWord_1374647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374647).length < 2 ^ (prefixWord ++ tailWord_1374647).sum := by decide
  have hdescent : baseEnd_1374647 < baseStart_1374647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 5, 4]
def baseStart_1374735 : Nat := 118140960795 + 1374735 * 2 ^ 59
def prefixEnd_1374735 : Nat := 4983230072969 + 3 ^ 40 * 1374735 * 2
def baseEnd_1374735 : Nat := 470599885039189384460143

theorem tailTrace_1374735 : CollatzResearch.WordTrace tailWord_1374735 prefixEnd_1374735 470599885039189384460143 := by
  unfold tailWord_1374735
  simp only [CollatzResearch.WordTrace]
  refine ⟨50140704674577355890837659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33427136449718237260558439 50140704674577355890837659)
  ·
    refine ⟨75211057011866033836256489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50140704674577355890837659 75211057011866033836256489)
    ·
      refine ⟨56408292758899525377192367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75211057011866033836256489 56408292758899525377192367)
      ·
        refine ⟨84612439138349288065788551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56408292758899525377192367 84612439138349288065788551)
        ·
          refine ⟨126918658707523932098682827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84612439138349288065788551 126918658707523932098682827)
          ·
            refine ⟨190377988061285898148024241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126918658707523932098682827 190377988061285898148024241)
            ·
              refine ⟨142783491045964423611018181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190377988061285898148024241 142783491045964423611018181)
              ·
                refine ⟨26771904571118329427065909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142783491045964423611018181 26771904571118329427065909)
                ·
                  refine ⟨2509866053542343383787429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26771904571118329427065909 2509866053542343383787429)
                  ·
                    refine ⟨470599885039189384460143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2509866053542343383787429 470599885039189384460143)
                    ·
                      rfl

theorem cell22_1374735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_1374735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374735 prefixEnd_1374735 := by exact prefixLift 1374735
  have htrace : WordTrace (prefixWord ++ tailWord_1374735) baseStart_1374735 baseEnd_1374735 := by
    simpa [prefixWord, tailWord_1374735, baseEnd_1374735] using wordTrace_append hprefix tailTrace_1374735
  have hstable : (prefixWord ++ tailWord_1374735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374735).length < 2 ^ (prefixWord ++ tailWord_1374735).sum := by decide
  have hdescent : baseEnd_1374735 < baseStart_1374735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374743 : List Nat := [1, 1, 3, 6, 1, 1, 1, 4, 1, 3]
def baseStart_1374743 : Nat := 118140960795 + 1374743 * 2 ^ 59
def prefixEnd_1374743 : Nat := 4983230072969 + 3 ^ 40 * 1374743 * 2
def baseEnd_1374743 : Nat := 470602623602680030260119

theorem tailTrace_1374743 : CollatzResearch.WordTrace tailWord_1374743 prefixEnd_1374743 470602623602680030260119 := by
  unfold tailWord_1374743
  simp only [CollatzResearch.WordTrace]
  refine ⟨50140996458548373257128883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33427330972365582171419255 50140996458548373257128883)
  ·
    refine ⟨75211494687822559885693325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50140996458548373257128883 75211494687822559885693325)
    ·
      refine ⟨28204310507933459957134997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75211494687822559885693325 28204310507933459957134997)
      ·
        refine ⟨1322077055059380935490703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28204310507933459957134997 1322077055059380935490703)
        ·
          refine ⟨1983115582589071403236055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322077055059380935490703 1983115582589071403236055)
          ·
            refine ⟨2974673373883607104854083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983115582589071403236055 2974673373883607104854083)
            ·
              refine ⟨4462010060825410657281125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974673373883607104854083 4462010060825410657281125)
              ·
                refine ⟨836626886404764498240211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4462010060825410657281125 836626886404764498240211)
                ·
                  refine ⟨1254940329607146747360317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836626886404764498240211 1254940329607146747360317)
                  ·
                    refine ⟨470602623602680030260119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254940329607146747360317 470602623602680030260119)
                    ·
                      rfl

theorem cell22_1374743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_1374743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374743 prefixEnd_1374743 := by exact prefixLift 1374743
  have htrace : WordTrace (prefixWord ++ tailWord_1374743) baseStart_1374743 baseEnd_1374743 := by
    simpa [prefixWord, tailWord_1374743, baseEnd_1374743] using wordTrace_append hprefix tailTrace_1374743
  have hstable : (prefixWord ++ tailWord_1374743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374743).length < 2 ^ (prefixWord ++ tailWord_1374743).sum := by decide
  have hdescent : baseEnd_1374743 < baseStart_1374743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374799 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 2, 3]
def baseStart_1374799 : Nat := 118140960795 + 1374799 * 2 ^ 59
def prefixEnd_1374799 : Nat := 4983230072969 + 3 ^ 40 * 1374799 * 2
def baseEnd_1374799 : Nat := 470621793547114550859947

theorem tailTrace_1374799 : CollatzResearch.WordTrace tailWord_1374799 prefixEnd_1374799 470621793547114550859947 := by
  unfold tailWord_1374799
  simp only [CollatzResearch.WordTrace]
  refine ⟨50143038946345494821167451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33428692630896996547444967 50143038946345494821167451)
  ·
    refine ⟨75214558419518242231751177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50143038946345494821167451 75214558419518242231751177)
    ·
      refine ⟨56410918814638681673813383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75214558419518242231751177 56410918814638681673813383)
      ·
        refine ⟨84616378221958022510720075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56410918814638681673813383 84616378221958022510720075)
        ·
          refine ⟨126924567332937033766080113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84616378221958022510720075 126924567332937033766080113)
          ·
            refine ⟨95193425499702775324560085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126924567332937033766080113 95193425499702775324560085)
            ·
              refine ⟨2231095910149283796669377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95193425499702775324560085 2231095910149283796669377)
              ·
                refine ⟨1673321932611962847502033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231095910149283796669377 1673321932611962847502033)
                ·
                  refine ⟨1254991449458972135626525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1673321932611962847502033 1254991449458972135626525)
                  ·
                    refine ⟨470621793547114550859947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254991449458972135626525 470621793547114550859947)
                    ·
                      rfl

theorem cell22_1374799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_1374799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374799 prefixEnd_1374799 := by exact prefixLift 1374799
  have htrace : WordTrace (prefixWord ++ tailWord_1374799) baseStart_1374799 baseEnd_1374799 := by
    simpa [prefixWord, tailWord_1374799, baseEnd_1374799] using wordTrace_append hprefix tailTrace_1374799
  have hstable : (prefixWord ++ tailWord_1374799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374799).length < 2 ^ (prefixWord ++ tailWord_1374799).sum := by decide
  have hdescent : baseEnd_1374799 < baseStart_1374799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374827 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 5, 3]
def baseStart_1374827 : Nat := 118140960795 + 1374827 * 2 ^ 59
def prefixEnd_1374827 : Nat := 4983230072969 + 3 ^ 40 * 1374827 * 2
def baseEnd_1374827 : Nat := 470631378519331811159861

theorem tailTrace_1374827 : CollatzResearch.WordTrace tailWord_1374827 prefixEnd_1374827 470631378519331811159861 := by
  unfold tailWord_1374827
  simp only [CollatzResearch.WordTrace]
  refine ⟨50144060190244055603186735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33429373460162703735457823 50144060190244055603186735)
  ·
    refine ⟨75216090285366083404780103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50144060190244055603186735 75216090285366083404780103)
    ·
      refine ⟨112824135428049125107170155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75216090285366083404780103 112824135428049125107170155)
      ·
        refine ⟨169236203142073687660755233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112824135428049125107170155 169236203142073687660755233)
        ·
          refine ⟨126927152356555265745566425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169236203142073687660755233 126927152356555265745566425)
          ·
            refine ⟨95195364267416449309174819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126927152356555265745566425 95195364267416449309174819)
            ·
              refine ⟨142793046401124673963762229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95195364267416449309174819 142793046401124673963762229)
              ·
                refine ⟨13386848100105438184102709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142793046401124673963762229 13386848100105438184102709)
                ·
                  refine ⟨1255017009384884829759629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13386848100105438184102709 1255017009384884829759629)
                  ·
                    refine ⟨470631378519331811159861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1255017009384884829759629 470631378519331811159861)
                    ·
                      rfl

theorem cell22_1374827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 3].length) (baseStart_1374827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374827 prefixEnd_1374827 := by exact prefixLift 1374827
  have htrace : WordTrace (prefixWord ++ tailWord_1374827) baseStart_1374827 baseEnd_1374827 := by
    simpa [prefixWord, tailWord_1374827, baseEnd_1374827] using wordTrace_append hprefix tailTrace_1374827
  have hstable : (prefixWord ++ tailWord_1374827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374827).length < 2 ^ (prefixWord ++ tailWord_1374827).sum := by decide
  have hdescent : baseEnd_1374827 < baseStart_1374827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374829 : List Nat := [1, 5, 1, 1, 3, 1, 4, 6]
def baseStart_1374829 : Nat := 118140960795 + 1374829 * 2 ^ 59
def prefixEnd_1374829 : Nat := 4983230072969 + 3 ^ 40 * 1374829 * 2
def baseEnd_1374829 : Nat := 52292451462244941401095

theorem tailTrace_1374829 : CollatzResearch.WordTrace tailWord_1374829 prefixEnd_1374829 52292451462244941401095 := by
  unfold tailWord_1374829
  simp only [CollatzResearch.WordTrace]
  refine ⟨50144133136236809944759541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33429422090824539963173027 50144133136236809944759541)
  ·
    refine ⟨4701012481522200932321207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50144133136236809944759541 4701012481522200932321207)
    ·
      refine ⟨7051518722283301398481811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4701012481522200932321207 7051518722283301398481811)
      ·
        refine ⟨10577278083424952097722717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051518722283301398481811 10577278083424952097722717)
        ·
          refine ⟨3966479281284357036646019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10577278083424952097722717 3966479281284357036646019)
          ·
            refine ⟨5949718921926535554969029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966479281284357036646019 5949718921926535554969029)
            ·
              refine ⟨1115572297861225416556693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5949718921926535554969029 1115572297861225416556693)
              ·
                refine ⟨52292451462244941401095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1115572297861225416556693 52292451462244941401095)
                ·
                  rfl

theorem cell22_1374829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 6].length) (baseStart_1374829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374829 prefixEnd_1374829 := by exact prefixLift 1374829
  have htrace : WordTrace (prefixWord ++ tailWord_1374829) baseStart_1374829 baseEnd_1374829 := by
    simpa [prefixWord, tailWord_1374829, baseEnd_1374829] using wordTrace_append hprefix tailTrace_1374829
  have hstable : (prefixWord ++ tailWord_1374829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374829).length < 2 ^ (prefixWord ++ tailWord_1374829).sum := by decide
  have hdescent : baseEnd_1374829 < baseStart_1374829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374857 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 5]
def baseStart_1374857 : Nat := 118140960795 + 1374857 * 2 ^ 59
def prefixEnd_1374857 : Nat := 4983230072969 + 3 ^ 40 * 1374857 * 2
def baseEnd_1374857 : Nat := 156880549377473910969923

theorem tailTrace_1374857 : CollatzResearch.WordTrace tailWord_1374857 prefixEnd_1374857 156880549377473910969923 := by
  unfold tailWord_1374857
  simp only [CollatzResearch.WordTrace]
  refine ⟨50145154380135370726778825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33430102920090247151185883 50145154380135370726778825)
  ·
    refine ⟨37608865785101528045084119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50145154380135370726778825 37608865785101528045084119)
    ·
      refine ⟨56413298677652292067626179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37608865785101528045084119 56413298677652292067626179)
      ·
        refine ⟨84619948016478438101439269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56413298677652292067626179 84619948016478438101439269)
        ·
          refine ⟨15866240253089707144019863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84619948016478438101439269 15866240253089707144019863)
          ·
            refine ⟨23799360379634560716029795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15866240253089707144019863 23799360379634560716029795)
            ·
              refine ⟨35699040569451841074044693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23799360379634560716029795 35699040569451841074044693)
              ·
                refine ⟨1673392526693055050345845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35699040569451841074044693 1673392526693055050345845)
                ·
                  refine ⟨156880549377473910969923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1673392526693055050345845 156880549377473910969923)
                  ·
                    rfl

theorem cell22_1374857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_1374857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374857 prefixEnd_1374857 := by exact prefixLift 1374857
  have htrace : WordTrace (prefixWord ++ tailWord_1374857) baseStart_1374857 baseEnd_1374857 := by
    simpa [prefixWord, tailWord_1374857, baseEnd_1374857] using wordTrace_append hprefix tailTrace_1374857
  have hstable : (prefixWord ++ tailWord_1374857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374857).length < 2 ^ (prefixWord ++ tailWord_1374857).sum := by decide
  have hdescent : baseEnd_1374857 < baseStart_1374857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374872 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1374872 : Nat := 118140960795 + 1374872 * 2 ^ 59
def prefixEnd_1374872 : Nat := 4983230072969 + 3 ^ 40 * 1374872 * 2
def baseEnd_1374872 : Nat := 470646782938966693784723

theorem tailTrace_1374872 : CollatzResearch.WordTrace tailWord_1374872 prefixEnd_1374872 470646782938966693784723 := by
  unfold tailWord_1374872
  simp only [CollatzResearch.WordTrace]
  refine ⟨25072850737540514144287435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33430467650054018859049913 25072850737540514144287435)
  ·
    refine ⟨37609276106310771216431153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25072850737540514144287435 37609276106310771216431153)
    ·
      refine ⟨28206957079733078412323365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37609276106310771216431153 28206957079733078412323365)
      ·
        refine ⟨5288804452449952202310631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28206957079733078412323365 5288804452449952202310631)
        ·
          refine ⟨7933206678674928303465947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288804452449952202310631 7933206678674928303465947)
          ·
            refine ⟨11899810018012392455198921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7933206678674928303465947 11899810018012392455198921)
            ·
              refine ⟨8924857513509294341399191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11899810018012392455198921 8924857513509294341399191)
              ·
                refine ⟨13387286270263941512098787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8924857513509294341399191 13387286270263941512098787)
                ·
                  refine ⟨20080929405395912268148181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13387286270263941512098787 20080929405395912268148181)
                  ·
                    refine ⟨470646782938966693784723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20080929405395912268148181 470646782938966693784723)
                    ·
                      rfl

theorem cell22_1374872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1374872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374872 prefixEnd_1374872 := by exact prefixLift 1374872
  have htrace : WordTrace (prefixWord ++ tailWord_1374872) baseStart_1374872 baseEnd_1374872 := by
    simpa [prefixWord, tailWord_1374872, baseEnd_1374872] using wordTrace_append hprefix tailTrace_1374872
  have hstable : (prefixWord ++ tailWord_1374872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374872).length < 2 ^ (prefixWord ++ tailWord_1374872).sum := by decide
  have hdescent : baseEnd_1374872 < baseStart_1374872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1374949 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1374949 : Nat := 118140960795 + 1374949 * 2 ^ 59
def prefixEnd_1374949 : Nat := 4983230072969 + 3 ^ 40 * 1374949 * 2
def baseEnd_1374949 : Nat := 470673141612564159609487

theorem tailTrace_1374949 : CollatzResearch.WordTrace tailWord_1374949 prefixEnd_1374949 470673141612564159609487 := by
  unfold tailWord_1374949
  simp only [CollatzResearch.WordTrace]
  refine ⟨50148509895802070439127901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33432339930534713626085267 50148509895802070439127901)
  ·
    refine ⟨18805691210925776414672963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50148509895802070439127901 18805691210925776414672963)
    ·
      refine ⟨28208536816388664622009445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18805691210925776414672963 28208536816388664622009445)
      ·
        refine ⟨5289100653072874616626771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28208536816388664622009445 5289100653072874616626771)
        ·
          refine ⟨7933650979609311924940157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5289100653072874616626771 7933650979609311924940157)
          ·
            refine ⟨2975119117353491971852559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7933650979609311924940157 2975119117353491971852559)
            ·
              refine ⟨4462678676030237957778839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975119117353491971852559 4462678676030237957778839)
              ·
                refine ⟨6694018014045356936668259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462678676030237957778839 6694018014045356936668259)
                ·
                  refine ⟨10041027021068035405002389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6694018014045356936668259 10041027021068035405002389)
                  ·
                    refine ⟨470673141612564159609487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10041027021068035405002389 470673141612564159609487)
                    ·
                      rfl

theorem cell22_1374949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1374949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1374949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1374949 prefixEnd_1374949 := by exact prefixLift 1374949
  have htrace : WordTrace (prefixWord ++ tailWord_1374949) baseStart_1374949 baseEnd_1374949 := by
    simpa [prefixWord, tailWord_1374949, baseEnd_1374949] using wordTrace_append hprefix tailTrace_1374949
  have hstable : (prefixWord ++ tailWord_1374949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1374949).length < 2 ^ (prefixWord ++ tailWord_1374949).sum := by decide
  have hdescent : baseEnd_1374949 < baseStart_1374949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1374949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375054 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_1375054 : Nat := 118140960795 + 1375054 * 2 ^ 59
def prefixEnd_1375054 : Nat := 4983230072969 + 3 ^ 40 * 1375054 * 2
def baseEnd_1375054 : Nat := 156903028419459628578055

theorem tailTrace_1375054 : CollatzResearch.WordTrace tailWord_1375054 prefixEnd_1375054 156903028419459628578055 := by
  unfold tailWord_1375054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269042445052709171462527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33434893040281115581133477 6269042445052709171462527)
  ·
    refine ⟨9403563667579063757193791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6269042445052709171462527 9403563667579063757193791)
    ·
      refine ⟨14105345501368595635790687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9403563667579063757193791 14105345501368595635790687)
      ·
        refine ⟨21158018252052893453686031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14105345501368595635790687 21158018252052893453686031)
        ·
          refine ⟨31737027378079340180529047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21158018252052893453686031 31737027378079340180529047)
          ·
            refine ⟨47605541067119010270793571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31737027378079340180529047 47605541067119010270793571)
            ·
              refine ⟨71408311600678515406190357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47605541067119010270793571 71408311600678515406190357)
              ·
                refine ⟨3347264606281805409665173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71408311600678515406190357 3347264606281805409665173)
                ·
                  refine ⟨156903028419459628578055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3347264606281805409665173 156903028419459628578055)
                  ·
                    rfl

theorem cell22_1375054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_1375054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375054 prefixEnd_1375054 := by exact prefixLift 1375054
  have htrace : WordTrace (prefixWord ++ tailWord_1375054) baseStart_1375054 baseEnd_1375054 := by
    simpa [prefixWord, tailWord_1375054, baseEnd_1375054] using wordTrace_append hprefix tailTrace_1375054
  have hstable : (prefixWord ++ tailWord_1375054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375054).length < 2 ^ (prefixWord ++ tailWord_1375054).sum := by decide
  have hdescent : baseEnd_1375054 < baseStart_1375054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375056 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_1375056 : Nat := 118140960795 + 1375056 * 2 ^ 59
def prefixEnd_1375056 : Nat := 4983230072969 + 3 ^ 40 * 1375056 * 2
def baseEnd_1375056 : Nat := 470709769899251547184159

theorem tailTrace_1375056 : CollatzResearch.WordTrace tailWord_1375056 prefixEnd_1375056 470709769899251547184159 := by
  unfold tailWord_1375056
  simp only [CollatzResearch.WordTrace]
  refine ⟨25076206253207213856636511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33434941670942951808848681 25076206253207213856636511)
  ·
    refine ⟨37614309379810820784954767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25076206253207213856636511 37614309379810820784954767)
    ·
      refine ⟨56421464069716231177432151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37614309379810820784954767 56421464069716231177432151)
      ·
        refine ⟨84632196104574346766148227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56421464069716231177432151 84632196104574346766148227)
        ·
          refine ⟨126948294156861520149222341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84632196104574346766148227 126948294156861520149222341)
          ·
            refine ⟨23802805154411535027979189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126948294156861520149222341 23802805154411535027979189)
            ·
              refine ⟨2231512983226081408873049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23802805154411535027979189 2231512983226081408873049)
              ·
                refine ⟨1673634737419561056654787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231512983226081408873049 1673634737419561056654787)
                ·
                  refine ⟨2510452106129341584982181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673634737419561056654787 2510452106129341584982181)
                  ·
                    refine ⟨470709769899251547184159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510452106129341584982181 470709769899251547184159)
                    ·
                      rfl

theorem cell22_1375056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_1375056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375056 prefixEnd_1375056 := by exact prefixLift 1375056
  have htrace : WordTrace (prefixWord ++ tailWord_1375056) baseStart_1375056 baseEnd_1375056 := by
    simpa [prefixWord, tailWord_1375056, baseEnd_1375056] using wordTrace_append hprefix tailTrace_1375056
  have hstable : (prefixWord ++ tailWord_1375056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375056).length < 2 ^ (prefixWord ++ tailWord_1375056).sum := by decide
  have hdescent : baseEnd_1375056 < baseStart_1375056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375071 : List Nat := [1, 1, 2, 3, 1, 3, 2, 5, 4]
def baseStart_1375071 : Nat := 118140960795 + 1375071 * 2 ^ 59
def prefixEnd_1375071 : Nat := 4983230072969 + 3 ^ 40 * 1375071 * 2
def baseEnd_1375071 : Nat := 156904968235265502686371

theorem tailTrace_1375071 : CollatzResearch.WordTrace tailWord_1375071 prefixEnd_1375071 156904968235265502686371 := by
  unfold tailWord_1375071
  simp only [CollatzResearch.WordTrace]
  refine ⟨50152959601360085275069067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33435306400906723516712711 50152959601360085275069067)
  ·
    refine ⟨75229439402040127912603601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50152959601360085275069067 75229439402040127912603601)
    ·
      refine ⟨56422079551530095934452701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75229439402040127912603601 56422079551530095934452701)
      ·
        refine ⟨21158279831823785975419763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56422079551530095934452701 21158279831823785975419763)
        ·
          refine ⟨31737419747735678963129645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21158279831823785975419763 31737419747735678963129645)
          ·
            refine ⟨11901532405400879611173617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31737419747735678963129645 11901532405400879611173617)
            ·
              refine ⟨8926149304050659708380213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11901532405400879611173617 8926149304050659708380213)
              ·
                refine ⟨836826497254749347660645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8926149304050659708380213 836826497254749347660645)
                ·
                  refine ⟨156904968235265502686371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836826497254749347660645 156904968235265502686371)
                  ·
                    rfl

theorem cell22_1375071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 4].length) (baseStart_1375071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375071 prefixEnd_1375071 := by exact prefixLift 1375071
  have htrace : WordTrace (prefixWord ++ tailWord_1375071) baseStart_1375071 baseEnd_1375071 := by
    simpa [prefixWord, tailWord_1375071, baseEnd_1375071] using wordTrace_append hprefix tailTrace_1375071
  have hstable : (prefixWord ++ tailWord_1375071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375071).length < 2 ^ (prefixWord ++ tailWord_1375071).sum := by decide
  have hdescent : baseEnd_1375071 < baseStart_1375071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375088 : List Nat := [2, 1, 1, 1, 4, 1, 6, 2, 4]
def baseStart_1375088 : Nat := 118140960795 + 1375088 * 2 ^ 59
def prefixEnd_1375088 : Nat := 4983230072969 + 3 ^ 40 * 1375088 * 2
def baseEnd_1375088 : Nat := 156906908051071376794687

theorem tailTrace_1375088 : CollatzResearch.WordTrace tailWord_1375088 prefixEnd_1375088 156906908051071376794687 := by
  unfold tailWord_1375088
  simp only [CollatzResearch.WordTrace]
  refine ⟨25076789821149248589218959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33435719761532331452291945 25076789821149248589218959)
  ·
    refine ⟨37615184731723872883828439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25076789821149248589218959 37615184731723872883828439)
    ·
      refine ⟨56422777097585809325742659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37615184731723872883828439 56422777097585809325742659)
      ·
        refine ⟨84634165646378713988613989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56422777097585809325742659 84634165646378713988613989)
        ·
          refine ⟨15868906058696008872865123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84634165646378713988613989 15868906058696008872865123)
          ·
            refine ⟨23803359088044013309297685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15868906058696008872865123 23803359088044013309297685)
            ·
              refine ⟨1115782457252063123873329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23803359088044013309297685 1115782457252063123873329)
              ·
                refine ⟨836836842939047342904997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115782457252063123873329 836836842939047342904997)
                ·
                  refine ⟨156906908051071376794687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836836842939047342904997 156906908051071376794687)
                  ·
                    rfl

theorem cell22_1375088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_1375088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375088 prefixEnd_1375088 := by exact prefixLift 1375088
  have htrace : WordTrace (prefixWord ++ tailWord_1375088) baseStart_1375088 baseEnd_1375088 := by
    simpa [prefixWord, tailWord_1375088, baseEnd_1375088] using wordTrace_append hprefix tailTrace_1375088
  have hstable : (prefixWord ++ tailWord_1375088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375088).length < 2 ^ (prefixWord ++ tailWord_1375088).sum := by decide
  have hdescent : baseEnd_1375088 < baseStart_1375088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375099 : List Nat := [1, 1, 1, 1, 1, 5, 5, 7]
def baseStart_1375099 : Nat := 118140960795 + 1375099 * 2 ^ 59
def prefixEnd_1375099 : Nat := 4983230072969 + 3 ^ 40 * 1375099 * 2
def baseEnd_1375099 : Nat := 52302721075334863151003

theorem tailTrace_1375099 : CollatzResearch.WordTrace tailWord_1375099 prefixEnd_1375099 52302721075334863151003 := by
  unfold tailWord_1375099
  simp only [CollatzResearch.WordTrace]
  refine ⟨50153980845258646057088351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33435987230172430704725567 50153980845258646057088351)
  ·
    refine ⟨75230971267887969085632527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50153980845258646057088351 75230971267887969085632527)
    ·
      refine ⟨112846456901831953628448791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75230971267887969085632527 112846456901831953628448791)
      ·
        refine ⟨169269685352747930442673187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112846456901831953628448791 169269685352747930442673187)
        ·
          refine ⟨253904528029121895664009781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169269685352747930442673187 253904528029121895664009781)
          ·
            refine ⟨23803549502730177718500917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 253904528029121895664009781 23803549502730177718500917)
            ·
              refine ⟨2231582765880954161109461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23803549502730177718500917 2231582765880954161109461)
              ·
                refine ⟨52302721075334863151003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2231582765880954161109461 52302721075334863151003)
                ·
                  rfl

theorem cell22_1375099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 7].length) (baseStart_1375099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375099 prefixEnd_1375099 := by exact prefixLift 1375099
  have htrace : WordTrace (prefixWord ++ tailWord_1375099) baseStart_1375099 baseEnd_1375099 := by
    simpa [prefixWord, tailWord_1375099, baseEnd_1375099] using wordTrace_append hprefix tailTrace_1375099
  have hstable : (prefixWord ++ tailWord_1375099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375099).length < 2 ^ (prefixWord ++ tailWord_1375099).sum := by decide
  have hdescent : baseEnd_1375099 < baseStart_1375099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375182 : List Nat := [4, 1, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_1375182 : Nat := 118140960795 + 1375182 * 2 ^ 59
def prefixEnd_1375182 : Nat := 4983230072969 + 3 ^ 40 * 1375182 * 2
def baseEnd_1375182 : Nat := 470752902274229218533773

theorem tailTrace_1375182 : CollatzResearch.WordTrace tailWord_1375182 prefixEnd_1375182 470752902274229218533773 := by
  unfold tailWord_1375182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269626012994743904044975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33438005402638634154906533 6269626012994743904044975)
  ·
    refine ⟨9404439019492115856067463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6269626012994743904044975 9404439019492115856067463)
    ·
      refine ⟨14106658529238173784101195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9404439019492115856067463 14106658529238173784101195)
      ·
        refine ⟨21159987793857260676151793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14106658529238173784101195 21159987793857260676151793)
        ·
          refine ⟨15869990845392945507113845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21159987793857260676151793 15869990845392945507113845)
          ·
            refine ⟨1487811641755588641291923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15869990845392945507113845 1487811641755588641291923)
            ·
              refine ⟨2231717462633382961937885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487811641755588641291923 2231717462633382961937885)
              ·
                refine ⟨836894048487518610726707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2231717462633382961937885 836894048487518610726707)
                ·
                  refine ⟨1255341072731277916090061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836894048487518610726707 1255341072731277916090061)
                  ·
                    refine ⟨470752902274229218533773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1255341072731277916090061 470752902274229218533773)
                    ·
                      rfl

theorem cell22_1375182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_1375182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375182 prefixEnd_1375182 := by exact prefixLift 1375182
  have htrace : WordTrace (prefixWord ++ tailWord_1375182) baseStart_1375182 baseEnd_1375182 := by
    simpa [prefixWord, tailWord_1375182, baseEnd_1375182] using wordTrace_append hprefix tailTrace_1375182
  have hstable : (prefixWord ++ tailWord_1375182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375182).length < 2 ^ (prefixWord ++ tailWord_1375182).sum := by decide
  have hdescent : baseEnd_1375182 < baseStart_1375182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375250 : List Nat := [3, 2, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1375250 : Nat := 118140960795 + 1375250 * 2 ^ 59
def prefixEnd_1375250 : Nat := 4983230072969 + 3 ^ 40 * 1375250 * 2
def baseEnd_1375250 : Nat := 470776180063899707833565

theorem tailTrace_1375250 : CollatzResearch.WordTrace tailWord_1375250 prefixEnd_1375250 470776180063899707833565 := by
  unfold tailWord_1375250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539872066927899711458801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33439658845141065897223469 12539872066927899711458801)
  ·
    refine ⟨9404904050195924783594101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12539872066927899711458801 9404904050195924783594101)
    ·
      refine ⟨881709754705867948461947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9404904050195924783594101 881709754705867948461947)
      ·
        refine ⟨1322564632058801922692921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881709754705867948461947 1322564632058801922692921)
        ·
          refine ⟨991923474044101442019691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322564632058801922692921 991923474044101442019691)
          ·
            refine ⟨1487885211066152163029537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991923474044101442019691 1487885211066152163029537)
            ·
              refine ⟨1115913908299614122272153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487885211066152163029537 1115913908299614122272153)
              ·
                refine ⟨836935431224710591704115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115913908299614122272153 836935431224710591704115)
                ·
                  refine ⟨1255403146837065887556173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836935431224710591704115 1255403146837065887556173)
                  ·
                    refine ⟨470776180063899707833565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1255403146837065887556173 470776180063899707833565)
                    ·
                      rfl

theorem cell22_1375250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1375250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375250 prefixEnd_1375250 := by exact prefixLift 1375250
  have htrace : WordTrace (prefixWord ++ tailWord_1375250) baseStart_1375250 baseEnd_1375250 := by
    simpa [prefixWord, tailWord_1375250, baseEnd_1375250] using wordTrace_append hprefix tailTrace_1375250
  have hstable : (prefixWord ++ tailWord_1375250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375250).length < 2 ^ (prefixWord ++ tailWord_1375250).sum := by decide
  have hdescent : baseEnd_1375250 < baseStart_1375250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375253 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1375253 : Nat := 118140960795 + 1375253 * 2 ^ 59
def prefixEnd_1375253 : Nat := 4983230072969 + 3 ^ 40 * 1375253 * 2
def baseEnd_1375253 : Nat := 470777207025208700008555

theorem tailTrace_1375253 : CollatzResearch.WordTrace tailWord_1375253 prefixEnd_1375253 470777207025208700008555 := by
  unfold tailWord_1375253
  simp only [CollatzResearch.WordTrace]
  refine ⟨50159597686700730358194413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33439731791133820238796275 50159597686700730358194413)
  ·
    refine ⟨18809849132512773884322905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50159597686700730358194413 18809849132512773884322905)
    ·
      refine ⟨14107386849384580413242179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18809849132512773884322905 14107386849384580413242179)
      ·
        refine ⟨21161080274076870619863269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14107386849384580413242179 21161080274076870619863269)
        ·
          refine ⟨3967702551389413241224363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21161080274076870619863269 3967702551389413241224363)
          ·
            refine ⟨5951553827084119861836545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967702551389413241224363 5951553827084119861836545)
            ·
              refine ⟨4463665370313089896377409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5951553827084119861836545 4463665370313089896377409)
              ·
                refine ⟨3347749027734817422283057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4463665370313089896377409 3347749027734817422283057)
                ·
                  refine ⟨2510811770801113066712293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3347749027734817422283057 2510811770801113066712293)
                  ·
                    refine ⟨470777207025208700008555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2510811770801113066712293 470777207025208700008555)
                    ·
                      rfl

theorem cell22_1375253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1375253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375253 prefixEnd_1375253 := by exact prefixLift 1375253
  have htrace : WordTrace (prefixWord ++ tailWord_1375253) baseStart_1375253 baseEnd_1375253 := by
    simpa [prefixWord, tailWord_1375253, baseEnd_1375253] using wordTrace_append hprefix tailTrace_1375253
  have hstable : (prefixWord ++ tailWord_1375253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375253).length < 2 ^ (prefixWord ++ tailWord_1375253).sum := by decide
  have hdescent : baseEnd_1375253 < baseStart_1375253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375255 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 2, 3]
def baseStart_1375255 : Nat := 118140960795 + 1375255 * 2 ^ 59
def prefixEnd_1375255 : Nat := 4983230072969 + 3 ^ 40 * 1375255 * 2
def baseEnd_1375255 : Nat := 470777891666081361458549

theorem tailTrace_1375255 : CollatzResearch.WordTrace tailWord_1375255 prefixEnd_1375255 470777891666081361458549 := by
  unfold tailWord_1375255
  simp only [CollatzResearch.WordTrace]
  refine ⟨50159670632693484699767219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33439780421795656466511479 50159670632693484699767219)
  ·
    refine ⟨75239505949040227049650829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50159670632693484699767219 75239505949040227049650829)
    ·
      refine ⟨28214814730890085143619061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75239505949040227049650829 28214814730890085143619061)
      ·
        refine ⟨2645138881020945482214287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28214814730890085143619061 2645138881020945482214287)
        ·
          refine ⟨3967708321531418223321431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645138881020945482214287 3967708321531418223321431)
          ·
            refine ⟨5951562482297127334982147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967708321531418223321431 5951562482297127334982147)
            ·
              refine ⟨8927343723445691002473221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951562482297127334982147 8927343723445691002473221)
              ·
                refine ⟨1673876948146067062963729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8927343723445691002473221 1673876948146067062963729)
                ·
                  refine ⟨1255407711109550297222797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1673876948146067062963729 1255407711109550297222797)
                  ·
                    refine ⟨470777891666081361458549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1255407711109550297222797 470777891666081361458549)
                    ·
                      rfl

theorem cell22_1375255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_1375255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375255 prefixEnd_1375255 := by exact prefixLift 1375255
  have htrace : WordTrace (prefixWord ++ tailWord_1375255) baseStart_1375255 baseEnd_1375255 := by
    simpa [prefixWord, tailWord_1375255, baseEnd_1375255] using wordTrace_append hprefix tailTrace_1375255
  have hstable : (prefixWord ++ tailWord_1375255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375255).length < 2 ^ (prefixWord ++ tailWord_1375255).sum := by decide
  have hdescent : baseEnd_1375255 < baseStart_1375255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375268 : List Nat := [2, 3, 1, 4, 1, 1, 3, 7]
def baseStart_1375268 : Nat := 118140960795 + 1375268 * 2 ^ 59
def prefixEnd_1375268 : Nat := 4983230072969 + 3 ^ 40 * 1375268 * 2
def baseEnd_1375268 : Nat := 52309149092417073431501

theorem tailTrace_1375268 : CollatzResearch.WordTrace tailWord_1375268 prefixEnd_1375268 52309149092417073431501 := by
  unfold tailWord_1375268
  simp only [CollatzResearch.WordTrace]
  refine ⟨25080072390823193959995229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33440096521097591946660305 25080072390823193959995229)
  ·
    refine ⟨9405027146558697734998211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25080072390823193959995229 9405027146558697734998211)
    ·
      refine ⟨14107540719838046602497317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9405027146558697734998211 14107540719838046602497317)
      ·
        refine ⟨2645163884969633737968247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14107540719838046602497317 2645163884969633737968247)
        ·
          refine ⟨3967745827454450606952371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645163884969633737968247 3967745827454450606952371)
          ·
            refine ⟨5951618741181675910428557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967745827454450606952371 5951618741181675910428557)
            ·
              refine ⟨2231857027943128466410709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5951618741181675910428557 2231857027943128466410709)
              ·
                refine ⟨52309149092417073431501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2231857027943128466410709 52309149092417073431501)
                ·
                  rfl

theorem cell22_1375268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 7].length) (baseStart_1375268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375268 prefixEnd_1375268 := by exact prefixLift 1375268
  have htrace : WordTrace (prefixWord ++ tailWord_1375268) baseStart_1375268 baseEnd_1375268 := by
    simpa [prefixWord, tailWord_1375268, baseEnd_1375268] using wordTrace_append hprefix tailTrace_1375268
  have hstable : (prefixWord ++ tailWord_1375268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375268).length < 2 ^ (prefixWord ++ tailWord_1375268).sum := by decide
  have hdescent : baseEnd_1375268 < baseStart_1375268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375281 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_1375281 : Nat := 118140960795 + 1375281 * 2 ^ 59
def prefixEnd_1375281 : Nat := 4983230072969 + 3 ^ 40 * 1375281 * 2
def baseEnd_1375281 : Nat := 470786791997425960308469

theorem tailTrace_1375281 : CollatzResearch.WordTrace tailWord_1375281 prefixEnd_1375281 470786791997425960308469 := by
  unfold tailWord_1375281
  simp only [CollatzResearch.WordTrace]
  refine ⟨50160618930599291140213697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33440412620399527426809131 50160618930599291140213697)
  ·
    refine ⟨37620464197949468355160273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50160618930599291140213697 37620464197949468355160273)
    ·
      refine ⟨28215348148462101266370205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37620464197949468355160273 28215348148462101266370205)
      ·
        refine ⟨10580755555673287974888827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28215348148462101266370205 10580755555673287974888827)
        ·
          refine ⟨15871133333509931962333241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10580755555673287974888827 15871133333509931962333241)
          ·
            refine ⟨11903350000132448971749931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15871133333509931962333241 11903350000132448971749931)
            ·
              refine ⟨17855025000198673457624897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11903350000132448971749931 17855025000198673457624897)
              ·
                refine ⟨13391268750149005093218673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17855025000198673457624897 13391268750149005093218673)
                ·
                  refine ⟨10043451562611753819914005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13391268750149005093218673 10043451562611753819914005)
                  ·
                    refine ⟨470786791997425960308469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10043451562611753819914005 470786791997425960308469)
                    ·
                      rfl

theorem cell22_1375281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_1375281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375281 prefixEnd_1375281 := by exact prefixLift 1375281
  have htrace : WordTrace (prefixWord ++ tailWord_1375281) baseStart_1375281 baseEnd_1375281 := by
    simpa [prefixWord, tailWord_1375281, baseEnd_1375281] using wordTrace_append hprefix tailTrace_1375281
  have hstable : (prefixWord ++ tailWord_1375281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375281).length < 2 ^ (prefixWord ++ tailWord_1375281).sum := by decide
  have hdescent : baseEnd_1375281 < baseStart_1375281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375296 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 7]
def baseStart_1375296 : Nat := 118140960795 + 1375296 * 2 ^ 59
def prefixEnd_1375296 : Nat := 4983230072969 + 3 ^ 40 * 1375296 * 2
def baseEnd_1375296 : Nat := 156930642267990307061141

theorem tailTrace_1375296 : CollatzResearch.WordTrace tailWord_1375296 prefixEnd_1375296 156930642267990307061141 := by
  unfold tailWord_1375296
  simp only [CollatzResearch.WordTrace]
  refine ⟨25080583012772474351004871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33440777350363299134673161 25080583012772474351004871)
  ·
    refine ⟨37620874519158711526507307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25080583012772474351004871 37620874519158711526507307)
    ·
      refine ⟨56431311778738067289760961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37620874519158711526507307 56431311778738067289760961)
      ·
        refine ⟨42323483834053550467320721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56431311778738067289760961 42323483834053550467320721)
        ·
          refine ⟨31742612875540162850490541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42323483834053550467320721 31742612875540162850490541)
          ·
            refine ⟨11903479828327561068933953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31742612875540162850490541 11903479828327561068933953)
            ·
              refine ⟨8927609871245670801700465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11903479828327561068933953 8927609871245670801700465)
              ·
                refine ⟨6695707403434253101275349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8927609871245670801700465 6695707403434253101275349)
                ·
                  refine ⟨156930642267990307061141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6695707403434253101275349 156930642267990307061141)
                  ·
                    rfl

theorem cell22_1375296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_1375296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375296 prefixEnd_1375296 := by exact prefixLift 1375296
  have htrace : WordTrace (prefixWord ++ tailWord_1375296) baseStart_1375296 baseEnd_1375296 := by
    simpa [prefixWord, tailWord_1375296, baseEnd_1375296] using wordTrace_append hprefix tailTrace_1375296
  have hstable : (prefixWord ++ tailWord_1375296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375296).length < 2 ^ (prefixWord ++ tailWord_1375296).sum := by decide
  have hdescent : baseEnd_1375296 < baseStart_1375296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375313 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 5]
def baseStart_1375313 : Nat := 118140960795 + 1375313 * 2 ^ 59
def prefixEnd_1375313 : Nat := 4983230072969 + 3 ^ 40 * 1375313 * 2
def baseEnd_1375313 : Nat := 156932582083796181169457

theorem tailTrace_1375313 : CollatzResearch.WordTrace tailWord_1375313 prefixEnd_1375313 156932582083796181169457 := by
  unfold tailWord_1375313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50161786066483360605378593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33441190710988907070252395 50161786066483360605378593)
  ·
    refine ⟨37621339549862520454033945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50161786066483360605378593 37621339549862520454033945)
    ·
      refine ⟨28216004662396890340525459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37621339549862520454033945 28216004662396890340525459)
      ·
        refine ⟨42324006993595335510788189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28216004662396890340525459 42324006993595335510788189)
        ·
          refine ⟨15871502622598250816545571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42324006993595335510788189 15871502622598250816545571)
          ·
            refine ⟨23807253933897376224818357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15871502622598250816545571 23807253933897376224818357)
            ·
              refine ⟨2231930056302879021076721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23807253933897376224818357 2231930056302879021076721)
              ·
                refine ⟨1673947542227159265807541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231930056302879021076721 1673947542227159265807541)
                ·
                  refine ⟨156932582083796181169457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1673947542227159265807541 156932582083796181169457)
                  ·
                    rfl

theorem cell22_1375313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_1375313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375313 prefixEnd_1375313 := by exact prefixLift 1375313
  have htrace : WordTrace (prefixWord ++ tailWord_1375313) baseStart_1375313 baseEnd_1375313 := by
    simpa [prefixWord, tailWord_1375313, baseEnd_1375313] using wordTrace_append hprefix tailTrace_1375313
  have hstable : (prefixWord ++ tailWord_1375313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375313).length < 2 ^ (prefixWord ++ tailWord_1375313).sum := by decide
  have hdescent : baseEnd_1375313 < baseStart_1375313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375394 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1375394 : Nat := 118140960795 + 1375394 * 2 ^ 59
def prefixEnd_1375394 : Nat := 4983230072969 + 3 ^ 40 * 1375394 * 2
def baseEnd_1375394 : Nat := 470825474206731332233123

theorem tailTrace_1375394 : CollatzResearch.WordTrace tailWord_1375394 prefixEnd_1375394 470825474206731332233123 := by
  unfold tailWord_1375394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12541185094797477859769309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33443160252793274292718157 12541185094797477859769309)
  ·
    refine ⟨4702944410549054197413491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12541185094797477859769309 4702944410549054197413491)
    ·
      refine ⟨7054416615823581296120237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4702944410549054197413491 7054416615823581296120237)
      ·
        refine ⟨2645406230933842986045089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7054416615823581296120237 2645406230933842986045089)
        ·
          refine ⟨1984054673200382239533817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2645406230933842986045089 1984054673200382239533817)
          ·
            refine ⟨1488041004900286679650363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1984054673200382239533817 1488041004900286679650363)
            ·
              refine ⟨2232061507350430019475545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488041004900286679650363 2232061507350430019475545)
              ·
                refine ⟨1674046130512822514606659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232061507350430019475545 1674046130512822514606659)
                ·
                  refine ⟨2511069195769233771909989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674046130512822514606659 2511069195769233771909989)
                  ·
                    refine ⟨470825474206731332233123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2511069195769233771909989 470825474206731332233123)
                    ·
                      rfl

theorem cell22_1375394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1375394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375394 prefixEnd_1375394 := by exact prefixLift 1375394
  have htrace : WordTrace (prefixWord ++ tailWord_1375394) baseStart_1375394 baseEnd_1375394 := by
    simpa [prefixWord, tailWord_1375394, baseEnd_1375394] using wordTrace_append hprefix tailTrace_1375394
  have hstable : (prefixWord ++ tailWord_1375394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375394).length < 2 ^ (prefixWord ++ tailWord_1375394).sum := by decide
  have hdescent : baseEnd_1375394 < baseStart_1375394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375426 : List Nat := [3, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1375426 : Nat := 118140960795 + 1375426 * 2 ^ 59
def prefixEnd_1375426 : Nat := 4983230072969 + 3 ^ 40 * 1375426 * 2
def baseEnd_1375426 : Nat := 156945476153564638477675

theorem tailTrace_1375426 : CollatzResearch.WordTrace tailWord_1375426 prefixEnd_1375426 156945476153564638477675 := by
  unfold tailWord_1375426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12541476878768495226060533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33443938343382653936161421 12541476878768495226060533)
  ·
    refine ⟨1175763457384546427443175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12541476878768495226060533 1175763457384546427443175)
    ·
      refine ⟨1763645186076819641164763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175763457384546427443175 1763645186076819641164763)
      ·
        refine ⟨2645467779115229461747145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763645186076819641164763 2645467779115229461747145)
        ·
          refine ⟨1984100834336422096310359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2645467779115229461747145 1984100834336422096310359)
          ·
            refine ⟨2976151251504633144465539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984100834336422096310359 2976151251504633144465539)
            ·
              refine ⟨4464226877256949716698309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976151251504633144465539 4464226877256949716698309)
              ·
                refine ⟨837042539485678071880933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4464226877256949716698309 837042539485678071880933)
                ·
                  refine ⟨156945476153564638477675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837042539485678071880933 156945476153564638477675)
                  ·
                    rfl

theorem cell22_1375426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1375426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375426 prefixEnd_1375426 := by exact prefixLift 1375426
  have htrace : WordTrace (prefixWord ++ tailWord_1375426) baseStart_1375426 baseEnd_1375426 := by
    simpa [prefixWord, tailWord_1375426, baseEnd_1375426] using wordTrace_append hprefix tailTrace_1375426
  have hstable : (prefixWord ++ tailWord_1375426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375426).length < 2 ^ (prefixWord ++ tailWord_1375426).sum := by decide
  have hdescent : baseEnd_1375426 < baseStart_1375426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375469 : List Nat := [1, 5, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_1375469 : Nat := 118140960795 + 1375469 * 2 ^ 59
def prefixEnd_1375469 : Nat := 4983230072969 + 3 ^ 40 * 1375469 * 2
def baseEnd_1375469 : Nat := 470851148239456136607893

theorem tailTrace_1375469 : CollatzResearch.WordTrace tailWord_1375469 prefixEnd_1375469 470851148239456136607893 := by
  unfold tailWord_1375469
  simp only [CollatzResearch.WordTrace]
  refine ⟨50167475853918199248057461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33444983902612132832038307 50167475853918199248057461)
  ·
    refine ⟨4703200861304831179505387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50167475853918199248057461 4703200861304831179505387)
    ·
      refine ⟨7054801291957246769258081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4703200861304831179505387 7054801291957246769258081)
      ·
        refine ⟨5291100968967935076943561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7054801291957246769258081 5291100968967935076943561)
        ·
          refine ⟨3968325726725951307707671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5291100968967935076943561 3968325726725951307707671)
          ·
            refine ⟨5952488590088926961561507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968325726725951307707671 5952488590088926961561507)
            ·
              refine ⟨8928732885133390442342261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5952488590088926961561507 8928732885133390442342261)
              ·
                refine ⟨837068707981255353969587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8928732885133390442342261 837068707981255353969587)
                ·
                  refine ⟨1255603061971883030954381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837068707981255353969587 1255603061971883030954381)
                  ·
                    refine ⟨470851148239456136607893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1255603061971883030954381 470851148239456136607893)
                    ·
                      rfl

theorem cell22_1375469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_1375469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375469 prefixEnd_1375469 := by exact prefixLift 1375469
  have htrace : WordTrace (prefixWord ++ tailWord_1375469) baseStart_1375469 baseEnd_1375469 := by
    simpa [prefixWord, tailWord_1375469, baseEnd_1375469] using wordTrace_append hprefix tailTrace_1375469
  have hstable : (prefixWord ++ tailWord_1375469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375469).length < 2 ^ (prefixWord ++ tailWord_1375469).sum := by decide
  have hdescent : baseEnd_1375469 < baseStart_1375469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375512 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_1375512 : Nat := 118140960795 + 1375512 * 2 ^ 59
def prefixEnd_1375512 : Nat := 4983230072969 + 3 ^ 40 * 1375512 * 2
def baseEnd_1375512 : Nat := 470865868018218357782761

theorem tailTrace_1375512 : CollatzResearch.WordTrace tailWord_1375512 prefixEnd_1375512 470865868018218357782761 := by
  unfold tailWord_1375512
  simp only [CollatzResearch.WordTrace]
  refine ⟨25084522096381208795936395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33446029461841611727915193 25084522096381208795936395)
  ·
    refine ⟨37626783144571813193904593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25084522096381208795936395 37626783144571813193904593)
    ·
      refine ⟨28220087358428859895428445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37626783144571813193904593 28220087358428859895428445)
      ·
        refine ⟨10582532759410822460785667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28220087358428859895428445 10582532759410822460785667)
        ·
          refine ⟨15873799139116233691178501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10582532759410822460785667 15873799139116233691178501)
          ·
            refine ⟨2976337338584293817095969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15873799139116233691178501 2976337338584293817095969)
            ·
              refine ⟨2232253003938220362821977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2976337338584293817095969 2232253003938220362821977)
              ·
                refine ⟨1674189752953665272116483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232253003938220362821977 1674189752953665272116483)
                ·
                  refine ⟨2511284629430497908174725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674189752953665272116483 2511284629430497908174725)
                  ·
                    refine ⟨470865868018218357782761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2511284629430497908174725 470865868018218357782761)
                    ·
                      rfl

theorem cell22_1375512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_1375512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375512 prefixEnd_1375512 := by exact prefixLift 1375512
  have htrace : WordTrace (prefixWord ++ tailWord_1375512) baseStart_1375512 baseEnd_1375512 := by
    simpa [prefixWord, tailWord_1375512, baseEnd_1375512] using wordTrace_append hprefix tailTrace_1375512
  have hstable : (prefixWord ++ tailWord_1375512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375512).length < 2 ^ (prefixWord ++ tailWord_1375512).sum := by decide
  have hdescent : baseEnd_1375512 < baseStart_1375512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375559 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 2, 3]
def baseStart_1375559 : Nat := 118140960795 + 1375559 * 2 ^ 59
def prefixEnd_1375559 : Nat := 4983230072969 + 3 ^ 40 * 1375559 * 2
def baseEnd_1375559 : Nat := 470881957078725901857617

theorem tailTrace_1375559 : CollatzResearch.WordTrace tailWord_1375559 prefixEnd_1375559 470881957078725901857617 := by
  unfold tailWord_1375559
  simp only [CollatzResearch.WordTrace]
  refine ⟨50170758423592144618833731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33447172282394763079222487 50170758423592144618833731)
  ·
    refine ⟨75256137635388216928250597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50170758423592144618833731 75256137635388216928250597)
    ·
      refine ⟨14110525806635290674046987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75256137635388216928250597 14110525806635290674046987)
      ·
        refine ⟨21165788709952936011070481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14110525806635290674046987 21165788709952936011070481)
        ·
          refine ⟨15874341532464702008302861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21165788709952936011070481 15874341532464702008302861)
          ·
            refine ⟨5952878074674263253113573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15874341532464702008302861 5952878074674263253113573)
            ·
              refine ⟨1116164639001424359958795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5952878074674263253113573 1116164639001424359958795)
              ·
                refine ⟨1674246958502136539938193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116164639001424359958795 1674246958502136539938193)
                ·
                  refine ⟨1255685218876602404953645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674246958502136539938193 1255685218876602404953645)
                  ·
                    refine ⟨470881957078725901857617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1255685218876602404953645 470881957078725901857617)
                    ·
                      rfl

theorem cell22_1375559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_1375559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375559 prefixEnd_1375559 := by exact prefixLift 1375559
  have htrace : WordTrace (prefixWord ++ tailWord_1375559) baseStart_1375559 baseEnd_1375559 := by
    simpa [prefixWord, tailWord_1375559, baseEnd_1375559] using wordTrace_append hprefix tailTrace_1375559
  have hstable : (prefixWord ++ tailWord_1375559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375559).length < 2 ^ (prefixWord ++ tailWord_1375559).sum := by decide
  have hdescent : baseEnd_1375559 < baseStart_1375559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375660 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1375660 : Nat := 118140960795 + 1375660 * 2 ^ 59
def prefixEnd_1375660 : Nat := 4983230072969 + 3 ^ 40 * 1375660 * 2
def baseEnd_1375660 : Nat := 470916531442795305082307

theorem tailTrace_1375660 : CollatzResearch.WordTrace tailWord_1375660 prefixEnd_1375660 470916531442795305082307 := by
  unfold tailWord_1375660
  simp only [CollatzResearch.WordTrace]
  refine ⟨25087221098113119434130217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33449628130817492578840289 25087221098113119434130217)
  ·
    refine ⟨18815415823584839575597663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25087221098113119434130217 18815415823584839575597663)
    ·
      refine ⟨28223123735377259363396495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18815415823584839575597663 28223123735377259363396495)
      ·
        refine ⟨42334685603065889045094743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28223123735377259363396495 42334685603065889045094743)
        ·
          refine ⟨63502028404598833567642115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42334685603065889045094743 63502028404598833567642115)
          ·
            refine ⟨95253042606898250351463173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63502028404598833567642115 95253042606898250351463173)
            ·
              refine ⟨17859945488793421940899345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95253042606898250351463173 17859945488793421940899345)
              ·
                refine ⟨13394959116595066455674509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17859945488793421940899345 13394959116595066455674509)
                ·
                  refine ⟨5023109668723149920877941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13394959116595066455674509 5023109668723149920877941)
                  ·
                    refine ⟨470916531442795305082307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5023109668723149920877941 470916531442795305082307)
                    ·
                      rfl

theorem cell22_1375660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1375660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375660 prefixEnd_1375660 := by exact prefixLift 1375660
  have htrace : WordTrace (prefixWord ++ tailWord_1375660) baseStart_1375660 baseEnd_1375660 := by
    simpa [prefixWord, tailWord_1375660, baseEnd_1375660] using wordTrace_append hprefix tailTrace_1375660
  have hstable : (prefixWord ++ tailWord_1375660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375660).length < 2 ^ (prefixWord ++ tailWord_1375660).sum := by decide
  have hdescent : baseEnd_1375660 < baseStart_1375660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375692 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1375692 : Nat := 118140960795 + 1375692 * 2 ^ 59
def prefixEnd_1375692 : Nat := 4983230072969 + 3 ^ 40 * 1375692 * 2
def baseEnd_1375692 : Nat := 470927485696757888282209

theorem tailTrace_1375692 : CollatzResearch.WordTrace tailWord_1375692 prefixEnd_1375692 470927485696757888282209 := by
  unfold tailWord_1375692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25087804666055154166712665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33450406221406872222283553 25087804666055154166712665)
  ·
    refine ⟨18815853499541365625034499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25087804666055154166712665 18815853499541365625034499)
    ·
      refine ⟨28223780249312048437551749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18815853499541365625034499 28223780249312048437551749)
      ·
        refine ⟨5291958796746009082040953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28223780249312048437551749 5291958796746009082040953)
        ·
          refine ⟨3968969097559506811530715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5291958796746009082040953 3968969097559506811530715)
          ·
            refine ⟨5953453646339260217296073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968969097559506811530715 5953453646339260217296073)
            ·
              refine ⟨4465090234754445162972055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5953453646339260217296073 4465090234754445162972055)
              ·
                refine ⟨6697635352131667744458083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4465090234754445162972055 6697635352131667744458083)
                ·
                  refine ⟨10046453028197501616687125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6697635352131667744458083 10046453028197501616687125)
                  ·
                    refine ⟨470927485696757888282209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10046453028197501616687125 470927485696757888282209)
                    ·
                      rfl

theorem cell22_1375692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1375692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375692 prefixEnd_1375692 := by exact prefixLift 1375692
  have htrace : WordTrace (prefixWord ++ tailWord_1375692) baseStart_1375692 baseEnd_1375692 := by
    simpa [prefixWord, tailWord_1375692, baseEnd_1375692] using wordTrace_append hprefix tailTrace_1375692
  have hstable : (prefixWord ++ tailWord_1375692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375692).length < 2 ^ (prefixWord ++ tailWord_1375692).sum := by decide
  have hdescent : baseEnd_1375692 < baseStart_1375692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375709 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1375709 : Nat := 118140960795 + 1375709 * 2 ^ 59
def prefixEnd_1375709 : Nat := 4983230072969 + 3 ^ 40 * 1375709 * 2
def baseEnd_1375709 : Nat := 470933305144175510607157

theorem tailTrace_1375709 : CollatzResearch.WordTrace tailWord_1375709 prefixEnd_1375709 470933305144175510607157 := by
  unfold tailWord_1375709
  simp only [CollatzResearch.WordTrace]
  refine ⟨50176229373048720236794181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33450819582032480157862787 50176229373048720236794181)
  ·
    refine ⟨9408043007446635044398909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50176229373048720236794181 9408043007446635044398909)
    ·
      refine ⟨3528016127792488141649591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9408043007446635044398909 3528016127792488141649591)
      ·
        refine ⟨5292024191688732212474387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528016127792488141649591 5292024191688732212474387)
        ·
          refine ⟨7938036287533098318711581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292024191688732212474387 7938036287533098318711581)
          ·
            refine ⟨2976763607824911869516843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7938036287533098318711581 2976763607824911869516843)
            ·
              refine ⟨4465145411737367804275265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976763607824911869516843 4465145411737367804275265)
              ·
                refine ⟨3348859058803025853206449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4465145411737367804275265 3348859058803025853206449)
                ·
                  refine ⟨2511644294102269389904837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3348859058803025853206449 2511644294102269389904837)
                  ·
                    refine ⟨470933305144175510607157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2511644294102269389904837 470933305144175510607157)
                    ·
                      rfl

theorem cell22_1375709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1375709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375709 prefixEnd_1375709 := by exact prefixLift 1375709
  have htrace : WordTrace (prefixWord ++ tailWord_1375709) baseStart_1375709 baseEnd_1375709 := by
    simpa [prefixWord, tailWord_1375709, baseEnd_1375709] using wordTrace_append hprefix tailTrace_1375709
  have hstable : (prefixWord ++ tailWord_1375709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375709).length < 2 ^ (prefixWord ++ tailWord_1375709).sum := by decide
  have hdescent : baseEnd_1375709 < baseStart_1375709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375735 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 9]
def baseStart_1375735 : Nat := 118140960795 + 1375735 * 2 ^ 59
def prefixEnd_1375735 : Nat := 4983230072969 + 3 ^ 40 * 1375735 * 2
def baseEnd_1375735 : Nat := 156980735158506703152359

theorem tailTrace_1375735 : CollatzResearch.WordTrace tailWord_1375735 prefixEnd_1375735 156980735158506703152359 := by
  unfold tailWord_1375735
  simp only [CollatzResearch.WordTrace]
  refine ⟨50177177670954526677240659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33451451780636351118160439 50177177670954526677240659)
  ·
    refine ⟨75265766506431790015860989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50177177670954526677240659 75265766506431790015860989)
    ·
      refine ⟨28224662439911921255947871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75265766506431790015860989 28224662439911921255947871)
      ·
        refine ⟨42336993659867881883921807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28224662439911921255947871 42336993659867881883921807)
        ·
          refine ⟨63505490489801822825882711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42336993659867881883921807 63505490489801822825882711)
          ·
            refine ⟨95258235734702734238824067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63505490489801822825882711 95258235734702734238824067)
            ·
              refine ⟨142887353602054101358236101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95258235734702734238824067 142887353602054101358236101)
              ·
                refine ⟨26791378800385144004669269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142887353602054101358236101 26791378800385144004669269)
                ·
                  refine ⟨156980735158506703152359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26791378800385144004669269 156980735158506703152359)
                  ·
                    rfl

theorem cell22_1375735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 9].length) (baseStart_1375735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375735 prefixEnd_1375735 := by exact prefixLift 1375735
  have htrace : WordTrace (prefixWord ++ tailWord_1375735) baseStart_1375735 baseEnd_1375735 := by
    simpa [prefixWord, tailWord_1375735, baseEnd_1375735] using wordTrace_append hprefix tailTrace_1375735
  have hstable : (prefixWord ++ tailWord_1375735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375735).length < 2 ^ (prefixWord ++ tailWord_1375735).sum := by decide
  have hdescent : baseEnd_1375735 < baseStart_1375735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375797 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 8]
def baseStart_1375797 : Nat := 118140960795 + 1375797 * 2 ^ 59
def prefixEnd_1375797 : Nat := 4983230072969 + 3 ^ 40 * 1375797 * 2
def baseEnd_1375797 : Nat := 156987809780857538135629

theorem tailTrace_1375797 : CollatzResearch.WordTrace tailWord_1375797 prefixEnd_1375797 156987809780857538135629 := by
  unfold tailWord_1375797
  simp only [CollatzResearch.WordTrace]
  refine ⟨50179438996729911265997645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33452959331153274177331763 50179438996729911265997645)
  ·
    refine ⟨18817289623773716724749117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50179438996729911265997645 18817289623773716724749117)
    ·
      refine ⟨7056483608915143771780919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18817289623773716724749117 7056483608915143771780919)
      ·
        refine ⟨10584725413372715657671379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7056483608915143771780919 10584725413372715657671379)
        ·
          refine ⟨15877088120059073486507069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10584725413372715657671379 15877088120059073486507069)
          ·
            refine ⟨5953908045022152557440151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15877088120059073486507069 5953908045022152557440151)
            ·
              refine ⟨8930862067533228836160227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953908045022152557440151 8930862067533228836160227)
              ·
                refine ⟨13396293101299843254240341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8930862067533228836160227 13396293101299843254240341)
                ·
                  refine ⟨156987809780857538135629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13396293101299843254240341 156987809780857538135629)
                  ·
                    rfl

theorem cell22_1375797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_1375797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375797 prefixEnd_1375797 := by exact prefixLift 1375797
  have htrace : WordTrace (prefixWord ++ tailWord_1375797) baseStart_1375797 baseEnd_1375797 := by
    simpa [prefixWord, tailWord_1375797, baseEnd_1375797] using wordTrace_append hprefix tailTrace_1375797
  have hstable : (prefixWord ++ tailWord_1375797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375797).length < 2 ^ (prefixWord ++ tailWord_1375797).sum := by decide
  have hdescent : baseEnd_1375797 < baseStart_1375797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375876 : List Nat := [2, 3, 2, 1, 5, 1, 8]
def baseStart_1375876 : Nat := 118140960795 + 1375876 * 2 ^ 59
def prefixEnd_1375876 : Nat := 4983230072969 + 3 ^ 40 * 1375876 * 2
def baseEnd_1375876 : Nat := 17444091579890471914135

theorem tailTrace_1375876 : CollatzResearch.WordTrace tailWord_1375876 prefixEnd_1375876 17444091579890471914135 := by
  unfold tailWord_1375876
  simp only [CollatzResearch.WordTrace]
  refine ⟨25091160181721853879061741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33454880242295805172082321 25091160181721853879061741)
  ·
    refine ⟨9409185068145695204648153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25091160181721853879061741 9409185068145695204648153)
    ·
      refine ⟨7056888801109271403486115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9409185068145695204648153 7056888801109271403486115)
      ·
        refine ⟨10585333201663907105229173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7056888801109271403486115 10585333201663907105229173)
        ·
          refine ⟨992374987655991291115235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10585333201663907105229173 992374987655991291115235)
          ·
            refine ⟨1488562481483986936672853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992374987655991291115235 1488562481483986936672853)
            ·
              refine ⟨17444091579890471914135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1488562481483986936672853 17444091579890471914135)
              ·
                rfl

theorem cell22_1375876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 8].length) (baseStart_1375876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375876 prefixEnd_1375876 := by exact prefixLift 1375876
  have htrace : WordTrace (prefixWord ++ tailWord_1375876) baseStart_1375876 baseEnd_1375876 := by
    simpa [prefixWord, tailWord_1375876, baseEnd_1375876] using wordTrace_append hprefix tailTrace_1375876
  have hstable : (prefixWord ++ tailWord_1375876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375876).length < 2 ^ (prefixWord ++ tailWord_1375876).sum := by decide
  have hdescent : baseEnd_1375876 < baseStart_1375876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1375981 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1375981 : Nat := 118140960795 + 1375981 * 2 ^ 59
def prefixEnd_1375981 : Nat := 4983230072969 + 3 ^ 40 * 1375981 * 2
def baseEnd_1375981 : Nat := 471026416302857467806323

theorem tailTrace_1375981 : CollatzResearch.WordTrace tailWord_1375981 prefixEnd_1375981 471026416302857467806323 := by
  unfold tailWord_1375981
  simp only [CollatzResearch.WordTrace]
  refine ⟨50186150028063310690695797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33457433352042207127130531 50186150028063310690695797)
  ·
    refine ⟨4704951565130935377252731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50186150028063310690695797 4704951565130935377252731)
    ·
      refine ⟨7057427347696403065879097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4704951565130935377252731 7057427347696403065879097)
      ·
        refine ⟨5293070510772302299409323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7057427347696403065879097 5293070510772302299409323)
        ·
          refine ⟨7939605766158453449113985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293070510772302299409323 7939605766158453449113985)
          ·
            refine ⟨5954704324618840086835489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7939605766158453449113985 5954704324618840086835489)
            ·
              refine ⟨4466028243464130065126617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5954704324618840086835489 4466028243464130065126617)
              ·
                refine ⟨3349521182598097548844963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4466028243464130065126617 3349521182598097548844963)
                ·
                  refine ⟨5024281773897146323267445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3349521182598097548844963 5024281773897146323267445)
                  ·
                    refine ⟨471026416302857467806323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5024281773897146323267445 471026416302857467806323)
                    ·
                      rfl

theorem cell22_1375981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1375981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1375981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1375981 prefixEnd_1375981 := by exact prefixLift 1375981
  have htrace : WordTrace (prefixWord ++ tailWord_1375981) baseStart_1375981 baseEnd_1375981 := by
    simpa [prefixWord, tailWord_1375981, baseEnd_1375981] using wordTrace_append hprefix tailTrace_1375981
  have hstable : (prefixWord ++ tailWord_1375981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1375981).length < 2 ^ (prefixWord ++ tailWord_1375981).sum := by decide
  have hdescent : baseEnd_1375981 < baseStart_1375981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1375981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376006 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1376006 : Nat := 118140960795 + 1376006 * 2 ^ 59
def prefixEnd_1376006 : Nat := 4983230072969 + 3 ^ 40 * 1376006 * 2
def baseEnd_1376006 : Nat := 157011658104588578643749

theorem tailTrace_1376006 : CollatzResearch.WordTrace tailWord_1376006 prefixEnd_1376006 157011658104588578643749 := by
  unfold tailWord_1376006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568345682905398123761121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33458041235315159973570581 1568345682905398123761121)
  ·
    refine ⟨1176259262179048592820841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1568345682905398123761121 1176259262179048592820841)
    ·
      refine ⟨882194446634286444615631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1176259262179048592820841 882194446634286444615631)
      ·
        refine ⟨1323291669951429666923447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882194446634286444615631 1323291669951429666923447)
        ·
          refine ⟨1984937504927144500385171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323291669951429666923447 1984937504927144500385171)
          ·
            refine ⟨2977406257390716750577757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984937504927144500385171 2977406257390716750577757)
            ·
              refine ⟨1116527346521518781466659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2977406257390716750577757 1116527346521518781466659)
              ·
                refine ⟨1674791019782278172199989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116527346521518781466659 1674791019782278172199989)
                ·
                  refine ⟨157011658104588578643749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1674791019782278172199989 157011658104588578643749)
                  ·
                    rfl

theorem cell22_1376006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1376006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376006 prefixEnd_1376006 := by exact prefixLift 1376006
  have htrace : WordTrace (prefixWord ++ tailWord_1376006) baseStart_1376006 baseEnd_1376006 := by
    simpa [prefixWord, tailWord_1376006, baseEnd_1376006] using wordTrace_append hprefix tailTrace_1376006
  have hstable : (prefixWord ++ tailWord_1376006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376006).length < 2 ^ (prefixWord ++ tailWord_1376006).sum := by decide
  have hdescent : baseEnd_1376006 < baseStart_1376006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376024 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1376024 : Nat := 118140960795 + 1376024 * 2 ^ 59
def prefixEnd_1376024 : Nat := 4983230072969 + 3 ^ 40 * 1376024 * 2
def baseEnd_1376024 : Nat := 471041136081619688981191

theorem tailTrace_1376024 : CollatzResearch.WordTrace tailWord_1376024 prefixEnd_1376024 471041136081619688981191 := by
  unfold tailWord_1376024
  simp only [CollatzResearch.WordTrace]
  refine ⟨25093859183453764517255563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33458478911271686023007417 25093859183453764517255563)
  ·
    refine ⟨37640788775180646775883345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25093859183453764517255563 37640788775180646775883345)
    ·
      refine ⟨28230591581385485081912509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37640788775180646775883345 28230591581385485081912509)
      ·
        refine ⟨10586471843019556905717191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28230591581385485081912509 10586471843019556905717191)
        ·
          refine ⟨15879707764529335358575787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10586471843019556905717191 15879707764529335358575787)
          ·
            refine ⟨23819561646794003037863681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15879707764529335358575787 23819561646794003037863681)
            ·
              refine ⟨17864671235095502278397761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23819561646794003037863681 17864671235095502278397761)
              ·
                refine ⟨13398503426321626708798321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17864671235095502278397761 13398503426321626708798321)
                ·
                  refine ⟨10048877569741220031598741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13398503426321626708798321 10048877569741220031598741)
                  ·
                    refine ⟨471041136081619688981191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10048877569741220031598741 471041136081619688981191)
                    ·
                      rfl

theorem cell22_1376024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1376024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376024 prefixEnd_1376024 := by exact prefixLift 1376024
  have htrace : WordTrace (prefixWord ++ tailWord_1376024) baseStart_1376024 baseEnd_1376024 := by
    simpa [prefixWord, tailWord_1376024, baseEnd_1376024] using wordTrace_append hprefix tailTrace_1376024
  have hstable : (prefixWord ++ tailWord_1376024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376024).length < 2 ^ (prefixWord ++ tailWord_1376024).sum := by decide
  have hdescent : baseEnd_1376024 < baseStart_1376024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376133 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_1376133 : Nat := 118140960795 + 1376133 * 2 ^ 59
def prefixEnd_1376133 : Nat := 4983230072969 + 3 ^ 40 * 1376133 * 2
def baseEnd_1376133 : Nat := 471078449009179738005857

theorem tailTrace_1376133 : CollatzResearch.WordTrace tailWord_1376133 prefixEnd_1376133 471078449009179738005857 := by
  unfold tailWord_1376133
  simp only [CollatzResearch.WordTrace]
  refine ⟨50191693923512640650229053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33461129282341760433486035 50191693923512640650229053)
  ·
    refine ⟨18821885221317240243835895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50191693923512640650229053 18821885221317240243835895)
    ·
      refine ⟨28232827831975860365753843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18821885221317240243835895 28232827831975860365753843)
      ·
        refine ⟨42349241747963790548630765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28232827831975860365753843 42349241747963790548630765)
        ·
          refine ⟨15880965655486421455736537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42349241747963790548630765 15880965655486421455736537)
          ·
            refine ⟨11910724241614816091802403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15880965655486421455736537 11910724241614816091802403)
            ·
              refine ⟨17866086362422224137703605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11910724241614816091802403 17866086362422224137703605)
              ·
                refine ⟨1674945596477083512909713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17866086362422224137703605 1674945596477083512909713)
                ·
                  refine ⟨1256209197357812634682285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674945596477083512909713 1256209197357812634682285)
                  ·
                    refine ⟨471078449009179738005857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256209197357812634682285 471078449009179738005857)
                    ·
                      rfl

theorem cell22_1376133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_1376133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376133 prefixEnd_1376133 := by exact prefixLift 1376133
  have htrace : WordTrace (prefixWord ++ tailWord_1376133) baseStart_1376133 baseEnd_1376133 := by
    simpa [prefixWord, tailWord_1376133, baseEnd_1376133] using wordTrace_append hprefix tailTrace_1376133
  have hstable : (prefixWord ++ tailWord_1376133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376133).length < 2 ^ (prefixWord ++ tailWord_1376133).sum := by decide
  have hdescent : baseEnd_1376133 < baseStart_1376133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376148 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1376148 : Nat := 118140960795 + 1376148 * 2 ^ 59
def prefixEnd_1376148 : Nat := 4983230072969 + 3 ^ 40 * 1376148 * 2
def baseEnd_1376148 : Nat := 471083583815724698880811

theorem tailTrace_1376148 : CollatzResearch.WordTrace tailWord_1376148 prefixEnd_1376148 471083583815724698880811 := by
  unfold tailWord_1376148
  simp only [CollatzResearch.WordTrace]
  refine ⟨25096120509229149106012549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33461494012305532141350065 25096120509229149106012549)
  ·
    refine ⟨4705522595480465457377353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25096120509229149106012549 4705522595480465457377353)
    ·
      refine ⟨3529141946610349093033015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4705522595480465457377353 3529141946610349093033015)
      ·
        refine ⟨5293712919915523639549523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529141946610349093033015 5293712919915523639549523)
        ·
          refine ⟨7940569379873285459324285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293712919915523639549523 7940569379873285459324285)
          ·
            refine ⟨2977713517452482047246607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7940569379873285459324285 2977713517452482047246607)
            ·
              refine ⟨4466570276178723070869911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977713517452482047246607 4466570276178723070869911)
              ·
                refine ⟨6699855414268084606304867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4466570276178723070869911 6699855414268084606304867)
                ·
                  refine ⟨10049783121402126909457301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6699855414268084606304867 10049783121402126909457301)
                  ·
                    refine ⟨471083583815724698880811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10049783121402126909457301 471083583815724698880811)
                    ·
                      rfl

theorem cell22_1376148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1376148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376148 prefixEnd_1376148 := by exact prefixLift 1376148
  have htrace : WordTrace (prefixWord ++ tailWord_1376148) baseStart_1376148 baseEnd_1376148 := by
    simpa [prefixWord, tailWord_1376148, baseEnd_1376148] using wordTrace_append hprefix tailTrace_1376148
  have hstable : (prefixWord ++ tailWord_1376148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376148).length < 2 ^ (prefixWord ++ tailWord_1376148).sum := by decide
  have hdescent : baseEnd_1376148 < baseStart_1376148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376152 : List Nat := [2, 1, 2, 6, 1, 1, 2, 3, 4]
def baseStart_1376152 : Nat := 118140960795 + 1376152 * 2 ^ 59
def prefixEnd_1376152 : Nat := 4983230072969 + 3 ^ 40 * 1376152 * 2
def baseEnd_1376152 : Nat := 157028317699156673926933

theorem tailTrace_1376152 : CollatzResearch.WordTrace tailWord_1376152 prefixEnd_1376152 157028317699156673926933 := by
  unfold tailWord_1376152
  simp only [CollatzResearch.WordTrace]
  refine ⟨25096193455221903447585355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33461591273629204596780473 25096193455221903447585355)
  ·
    refine ⟨37644290182832855171378033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25096193455221903447585355 37644290182832855171378033)
    ·
      refine ⟨28233217637124641378533525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37644290182832855171378033 28233217637124641378533525)
      ·
        refine ⟨1323432076740217564618759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28233217637124641378533525 1323432076740217564618759)
        ·
          refine ⟨1985148115110326346928139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323432076740217564618759 1985148115110326346928139)
          ·
            refine ⟨2977722172665489520392209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985148115110326346928139 2977722172665489520392209)
            ·
              refine ⟨2233291629499117140294157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2977722172665489520392209 2233291629499117140294157)
              ·
                refine ⟨837484361062168927610309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2233291629499117140294157 837484361062168927610309)
                ·
                  refine ⟨157028317699156673926933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837484361062168927610309 157028317699156673926933)
                  ·
                    rfl

theorem cell22_1376152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_1376152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376152 prefixEnd_1376152 := by exact prefixLift 1376152
  have htrace : WordTrace (prefixWord ++ tailWord_1376152) baseStart_1376152 baseEnd_1376152 := by
    simpa [prefixWord, tailWord_1376152, baseEnd_1376152] using wordTrace_append hprefix tailTrace_1376152
  have hstable : (prefixWord ++ tailWord_1376152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376152).length < 2 ^ (prefixWord ++ tailWord_1376152).sum := by decide
  have hdescent : baseEnd_1376152 < baseStart_1376152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376167 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1376167 : Nat := 118140960795 + 1376167 * 2 ^ 59
def prefixEnd_1376167 : Nat := 4983230072969 + 3 ^ 40 * 1376167 * 2
def baseEnd_1376167 : Nat := 471090087904014982655753

theorem tailTrace_1376167 : CollatzResearch.WordTrace tailWord_1376167 prefixEnd_1376167 471090087904014982655753 := by
  unfold tailWord_1376167
  simp only [CollatzResearch.WordTrace]
  refine ⟨50192934005389464456966755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33461956003592976304644503 50192934005389464456966755)
  ·
    refine ⟨75289401008084196685450133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50192934005389464456966755 75289401008084196685450133)
    ·
      refine ⟨3529190672253946719630475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75289401008084196685450133 3529190672253946719630475)
      ·
        refine ⟨5293786008380920079445713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529190672253946719630475 5293786008380920079445713)
        ·
          refine ⟨3970339506285690059584285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5293786008380920079445713 3970339506285690059584285)
          ·
            refine ⟨1488877314857133772344107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3970339506285690059584285 1488877314857133772344107)
            ·
              refine ⟨2233315972285700658516161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488877314857133772344107 2233315972285700658516161)
              ·
                refine ⟨1674986979214275493887121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233315972285700658516161 1674986979214275493887121)
                ·
                  refine ⟨1256240234410706620415341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674986979214275493887121 1256240234410706620415341)
                  ·
                    refine ⟨471090087904014982655753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256240234410706620415341 471090087904014982655753)
                    ·
                      rfl

theorem cell22_1376167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1376167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376167 prefixEnd_1376167 := by exact prefixLift 1376167
  have htrace : WordTrace (prefixWord ++ tailWord_1376167) baseStart_1376167 baseEnd_1376167 := by
    simpa [prefixWord, tailWord_1376167, baseEnd_1376167] using wordTrace_append hprefix tailTrace_1376167
  have hstable : (prefixWord ++ tailWord_1376167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376167).length < 2 ^ (prefixWord ++ tailWord_1376167).sum := by decide
  have hdescent : baseEnd_1376167 < baseStart_1376167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376268 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1376268 : Nat := 118140960795 + 1376268 * 2 ^ 59
def prefixEnd_1376268 : Nat := 4983230072969 + 3 ^ 40 * 1376268 * 2
def baseEnd_1376268 : Nat := 471124662268084385880443

theorem tailTrace_1376268 : CollatzResearch.WordTrace tailWord_1376268 prefixEnd_1376268 471124662268084385880443 := by
  unfold tailWord_1376268
  simp only [CollatzResearch.WordTrace]
  refine ⟨25098308889011779353196729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33464411852015705804262305 25098308889011779353196729)
  ·
    refine ⟨18823731666758834514897547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25098308889011779353196729 18823731666758834514897547)
    ·
      refine ⟨28235597500138251772346321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18823731666758834514897547 28235597500138251772346321)
      ·
        refine ⟨21176698125103688829259741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28235597500138251772346321 21176698125103688829259741)
        ·
          refine ⟨7941261796913883310972403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21176698125103688829259741 7941261796913883310972403)
          ·
            refine ⟨11911892695370824966458605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7941261796913883310972403 11911892695370824966458605)
            ·
              refine ⟨4466959760764059362421977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11911892695370824966458605 4466959760764059362421977)
              ·
                refine ⟨3350219820573044521816483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4466959760764059362421977 3350219820573044521816483)
                ·
                  refine ⟨5025329730859566782724725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3350219820573044521816483 5025329730859566782724725)
                  ·
                    refine ⟨471124662268084385880443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5025329730859566782724725 471124662268084385880443)
                    ·
                      rfl

theorem cell22_1376268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1376268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376268 prefixEnd_1376268 := by exact prefixLift 1376268
  have htrace : WordTrace (prefixWord ++ tailWord_1376268) baseStart_1376268 baseEnd_1376268 := by
    simpa [prefixWord, tailWord_1376268, baseEnd_1376268] using wordTrace_append hprefix tailTrace_1376268
  have hstable : (prefixWord ++ tailWord_1376268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376268).length < 2 ^ (prefixWord ++ tailWord_1376268).sum := by decide
  have hdescent : baseEnd_1376268 < baseStart_1376268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376270 : List Nat := [4, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_1376270 : Nat := 118140960795 + 1376270 * 2 ^ 59
def prefixEnd_1376270 : Nat := 4983230072969 + 3 ^ 40 * 1376270 * 2
def baseEnd_1376270 : Nat := 157041782302985682443479

theorem tailTrace_1376270 : CollatzResearch.WordTrace tailWord_1376270 prefixEnd_1376270 157041782302985682443479 := by
  unfold tailWord_1376270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274586340502039130995783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33464460482677542031977509 6274586340502039130995783)
  ·
    refine ⟨9411879510753058696493675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6274586340502039130995783 9411879510753058696493675)
    ·
      refine ⟨14117819266129588044740513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9411879510753058696493675 14117819266129588044740513)
      ·
        refine ⟨10588364449597191033555385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14117819266129588044740513 10588364449597191033555385)
        ·
          refine ⟨7941273337197893275166539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10588364449597191033555385 7941273337197893275166539)
          ·
            refine ⟨11911910005796839912749809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7941273337197893275166539 11911910005796839912749809)
            ·
              refine ⟨8933932504347629934562357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11911910005796839912749809 8933932504347629934562357)
              ·
                refine ⟨837556172282590306365221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8933932504347629934562357 837556172282590306365221)
                ·
                  refine ⟨157041782302985682443479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837556172282590306365221 157041782302985682443479)
                  ·
                    rfl

theorem cell22_1376270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_1376270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376270 prefixEnd_1376270 := by exact prefixLift 1376270
  have htrace : WordTrace (prefixWord ++ tailWord_1376270) baseStart_1376270 baseEnd_1376270 := by
    simpa [prefixWord, tailWord_1376270, baseEnd_1376270] using wordTrace_append hprefix tailTrace_1376270
  have hstable : (prefixWord ++ tailWord_1376270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376270).length < 2 ^ (prefixWord ++ tailWord_1376270).sum := by decide
  have hdescent : baseEnd_1376270 < baseStart_1376270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376302 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1376302 : Nat := 118140960795 + 1376302 * 2 ^ 59
def prefixEnd_1376302 : Nat := 4983230072969 + 3 ^ 40 * 1376302 * 2
def baseEnd_1376302 : Nat := 471136301162919630530339

theorem tailTrace_1376302 : CollatzResearch.WordTrace tailWord_1376302 prefixEnd_1376302 471136301162919630530339 := by
  unfold tailWord_1376302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274732232487547814141395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33465238573266921675420773 6274732232487547814141395)
  ·
    refine ⟨9412098348731321721212093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6274732232487547814141395 9412098348731321721212093)
    ·
      refine ⟨3529536880774245645454535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9412098348731321721212093 3529536880774245645454535)
      ·
        refine ⟨5294305321161368468181803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529536880774245645454535 5294305321161368468181803)
        ·
          refine ⟨7941457981742052702272705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5294305321161368468181803 7941457981742052702272705)
          ·
            refine ⟨5956093486306539526704529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7941457981742052702272705 5956093486306539526704529)
            ·
              refine ⟨4467070114729904645028397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5956093486306539526704529 4467070114729904645028397)
              ·
                refine ⟨1675151293023714241885649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4467070114729904645028397 1675151293023714241885649)
                ·
                  refine ⟨1256363469767785681414237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1675151293023714241885649 1256363469767785681414237)
                  ·
                    refine ⟨471136301162919630530339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256363469767785681414237 471136301162919630530339)
                    ·
                      rfl

theorem cell22_1376302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1376302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376302 prefixEnd_1376302 := by exact prefixLift 1376302
  have htrace : WordTrace (prefixWord ++ tailWord_1376302) baseStart_1376302 baseEnd_1376302 := by
    simpa [prefixWord, tailWord_1376302, baseEnd_1376302] using wordTrace_append hprefix tailTrace_1376302
  have hstable : (prefixWord ++ tailWord_1376302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376302).length < 2 ^ (prefixWord ++ tailWord_1376302).sum := by decide
  have hdescent : baseEnd_1376302 < baseStart_1376302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1376452 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1376452 : Nat := 118140960795 + 1376452 * 2 ^ 59
def prefixEnd_1376452 : Nat := 4983230072969 + 3 ^ 40 * 1376452 * 2
def baseEnd_1376452 : Nat := 471187649228369239279879

theorem tailTrace_1376452 : CollatzResearch.WordTrace tailWord_1376452 prefixEnd_1376452 471187649228369239279879 := by
  unfold tailWord_1376452
  simp only [CollatzResearch.WordTrace]
  refine ⟨25101664404678479065545805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33468885872904638754061073 25101664404678479065545805)
  ·
    refine ⟨9413124151754429649579677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25101664404678479065545805 9413124151754429649579677)
    ·
      refine ⟨3529921556907911118592379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9413124151754429649579677 3529921556907911118592379)
      ·
        refine ⟨5294882335361866677888569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529921556907911118592379 5294882335361866677888569)
        ·
          refine ⟨3971161751521400008416427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5294882335361866677888569 3971161751521400008416427)
          ·
            refine ⟨5956742627282100012624641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971161751521400008416427 5956742627282100012624641)
            ·
              refine ⟨4467556970461575009468481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5956742627282100012624641 4467556970461575009468481)
              ·
                refine ⟨3350667727846181257101361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4467556970461575009468481 3350667727846181257101361)
                ·
                  refine ⟨2513000795884635942826021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3350667727846181257101361 2513000795884635942826021)
                  ·
                    refine ⟨471187649228369239279879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2513000795884635942826021 471187649228369239279879)
                    ·
                      rfl

theorem cell22_1376452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1376452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1376452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1376452 prefixEnd_1376452 := by exact prefixLift 1376452
  have htrace : WordTrace (prefixWord ++ tailWord_1376452) baseStart_1376452 baseEnd_1376452 := by
    simpa [prefixWord, tailWord_1376452, baseEnd_1376452] using wordTrace_append hprefix tailTrace_1376452
  have hstable : (prefixWord ++ tailWord_1376452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1376452).length < 2 ^ (prefixWord ++ tailWord_1376452).sum := by decide
  have hdescent : baseEnd_1376452 < baseStart_1376452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1376452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
