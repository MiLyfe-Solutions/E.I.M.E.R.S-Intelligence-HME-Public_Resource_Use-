import V185TrunkScan23Chunk1165

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6907565 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_6907565 : Nat := 118140960795 + 6907565 * 2 ^ 59
def prefixEnd_6907565 : Nat := 4983230072969 + 3 ^ 40 * 6907565 * 2
def baseEnd_6907565 : Nat := 3546900997174371853870193

theorem tailTrace_6907565 : CollatzResearch.WordTrace tailWord_6907565 prefixEnd_6907565 3546900997174371853870193 := by
  unfold tailWord_6907565
  simp only [CollatzResearch.WordTrace]
  refine ⟨251939593220079198024948149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167959728813386132016632099 251939593220079198024948149)
  ·
    refine ⟨23619336864382424814838889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251939593220079198024948149 23619336864382424814838889)
    ·
      refine ⟨17714502648286818611129167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23619336864382424814838889 17714502648286818611129167)
      ·
        refine ⟨26571753972430227916693751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17714502648286818611129167 26571753972430227916693751)
        ·
          refine ⟨39857630958645341875040627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26571753972430227916693751 39857630958645341875040627)
          ·
            refine ⟨59786446437968012812560941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39857630958645341875040627 59786446437968012812560941)
            ·
              refine ⟨22419917414238004804710353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59786446437968012812560941 22419917414238004804710353)
              ·
                refine ⟨16814938060678503603532765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22419917414238004804710353 16814938060678503603532765)
                ·
                  refine ⟨6305601772754438851324787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16814938060678503603532765 6305601772754438851324787)
                  ·
                    refine ⟨9458402659131658276987181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305601772754438851324787 9458402659131658276987181)
                    ·
                      refine ⟨3546900997174371853870193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458402659131658276987181 3546900997174371853870193)
                      ·
                        rfl

theorem cell23_6907565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_6907565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907565 prefixEnd_6907565 := by exact prefixLift 6907565
  have htrace : WordTrace (prefixWord ++ tailWord_6907565) baseStart_6907565 baseEnd_6907565 := by
    simpa [prefixWord, tailWord_6907565, baseEnd_6907565] using wordTrace_append hprefix tailTrace_6907565
  have hstable : (prefixWord ++ tailWord_6907565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907565).length < 2 ^ (prefixWord ++ tailWord_6907565).sum := by decide
  have hdescent : baseEnd_6907565 < baseStart_6907565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907571 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 4]
def baseStart_6907571 : Nat := 118140960795 + 6907571 * 2 ^ 59
def prefixEnd_6907571 : Nat := 4983230072969 + 3 ^ 40 * 6907571 * 2
def baseEnd_6907571 : Nat := 3546904078058298830395165

theorem tailTrace_6907571 : CollatzResearch.WordTrace tailWord_6907571 prefixEnd_6907571 3546904078058298830395165 := by
  unfold tailWord_6907571
  simp only [CollatzResearch.WordTrace]
  refine ⟨251939812058057461049666567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167959874705371640699777711 251939812058057461049666567)
  ·
    refine ⟨377909718087086191574499851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251939812058057461049666567 377909718087086191574499851)
    ·
      refine ⟨566864577130629287361749777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377909718087086191574499851 566864577130629287361749777)
      ·
        refine ⟨425148432847971965521312333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566864577130629287361749777 425148432847971965521312333)
        ·
          refine ⟨159430662317989487070492125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425148432847971965521312333 159430662317989487070492125)
          ·
            refine ⟨59786498369246057651434547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159430662317989487070492125 59786498369246057651434547)
            ·
              refine ⟨89679747553869086477151821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59786498369246057651434547 89679747553869086477151821)
              ·
                refine ⟨33629905332700907428931933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89679747553869086477151821 33629905332700907428931933)
                ·
                  refine ⟨12611214499762840285849475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33629905332700907428931933 12611214499762840285849475)
                  ·
                    refine ⟨18916821749644260428774213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12611214499762840285849475 18916821749644260428774213)
                    ·
                      refine ⟨3546904078058298830395165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18916821749644260428774213 3546904078058298830395165)
                      ·
                        rfl

theorem cell23_6907571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_6907571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907571 prefixEnd_6907571 := by exact prefixLift 6907571
  have htrace : WordTrace (prefixWord ++ tailWord_6907571) baseStart_6907571 baseEnd_6907571 := by
    simpa [prefixWord, tailWord_6907571, baseEnd_6907571] using wordTrace_append hprefix tailTrace_6907571
  have hstable : (prefixWord ++ tailWord_6907571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907571).length < 2 ^ (prefixWord ++ tailWord_6907571).sum := by decide
  have hdescent : baseEnd_6907571 < baseStart_6907571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907575 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 2, 3, 2]
def baseStart_6907575 : Nat := 118140960795 + 6907575 * 2 ^ 59
def prefixEnd_6907575 : Nat := 4983230072969 + 3 ^ 40 * 6907575 * 2
def baseEnd_6907575 : Nat := 3546906131980916814745147

theorem tailTrace_6907575 : CollatzResearch.WordTrace tailWord_6907575 prefixEnd_6907575 3546906131980916814745147 := by
  unfold tailWord_6907575
  simp only [CollatzResearch.WordTrace]
  refine ⟨251939957950042969732812179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167959971966695313155208119 251939957950042969732812179)
  ·
    refine ⟨377909936925064454599218269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251939957950042969732812179 377909936925064454599218269)
    ·
      refine ⟨141716226346899170474706851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377909936925064454599218269 141716226346899170474706851)
      ·
        refine ⟨212574339520348755712060277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141716226346899170474706851 212574339520348755712060277)
        ·
          refine ⟨19928844330032695848005651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212574339520348755712060277 19928844330032695848005651)
          ·
            refine ⟨29893266495049043772008477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19928844330032695848005651 29893266495049043772008477)
            ·
              refine ⟨11209974935643391414503179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29893266495049043772008477 11209974935643391414503179)
              ·
                refine ⟨16814962403465087121754769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11209974935643391414503179 16814962403465087121754769)
                ·
                  refine ⟨12611221802598815341316077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16814962403465087121754769 12611221802598815341316077)
                  ·
                    refine ⟨4729208175974555752993529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12611221802598815341316077 4729208175974555752993529)
                    ·
                      refine ⟨3546906131980916814745147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729208175974555752993529 3546906131980916814745147)
                      ·
                        rfl

theorem cell23_6907575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_6907575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907575 prefixEnd_6907575 := by exact prefixLift 6907575
  have htrace : WordTrace (prefixWord ++ tailWord_6907575) baseStart_6907575 baseEnd_6907575 := by
    simpa [prefixWord, tailWord_6907575, baseEnd_6907575] using wordTrace_append hprefix tailTrace_6907575
  have hstable : (prefixWord ++ tailWord_6907575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907575).length < 2 ^ (prefixWord ++ tailWord_6907575).sum := by decide
  have hdescent : baseEnd_6907575 < baseStart_6907575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907581 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_6907581 : Nat := 118140960795 + 6907581 * 2 ^ 59
def prefixEnd_6907581 : Nat := 4983230072969 + 3 ^ 40 * 6907581 * 2
def baseEnd_6907581 : Nat := 1182303070954947930423373

theorem tailTrace_6907581 : CollatzResearch.WordTrace tailWord_6907581 prefixEnd_6907581 1182303070954947930423373 := by
  unfold tailWord_6907581
  simp only [CollatzResearch.WordTrace]
  refine ⟨251940176788021232757530597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167960117858680821838353731 251940176788021232757530597)
  ·
    refine ⟨47238783147753981142036987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251940176788021232757530597 47238783147753981142036987)
    ·
      refine ⟨70858174721630971713055481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47238783147753981142036987 70858174721630971713055481)
      ·
        refine ⟨53143631041223228784791611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70858174721630971713055481 53143631041223228784791611)
        ·
          refine ⟨79715446561834843177187417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53143631041223228784791611 79715446561834843177187417)
          ·
            refine ⟨59786584921376132382890563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79715446561834843177187417 59786584921376132382890563)
            ·
              refine ⟨89679877382064198574335845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59786584921376132382890563 89679877382064198574335845)
              ·
                refine ⟨16814977009137037232687971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89679877382064198574335845 16814977009137037232687971)
                ·
                  refine ⟨25222465513705555849031957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16814977009137037232687971 25222465513705555849031957)
                  ·
                    refine ⟨1182303070954947930423373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25222465513705555849031957 1182303070954947930423373)
                    ·
                      rfl

theorem cell23_6907581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_6907581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907581 prefixEnd_6907581 := by exact prefixLift 6907581
  have htrace : WordTrace (prefixWord ++ tailWord_6907581) baseStart_6907581 baseEnd_6907581 := by
    simpa [prefixWord, tailWord_6907581, baseEnd_6907581] using wordTrace_append hprefix tailTrace_6907581
  have hstable : (prefixWord ++ tailWord_6907581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907581).length < 2 ^ (prefixWord ++ tailWord_6907581).sum := by decide
  have hdescent : baseEnd_6907581 < baseStart_6907581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907582 : List Nat := [4, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_6907582 : Nat := 118140960795 + 6907582 * 2 ^ 59
def prefixEnd_6907582 : Nat := 4983230072969 + 3 ^ 40 * 6907582 * 2
def baseEnd_6907582 : Nat := 3546909726345498287357615

theorem tailTrace_6907582 : CollatzResearch.WordTrace tailWord_6907582 prefixEnd_6907582 3546909726345498287357615 := by
  unfold tailWord_6907582
  simp only [CollatzResearch.WordTrace]
  refine ⟨31492526657627201241039625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167960142174011739952211333 31492526657627201241039625)
  ·
    refine ⟨23619394993220400930779719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31492526657627201241039625 23619394993220400930779719)
    ·
      refine ⟨35429092489830601396169579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23619394993220400930779719 35429092489830601396169579)
      ·
        refine ⟨53143638734745902094254369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35429092489830601396169579 53143638734745902094254369)
        ·
          refine ⟨39857729051059426570690777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53143638734745902094254369 39857729051059426570690777)
          ·
            refine ⟨29893296788294569928018083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39857729051059426570690777 29893296788294569928018083)
            ·
              refine ⟨44839945182441854892027125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29893296788294569928018083 44839945182441854892027125)
              ·
                refine ⟨4203744860853923896127543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44839945182441854892027125 4203744860853923896127543)
                ·
                  refine ⟨6305617291280885844191315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203744860853923896127543 6305617291280885844191315)
                  ·
                    refine ⟨9458425936921328766286973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305617291280885844191315 9458425936921328766286973)
                    ·
                      refine ⟨3546909726345498287357615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458425936921328766286973 3546909726345498287357615)
                      ·
                        rfl

theorem cell23_6907582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_6907582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907582 prefixEnd_6907582 := by exact prefixLift 6907582
  have htrace : WordTrace (prefixWord ++ tailWord_6907582) baseStart_6907582 baseEnd_6907582 := by
    simpa [prefixWord, tailWord_6907582, baseEnd_6907582] using wordTrace_append hprefix tailTrace_6907582
  have hstable : (prefixWord ++ tailWord_6907582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907582).length < 2 ^ (prefixWord ++ tailWord_6907582).sum := by decide
  have hdescent : baseEnd_6907582 < baseStart_6907582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907591 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_6907591 : Nat := 118140960795 + 6907591 * 2 ^ 59
def prefixEnd_6907591 : Nat := 4983230072969 + 3 ^ 40 * 6907591 * 2
def baseEnd_6907591 : Nat := 3546914347671388752145073

theorem tailTrace_6907591 : CollatzResearch.WordTrace tailWord_6907591 prefixEnd_6907591 3546914347671388752145073 := by
  unfold tailWord_6907591
  simp only [CollatzResearch.WordTrace]
  refine ⟨251940541517985004465394627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167960361011990002976929751 251940541517985004465394627)
  ·
    refine ⟨377910812276977506698091941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251940541517985004465394627 377910812276977506698091941)
    ·
      refine ⟨70858277301933282505892239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377910812276977506698091941 70858277301933282505892239)
      ·
        refine ⟨106287415952899923758838359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70858277301933282505892239 106287415952899923758838359)
        ·
          refine ⟨159431123929349885638257539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106287415952899923758838359 159431123929349885638257539)
          ·
            refine ⟨239146685894024828457386309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159431123929349885638257539 239146685894024828457386309)
            ·
              refine ⟨44840003605129655335759933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239146685894024828457386309 44840003605129655335759933)
              ·
                refine ⟨16815001351923620750909975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44840003605129655335759933 16815001351923620750909975)
                ·
                  refine ⟨25222502027885431126364963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16815001351923620750909975 25222502027885431126364963)
                  ·
                    refine ⟨37833753041828146689547445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25222502027885431126364963 37833753041828146689547445)
                    ·
                      refine ⟨3546914347671388752145073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37833753041828146689547445 3546914347671388752145073)
                      ·
                        rfl

theorem cell23_6907591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_6907591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907591 prefixEnd_6907591 := by exact prefixLift 6907591
  have htrace : WordTrace (prefixWord ++ tailWord_6907591) baseStart_6907591 baseEnd_6907591 := by
    simpa [prefixWord, tailWord_6907591, baseEnd_6907591] using wordTrace_append hprefix tailTrace_6907591
  have hstable : (prefixWord ++ tailWord_6907591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907591).length < 2 ^ (prefixWord ++ tailWord_6907591).sum := by decide
  have hdescent : baseEnd_6907591 < baseStart_6907591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907598 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_6907598 : Nat := 118140960795 + 6907598 * 2 ^ 59
def prefixEnd_6907598 : Nat := 4983230072969 + 3 ^ 40 * 6907598 * 2
def baseEnd_6907598 : Nat := 1182305980678656741585847

theorem tailTrace_6907598 : CollatzResearch.WordTrace tailWord_6907598 prefixEnd_6907598 1182305980678656741585847 := by
  unfold tailWord_6907598
  simp only [CollatzResearch.WordTrace]
  refine ⟨31492599603619955582612431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167960531219306429773932965 31492599603619955582612431)
  ·
    refine ⟨47238899405429933373918647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31492599603619955582612431 47238899405429933373918647)
    ·
      refine ⟨70858349108144900060877971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47238899405429933373918647 70858349108144900060877971)
      ·
        refine ⟨106287523662217350091316957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70858349108144900060877971 106287523662217350091316957)
        ·
          refine ⟨39857821373331506284243859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106287523662217350091316957 39857821373331506284243859)
          ·
            refine ⟨59786732059997259426365789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39857821373331506284243859 59786732059997259426365789)
            ·
              refine ⟨22420024522498972284887171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59786732059997259426365789 22420024522498972284887171)
              ·
                refine ⟨33630036783748458427330757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22420024522498972284887171 33630036783748458427330757)
                ·
                  refine ⟨6305631896952835955124517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33630036783748458427330757 6305631896952835955124517)
                  ·
                    refine ⟨1182305980678656741585847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6305631896952835955124517 1182305980678656741585847)
                    ·
                      rfl

theorem cell23_6907598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_6907598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907598 prefixEnd_6907598 := by exact prefixLift 6907598
  have htrace : WordTrace (prefixWord ++ tailWord_6907598) baseStart_6907598 baseEnd_6907598 := by
    simpa [prefixWord, tailWord_6907598, baseEnd_6907598] using wordTrace_append hprefix tailTrace_6907598
  have hstable : (prefixWord ++ tailWord_6907598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907598).length < 2 ^ (prefixWord ++ tailWord_6907598).sum := by decide
  have hdescent : baseEnd_6907598 < baseStart_6907598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907615 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 2, 4]
def baseStart_6907615 : Nat := 118140960795 + 6907615 * 2 ^ 59
def prefixEnd_6907615 : Nat := 4983230072969 + 3 ^ 40 * 6907615 * 2
def baseEnd_6907615 : Nat := 1182308890402365552748321

theorem tailTrace_6907615 : CollatzResearch.WordTrace tailWord_6907615 prefixEnd_6907615 1182308890402365552748321 := by
  unfold tailWord_6907615
  simp only [CollatzResearch.WordTrace]
  refine ⟨251941416869898056564268299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167960944579932037709512199 251941416869898056564268299)
  ·
    refine ⟨377912125304847084846402449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251941416869898056564268299 377912125304847084846402449)
    ·
      refine ⟨283434093978635313634801837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377912125304847084846402449 283434093978635313634801837)
      ·
        refine ⟨106287785241988242613050689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283434093978635313634801837 106287785241988242613050689)
        ·
          refine ⟨79715838931491181959788017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106287785241988242613050689 79715838931491181959788017)
          ·
            refine ⟨59786879198618386469841013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79715838931491181959788017 59786879198618386469841013)
            ·
              refine ⟨5605019924870473731547595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59786879198618386469841013 5605019924870473731547595)
              ·
                refine ⟨8407529887305710597321393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605019924870473731547595 8407529887305710597321393)
                ·
                  refine ⟨6305647415479282947991045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8407529887305710597321393 6305647415479282947991045)
                  ·
                    refine ⟨1182308890402365552748321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6305647415479282947991045 1182308890402365552748321)
                    ·
                      rfl

theorem cell23_6907615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 4].length) (baseStart_6907615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907615 prefixEnd_6907615 := by exact prefixLift 6907615
  have htrace : WordTrace (prefixWord ++ tailWord_6907615) baseStart_6907615 baseEnd_6907615 := by
    simpa [prefixWord, tailWord_6907615, baseEnd_6907615] using wordTrace_append hprefix tailTrace_6907615
  have hstable : (prefixWord ++ tailWord_6907615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907615).length < 2 ^ (prefixWord ++ tailWord_6907615).sum := by decide
  have hdescent : baseEnd_6907615 < baseStart_6907615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907672 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 2, 1, 3]
def baseStart_6907672 : Nat := 118140960795 + 6907672 * 2 ^ 59
def prefixEnd_6907672 : Nat := 4983230072969 + 3 ^ 40 * 6907672 * 2
def baseEnd_6907672 : Nat := 3546955939604402935232201

theorem tailTrace_6907672 : CollatzResearch.WordTrace tailWord_6907672 prefixEnd_6907672 3546955939604402935232201 := by
  unfold tailWord_6907672
  simp only [CollatzResearch.WordTrace]
  refine ⟨125971747915345777649546635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167962330553794370199395513 125971747915345777649546635)
  ·
    refine ⟨188957621873018666474319953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125971747915345777649546635 188957621873018666474319953)
    ·
      refine ⟨141718216404763999855739965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188957621873018666474319953 141718216404763999855739965)
      ·
        refine ⟨53144331151786499945902487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141718216404763999855739965 53144331151786499945902487)
        ·
          refine ⟨79716496727679749918853731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53144331151786499945902487 79716496727679749918853731)
          ·
            refine ⟨119574745091519624878280597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79716496727679749918853731 119574745091519624878280597)
            ·
              refine ⟨5605066176164982416169403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119574745091519624878280597 5605066176164982416169403)
              ·
                refine ⟨8407599264247473624254105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605066176164982416169403 8407599264247473624254105)
                ·
                  refine ⟨6305699448185605218190579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8407599264247473624254105 6305699448185605218190579)
                  ·
                    refine ⟨9458549172278407827285869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305699448185605218190579 9458549172278407827285869)
                    ·
                      refine ⟨3546955939604402935232201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458549172278407827285869 3546955939604402935232201)
                      ·
                        rfl

theorem cell23_6907672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_6907672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907672 prefixEnd_6907672 := by exact prefixLift 6907672
  have htrace : WordTrace (prefixWord ++ tailWord_6907672) baseStart_6907672 baseEnd_6907672 := by
    simpa [prefixWord, tailWord_6907672, baseEnd_6907672] using wordTrace_append hprefix tailTrace_6907672
  have hstable : (prefixWord ++ tailWord_6907672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907672).length < 2 ^ (prefixWord ++ tailWord_6907672).sum := by decide
  have hdescent : baseEnd_6907672 < baseStart_6907672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907698 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_6907698 : Nat := 118140960795 + 6907698 * 2 ^ 59
def prefixEnd_6907698 : Nat := 4983230072969 + 3 ^ 40 * 6907698 * 2
def baseEnd_6907698 : Nat := 3546969290101419833507081

theorem tailTrace_6907698 : CollatzResearch.WordTrace tailWord_6907698 prefixEnd_6907698 3546969290101419833507081 := by
  unfold tailWord_6907698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62986111032149340434884937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167962962752398241159693165 62986111032149340434884937)
  ·
    refine ⟨47239583274112005326163703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62986111032149340434884937 47239583274112005326163703)
    ·
      refine ⟨70859374911168007989245555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47239583274112005326163703 70859374911168007989245555)
      ·
        refine ⟨106289062366752011983868333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70859374911168007989245555 106289062366752011983868333)
        ·
          refine ⟨39858398387532004493950625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106289062366752011983868333 39858398387532004493950625)
          ·
            refine ⟨29893798790649003370462969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39858398387532004493950625 29893798790649003370462969)
            ·
              refine ⟨22420349092986752527847227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29893798790649003370462969 22420349092986752527847227)
              ·
                refine ⟨33630523639480128791770841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22420349092986752527847227 33630523639480128791770841)
                ·
                  refine ⟨25222892729610096593828131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33630523639480128791770841 25222892729610096593828131)
                  ·
                    refine ⟨37834339094415144890742197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25222892729610096593828131 37834339094415144890742197)
                    ·
                      refine ⟨3546969290101419833507081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37834339094415144890742197 3546969290101419833507081)
                      ·
                        rfl

theorem cell23_6907698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_6907698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907698 prefixEnd_6907698 := by exact prefixLift 6907698
  have htrace : WordTrace (prefixWord ++ tailWord_6907698) baseStart_6907698 baseEnd_6907698 := by
    simpa [prefixWord, tailWord_6907698, baseEnd_6907698] using wordTrace_append hprefix tailTrace_6907698
  have hstable : (prefixWord ++ tailWord_6907698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907698).length < 2 ^ (prefixWord ++ tailWord_6907698).sum := by decide
  have hdescent : baseEnd_6907698 < baseStart_6907698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907699 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 1, 3, 2]
def baseStart_6907699 : Nat := 118140960795 + 6907699 * 2 ^ 59
def prefixEnd_6907699 : Nat := 4983230072969 + 3 ^ 40 * 6907699 * 2
def baseEnd_6907699 : Nat := 3546969803582074329594577

theorem tailTrace_6907699 : CollatzResearch.WordTrace tailWord_6907699 prefixEnd_6907699 3546969803582074329594577 := by
  unfold tailWord_6907699
  simp only [CollatzResearch.WordTrace]
  refine ⟨251944480601593738910326151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167962987067729159273550767 251944480601593738910326151)
  ·
    refine ⟨377916720902390608365489227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251944480601593738910326151 377916720902390608365489227)
    ·
      refine ⟨566875081353585912548233841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377916720902390608365489227 566875081353585912548233841)
      ·
        refine ⟨425156311015189434411175381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566875081353585912548233841 425156311015189434411175381)
        ·
          refine ⟨9964601039418502369011923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 425156311015189434411175381 9964601039418502369011923)
          ·
            refine ⟨14946901559127753553517885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964601039418502369011923 14946901559127753553517885)
            ·
              refine ⟨5605088084672907582569207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14946901559127753553517885 5605088084672907582569207)
              ·
                refine ⟨8407632127009361373853811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605088084672907582569207 8407632127009361373853811)
                ·
                  refine ⟨12611448190514042060780717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8407632127009361373853811 12611448190514042060780717)
                  ·
                    refine ⟨4729293071442765772792769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12611448190514042060780717 4729293071442765772792769)
                    ·
                      refine ⟨3546969803582074329594577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729293071442765772792769 3546969803582074329594577)
                      ·
                        rfl

theorem cell23_6907699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 3, 2].length) (baseStart_6907699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907699 prefixEnd_6907699 := by exact prefixLift 6907699
  have htrace : WordTrace (prefixWord ++ tailWord_6907699) baseStart_6907699 baseEnd_6907699 := by
    simpa [prefixWord, tailWord_6907699, baseEnd_6907699] using wordTrace_append hprefix tailTrace_6907699
  have hstable : (prefixWord ++ tailWord_6907699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907699).length < 2 ^ (prefixWord ++ tailWord_6907699).sum := by decide
  have hdescent : baseEnd_6907699 < baseStart_6907699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907725 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6907725 : Nat := 118140960795 + 6907725 * 2 ^ 59
def prefixEnd_6907725 : Nat := 4983230072969 + 3 ^ 40 * 6907725 * 2
def baseEnd_6907725 : Nat := 3546983154079091227869457

theorem tailTrace_6907725 : CollatzResearch.WordTrace tailWord_6907725 prefixEnd_6907725 3546983154079091227869457 := by
  unfold tailWord_6907725
  simp only [CollatzResearch.WordTrace]
  refine ⟨251945428899499545350772629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167963619266333030233848419 251945428899499545350772629)
  ·
    refine ⟨11809941979664041188317467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 251945428899499545350772629 11809941979664041188317467)
    ·
      refine ⟨17714912969496061782476201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11809941979664041188317467 17714912969496061782476201)
      ·
        refine ⟨13286184727122046336857151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17714912969496061782476201 13286184727122046336857151)
        ·
          refine ⟨19929277090683069505285727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13286184727122046336857151 19929277090683069505285727)
          ·
            refine ⟨29893915636024604257928591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19929277090683069505285727 29893915636024604257928591)
            ·
              refine ⟨44840873454036906386892887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29893915636024604257928591 44840873454036906386892887)
              ·
                refine ⟨67261310181055359580339331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44840873454036906386892887 67261310181055359580339331)
                ·
                  refine ⟨100891965271583039370508997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67261310181055359580339331 100891965271583039370508997)
                  ·
                    refine ⟨18917243488421819881970437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100891965271583039370508997 18917243488421819881970437)
                    ·
                      refine ⟨3546983154079091227869457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18917243488421819881970437 3546983154079091227869457)
                      ·
                        rfl

theorem cell23_6907725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6907725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907725 prefixEnd_6907725 := by exact prefixLift 6907725
  have htrace : WordTrace (prefixWord ++ tailWord_6907725) baseStart_6907725 baseEnd_6907725 := by
    simpa [prefixWord, tailWord_6907725, baseEnd_6907725] using wordTrace_append hprefix tailTrace_6907725
  have hstable : (prefixWord ++ tailWord_6907725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907725).length < 2 ^ (prefixWord ++ tailWord_6907725).sum := by decide
  have hdescent : baseEnd_6907725 < baseStart_6907725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907785 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 2, 4, 2]
def baseStart_6907785 : Nat := 118140960795 + 6907785 * 2 ^ 59
def prefixEnd_6907785 : Nat := 4983230072969 + 3 ^ 40 * 6907785 * 2
def baseEnd_6907785 : Nat := 3547013962918360993119181

theorem tailTrace_6907785 : CollatzResearch.WordTrace tailWord_6907785 prefixEnd_6907785 3547013962918360993119181 := by
  unfold tailWord_6907785
  simp only [CollatzResearch.WordTrace]
  refine ⟨251947617279282175597956809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167965078186188117065304539 251947617279282175597956809)
  ·
    refine ⟨188960712959461631698467607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251947617279282175597956809 188960712959461631698467607)
    ·
      refine ⟨283441069439192447547701411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188960712959461631698467607 283441069439192447547701411)
      ·
        refine ⟨425161604158788671321552117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283441069439192447547701411 425161604158788671321552117)
        ·
          refine ⟨39858900389886437936395511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 425161604158788671321552117 39858900389886437936395511)
          ·
            refine ⟨59788350584829656904593267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39858900389886437936395511 59788350584829656904593267)
            ·
              refine ⟨89682525877244485356889901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59788350584829656904593267 89682525877244485356889901)
              ·
                refine ⟨33630947203966682008833713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89682525877244485356889901 33630947203966682008833713)
                ·
                  refine ⟨25223210402975011506625285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33630947203966682008833713 25223210402975011506625285)
                  ·
                    refine ⟨4729351950557814657492241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25223210402975011506625285 4729351950557814657492241)
                    ·
                      refine ⟨3547013962918360993119181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729351950557814657492241 3547013962918360993119181)
                      ·
                        rfl

theorem cell23_6907785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 4, 2].length) (baseStart_6907785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907785 prefixEnd_6907785 := by exact prefixLift 6907785
  have htrace : WordTrace (prefixWord ++ tailWord_6907785) baseStart_6907785 baseEnd_6907785 := by
    simpa [prefixWord, tailWord_6907785, baseEnd_6907785] using wordTrace_append hprefix tailTrace_6907785
  have hstable : (prefixWord ++ tailWord_6907785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907785).length < 2 ^ (prefixWord ++ tailWord_6907785).sum := by decide
  have hdescent : baseEnd_6907785 < baseStart_6907785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907805 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_6907805 : Nat := 118140960795 + 6907805 * 2 ^ 59
def prefixEnd_6907805 : Nat := 4983230072969 + 3 ^ 40 * 6907805 * 2
def baseEnd_6907805 : Nat := 3547024232531450914869089

theorem tailTrace_6907805 : CollatzResearch.WordTrace tailWord_6907805 prefixEnd_6907805 3547024232531450914869089 := by
  unfold tailWord_6907805
  simp only [CollatzResearch.WordTrace]
  refine ⟨251948346739209719013684869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167965564492806479342456579 251948346739209719013684869)
  ·
    refine ⟨47240315013601822315065913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251948346739209719013684869 47240315013601822315065913)
    ·
      refine ⟨35430236260201366736299435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47240315013601822315065913 35430236260201366736299435)
      ·
        refine ⟨53145354390302050104449153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35430236260201366736299435 53145354390302050104449153)
        ·
          refine ⟨39859015792726537578336865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53145354390302050104449153 39859015792726537578336865)
          ·
            refine ⟨29894261844544903183752649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39859015792726537578336865 29894261844544903183752649)
            ·
              refine ⟨22420696383408677387814487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29894261844544903183752649 22420696383408677387814487)
              ·
                refine ⟨33631044575113016081721731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22420696383408677387814487 33631044575113016081721731)
                ·
                  refine ⟨50446566862669524122582597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33631044575113016081721731 50446566862669524122582597)
                  ·
                    refine ⟨9458731286750535772984237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50446566862669524122582597 9458731286750535772984237)
                    ·
                      refine ⟨3547024232531450914869089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458731286750535772984237 3547024232531450914869089)
                      ·
                        rfl

theorem cell23_6907805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_6907805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907805 prefixEnd_6907805 := by exact prefixLift 6907805
  have htrace : WordTrace (prefixWord ++ tailWord_6907805) baseStart_6907805 baseEnd_6907805 := by
    simpa [prefixWord, tailWord_6907805, baseEnd_6907805] using wordTrace_append hprefix tailTrace_6907805
  have hstable : (prefixWord ++ tailWord_6907805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907805).length < 2 ^ (prefixWord ++ tailWord_6907805).sum := by decide
  have hdescent : baseEnd_6907805 < baseStart_6907805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907845 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 1, 5, 2]
def baseStart_6907845 : Nat := 118140960795 + 6907845 * 2 ^ 59
def prefixEnd_6907845 : Nat := 4983230072969 + 3 ^ 40 * 6907845 * 2
def baseEnd_6907845 : Nat := 3547044771757630758368905

theorem tailTrace_6907845 : CollatzResearch.WordTrace tailWord_6907845 prefixEnd_6907845 3547044771757630758368905 := by
  unfold tailWord_6907845
  simp only [CollatzResearch.WordTrace]
  refine ⟨251949805659064805845140989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167966537106043203896760659 251949805659064805845140989)
  ·
    refine ⟨94481177122149302191927871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251949805659064805845140989 94481177122149302191927871)
    ·
      refine ⟨141721765683223953287891807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94481177122149302191927871 141721765683223953287891807)
      ·
        refine ⟨212582648524835929931837711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141721765683223953287891807 212582648524835929931837711)
        ·
          refine ⟨318873972787253894897756567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212582648524835929931837711 318873972787253894897756567)
          ·
            refine ⟨478310959180880842346634851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318873972787253894897756567 478310959180880842346634851)
            ·
              refine ⟨717466438771321263519952277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478310959180880842346634851 717466438771321263519952277)
              ·
                refine ⟨33631239317405684227497763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 717466438771321263519952277 33631239317405684227497763)
                ·
                  refine ⟨50446858976108526341246645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33631239317405684227497763 50446858976108526341246645)
                  ·
                    refine ⟨4729393029010174344491873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50446858976108526341246645 4729393029010174344491873)
                    ·
                      refine ⟨3547044771757630758368905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729393029010174344491873 3547044771757630758368905)
                      ·
                        rfl

theorem cell23_6907845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_6907845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907845 prefixEnd_6907845 := by exact prefixLift 6907845
  have htrace : WordTrace (prefixWord ++ tailWord_6907845) baseStart_6907845 baseEnd_6907845 := by
    simpa [prefixWord, tailWord_6907845, baseEnd_6907845] using wordTrace_append hprefix tailTrace_6907845
  have hstable : (prefixWord ++ tailWord_6907845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907845).length < 2 ^ (prefixWord ++ tailWord_6907845).sum := by decide
  have hdescent : baseEnd_6907845 < baseStart_6907845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907886 : List Nat := [4, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_6907886 : Nat := 118140960795 + 6907886 * 2 ^ 59
def prefixEnd_6907886 : Nat := 4983230072969 + 3 ^ 40 * 6907886 * 2
def baseEnd_6907886 : Nat := 3547065824464465097956217

theorem tailTrace_6907886 : CollatzResearch.WordTrace tailWord_6907886 prefixEnd_6907886 3547065824464465097956217 := by
  unfold tailWord_6907886
  simp only [CollatzResearch.WordTrace]
  refine ⟨31493912631489533730922939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167967534034610846564922341 31493912631489533730922939)
  ·
    refine ⟨47240868947234300596384409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31493912631489533730922939 47240868947234300596384409)
    ·
      refine ⟨35430651710425725447288307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47240868947234300596384409 35430651710425725447288307)
      ·
        refine ⟨53145977565638588170932461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35430651710425725447288307 53145977565638588170932461)
        ·
          refine ⟨19929741587114470564099673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53145977565638588170932461 19929741587114470564099673)
          ·
            refine ⟨14947306190335852923074755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19929741587114470564099673 14947306190335852923074755)
            ·
              refine ⟨22420959285503779384612133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14947306190335852923074755 22420959285503779384612133)
              ·
                refine ⟨4203929866031958634614775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22420959285503779384612133 4203929866031958634614775)
                ·
                  refine ⟨6305894799047937951922163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203929866031958634614775 6305894799047937951922163)
                  ·
                    refine ⟨9458842198571906927883245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305894799047937951922163 9458842198571906927883245)
                    ·
                      refine ⟨3547065824464465097956217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458842198571906927883245 3547065824464465097956217)
                      ·
                        rfl

theorem cell23_6907886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_6907886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907886 prefixEnd_6907886 := by exact prefixLift 6907886
  have htrace : WordTrace (prefixWord ++ tailWord_6907886) baseStart_6907886 baseEnd_6907886 := by
    simpa [prefixWord, tailWord_6907886, baseEnd_6907886] using wordTrace_append hprefix tailTrace_6907886
  have hstable : (prefixWord ++ tailWord_6907886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907886).length < 2 ^ (prefixWord ++ tailWord_6907886).sum := by decide
  have hdescent : baseEnd_6907886 < baseStart_6907886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907888 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_6907888 : Nat := 118140960795 + 6907888 * 2 ^ 59
def prefixEnd_6907888 : Nat := 4983230072969 + 3 ^ 40 * 6907888 * 2
def baseEnd_6907888 : Nat := 3547066851425774090131207

theorem tailTrace_6907888 : CollatzResearch.WordTrace tailWord_6907888 prefixEnd_6907888 3547066851425774090131207 := by
  unfold tailWord_6907888
  simp only [CollatzResearch.WordTrace]
  refine ⟨125975686998954512094478159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167967582665272682792637545 125975686998954512094478159)
  ·
    refine ⟨188963530498431768141717239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125975686998954512094478159 188963530498431768141717239)
    ·
      refine ⟨283445295747647652212575859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188963530498431768141717239 283445295747647652212575859)
      ·
        refine ⟨425167943621471478318863789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283445295747647652212575859 425167943621471478318863789)
        ·
          refine ⟨159437978858051804369573921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425167943621471478318863789 159437978858051804369573921)
          ·
            refine ⟨119578484143538853277180441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159437978858051804369573921 119578484143538853277180441)
            ·
              refine ⟨89683863107654139957885331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119578484143538853277180441 89683863107654139957885331)
              ·
                refine ⟨134525794661481209936827997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89683863107654139957885331 134525794661481209936827997)
                ·
                  refine ⟨50447172998055453726310499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134525794661481209936827997 50447172998055453726310499)
                  ·
                    refine ⟨75670759497083180589465749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50447172998055453726310499 75670759497083180589465749)
                    ·
                      refine ⟨3547066851425774090131207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75670759497083180589465749 3547066851425774090131207)
                      ·
                        rfl

theorem cell23_6907888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_6907888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907888 prefixEnd_6907888 := by exact prefixLift 6907888
  have htrace : WordTrace (prefixWord ++ tailWord_6907888) baseStart_6907888 baseEnd_6907888 := by
    simpa [prefixWord, tailWord_6907888, baseEnd_6907888] using wordTrace_append hprefix tailTrace_6907888
  have hstable : (prefixWord ++ tailWord_6907888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907888).length < 2 ^ (prefixWord ++ tailWord_6907888).sum := by decide
  have hdescent : baseEnd_6907888 < baseStart_6907888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907902 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_6907902 : Nat := 118140960795 + 6907902 * 2 ^ 59
def prefixEnd_6907902 : Nat := 4983230072969 + 3 ^ 40 * 6907902 * 2
def baseEnd_6907902 : Nat := 1182358013384979011785381

theorem tailTrace_6907902 : CollatzResearch.WordTrace tailWord_6907902 prefixEnd_6907902 1182358013384979011785381 := by
  unfold tailWord_6907902
  simp only [CollatzResearch.WordTrace]
  refine ⟨31493985577482288072495745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167967923079905536386643973 31493985577482288072495745)
  ·
    refine ⟨23620489183111716054371809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31493985577482288072495745 23620489183111716054371809)
    ·
      refine ⟨17715366887333787040778857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23620489183111716054371809 17715366887333787040778857)
      ·
        refine ⟨13286525165500340280584143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17715366887333787040778857 13286525165500340280584143)
        ·
          refine ⟨19929787748250510420876215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13286525165500340280584143 19929787748250510420876215)
          ·
            refine ⟨29894681622375765631314323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19929787748250510420876215 29894681622375765631314323)
            ·
              refine ⟨44842022433563648446971485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29894681622375765631314323 44842022433563648446971485)
              ·
                refine ⟨16815758412586368167614307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44842022433563648446971485 16815758412586368167614307)
                ·
                  refine ⟨25223637618879552251421461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16815758412586368167614307 25223637618879552251421461)
                  ·
                    refine ⟨1182358013384979011785381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25223637618879552251421461 1182358013384979011785381)
                    ·
                      rfl

theorem cell23_6907902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_6907902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907902 prefixEnd_6907902 := by exact prefixLift 6907902
  have htrace : WordTrace (prefixWord ++ tailWord_6907902) baseStart_6907902 baseEnd_6907902 := by
    simpa [prefixWord, tailWord_6907902, baseEnd_6907902] using wordTrace_append hprefix tailTrace_6907902
  have hstable : (prefixWord ++ tailWord_6907902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907902).length < 2 ^ (prefixWord ++ tailWord_6907902).sum := by decide
  have hdescent : baseEnd_6907902 < baseStart_6907902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907909 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 3, 2, 2]
def baseStart_6907909 : Nat := 118140960795 + 6907909 * 2 ^ 59
def prefixEnd_6907909 : Nat := 4983230072969 + 3 ^ 40 * 6907909 * 2
def baseEnd_6907909 : Nat := 3547077634519518507968611

theorem tailTrace_6907909 : CollatzResearch.WordTrace tailWord_6907909 prefixEnd_6907909 3547077634519518507968611 := by
  unfold tailWord_6907909
  simp only [CollatzResearch.WordTrace]
  refine ⟨251952139930832944775470781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167968093287221963183647187 251952139930832944775470781)
  ·
    refine ⟨94482052474062354290801543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251952139930832944775470781 94482052474062354290801543)
    ·
      refine ⟨141723078711093531436202315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94482052474062354290801543 141723078711093531436202315)
      ·
        refine ⟨212584618066640297154303473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141723078711093531436202315 212584618066640297154303473)
        ·
          refine ⟨159438463549980222865727605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212584618066640297154303473 159438463549980222865727605)
          ·
            refine ⟨14947355957810645893661963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159438463549980222865727605 14947355957810645893661963)
            ·
              refine ⟨22421033936715968840492945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14947355957810645893661963 22421033936715968840492945)
              ·
                refine ⟨16815775452536976630369709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22421033936715968840492945 16815775452536976630369709)
                ·
                  refine ⟨6305915794701366236388641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16815775452536976630369709 6305915794701366236388641)
                  ·
                    refine ⟨4729436846026024677291481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6305915794701366236388641 4729436846026024677291481)
                    ·
                      refine ⟨3547077634519518507968611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729436846026024677291481 3547077634519518507968611)
                      ·
                        rfl

theorem cell23_6907909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_6907909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907909 prefixEnd_6907909 := by exact prefixLift 6907909
  have htrace : WordTrace (prefixWord ++ tailWord_6907909) baseStart_6907909 baseEnd_6907909 := by
    simpa [prefixWord, tailWord_6907909, baseEnd_6907909] using wordTrace_append hprefix tailTrace_6907909
  have hstable : (prefixWord ++ tailWord_6907909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907909).length < 2 ^ (prefixWord ++ tailWord_6907909).sum := by decide
  have hdescent : baseEnd_6907909 < baseStart_6907909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907912 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_6907912 : Nat := 118140960795 + 6907912 * 2 ^ 59
def prefixEnd_6907912 : Nat := 4983230072969 + 3 ^ 40 * 6907912 * 2
def baseEnd_6907912 : Nat := 3547079174961481996231097

theorem tailTrace_6907912 : CollatzResearch.WordTrace tailWord_6907912 prefixEnd_6907912 3547079174961481996231097 := by
  unfold tailWord_6907912
  simp only [CollatzResearch.WordTrace]
  refine ⟨125976124674911038143914995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167968166233214717525219993 125976124674911038143914995)
  ·
    refine ⟨188964187012366557215872493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125976124674911038143914995 188964187012366557215872493)
    ·
      refine ⟨70861570129637458955952185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188964187012366557215872493 70861570129637458955952185)
      ·
        refine ⟨53146177597228094216964139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70861570129637458955952185 53146177597228094216964139)
        ·
          refine ⟨79719266395842141325446209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53146177597228094216964139 79719266395842141325446209)
          ·
            refine ⟨59789449796881605994084657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79719266395842141325446209 59789449796881605994084657)
            ·
              refine ⟨44842087347661204495563493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59789449796881605994084657 44842087347661204495563493)
              ·
                refine ⟨8407891377686475842918155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44842087347661204495563493 8407891377686475842918155)
                ·
                  refine ⟨12611837066529713764377233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8407891377686475842918155 12611837066529713764377233)
                  ·
                    refine ⟨9458877799897285323282925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12611837066529713764377233 9458877799897285323282925)
                    ·
                      refine ⟨3547079174961481996231097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458877799897285323282925 3547079174961481996231097)
                      ·
                        rfl

theorem cell23_6907912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_6907912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907912 prefixEnd_6907912 := by exact prefixLift 6907912
  have htrace : WordTrace (prefixWord ++ tailWord_6907912) baseStart_6907912 baseEnd_6907912 := by
    simpa [prefixWord, tailWord_6907912, baseEnd_6907912] using wordTrace_append hprefix tailTrace_6907912
  have hstable : (prefixWord ++ tailWord_6907912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907912).length < 2 ^ (prefixWord ++ tailWord_6907912).sum := by decide
  have hdescent : baseEnd_6907912 < baseStart_6907912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907915 : List Nat := [1, 1, 1, 1, 6, 1, 5, 7]
def baseStart_6907915 : Nat := 118140960795 + 6907915 * 2 ^ 59
def prefixEnd_6907915 : Nat := 4983230072969 + 3 ^ 40 * 6907915 * 2
def baseEnd_6907915 : Nat := 131373359829757240166429

theorem tailTrace_6907915 : CollatzResearch.WordTrace tailWord_6907915 prefixEnd_6907915 131373359829757240166429 := by
  unfold tailWord_6907915
  simp only [CollatzResearch.WordTrace]
  refine ⟨251952358768811207800189199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167968239179207471866792799 251952358768811207800189199)
  ·
    refine ⟨377928538153216811700283799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251952358768811207800189199 377928538153216811700283799)
    ·
      refine ⟨566892807229825217550425699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377928538153216811700283799 566892807229825217550425699)
      ·
        refine ⟨850339210844737826325638549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566892807229825217550425699 850339210844737826325638549)
        ·
          refine ⟨39859650508347085609014307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 850339210844737826325638549 39859650508347085609014307)
          ·
            refine ⟨59789475762520628413521461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39859650508347085609014307 59789475762520628413521461)
            ·
              refine ⟨5605263352736308913767637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59789475762520628413521461 5605263352736308913767637)
              ·
                refine ⟨131373359829757240166429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5605263352736308913767637 131373359829757240166429)
                ·
                  rfl

theorem cell23_6907915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 7].length) (baseStart_6907915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907915 prefixEnd_6907915 := by exact prefixLift 6907915
  have htrace : WordTrace (prefixWord ++ tailWord_6907915) baseStart_6907915 baseEnd_6907915 := by
    simpa [prefixWord, tailWord_6907915, baseEnd_6907915] using wordTrace_append hprefix tailTrace_6907915
  have hstable : (prefixWord ++ tailWord_6907915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907915).length < 2 ^ (prefixWord ++ tailWord_6907915).sum := by decide
  have hdescent : baseEnd_6907915 < baseStart_6907915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907943 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6907943 : Nat := 118140960795 + 6907943 * 2 ^ 59
def prefixEnd_6907943 : Nat := 4983230072969 + 3 ^ 40 * 6907943 * 2
def baseEnd_6907943 : Nat := 3547095092861771374943455

theorem tailTrace_6907943 : CollatzResearch.WordTrace tailWord_6907943 prefixEnd_6907943 3547095092861771374943455 := by
  unfold tailWord_6907943
  simp only [CollatzResearch.WordTrace]
  refine ⟨251953380012709768582208483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167968920008473179054805655 251953380012709768582208483)
  ·
    refine ⟨377930070019064652873312725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251953380012709768582208483 377930070019064652873312725)
    ·
      refine ⟨8857736016071827801718267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 377930070019064652873312725 8857736016071827801718267)
      ·
        refine ⟨13286604024107741702577401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857736016071827801718267 13286604024107741702577401)
        ·
          refine ⟨9964953018080806276933051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13286604024107741702577401 9964953018080806276933051)
          ·
            refine ⟨14947429527121209415399577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964953018080806276933051 14947429527121209415399577)
            ·
              refine ⟨11210572145340907061549683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14947429527121209415399577 11210572145340907061549683)
              ·
                refine ⟨16815858218011360592324525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11210572145340907061549683 16815858218011360592324525)
                ·
                  refine ⟨6305946831754260222121697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16815858218011360592324525 6305946831754260222121697)
                  ·
                    refine ⟨4729460123815695166591273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6305946831754260222121697 4729460123815695166591273)
                    ·
                      refine ⟨3547095092861771374943455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729460123815695166591273 3547095092861771374943455)
                      ·
                        rfl

theorem cell23_6907943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6907943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907943 prefixEnd_6907943 := by exact prefixLift 6907943
  have htrace : WordTrace (prefixWord ++ tailWord_6907943) baseStart_6907943 baseEnd_6907943 := by
    simpa [prefixWord, tailWord_6907943, baseEnd_6907943] using wordTrace_append hprefix tailTrace_6907943
  have hstable : (prefixWord ++ tailWord_6907943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907943).length < 2 ^ (prefixWord ++ tailWord_6907943).sum := by decide
  have hdescent : baseEnd_6907943 < baseStart_6907943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907956 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_6907956 : Nat := 118140960795 + 6907956 * 2 ^ 59
def prefixEnd_6907956 : Nat := 4983230072969 + 3 ^ 40 * 6907956 * 2
def baseEnd_6907956 : Nat := 3547101768110279824080895

theorem tailTrace_6907956 : CollatzResearch.WordTrace tailWord_6907956 prefixEnd_6907956 3547101768110279824080895 := by
  unfold tailWord_6907956
  simp only [CollatzResearch.WordTrace]
  refine ⟨125976927080831335901215861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167969236107775114534954481 125976927080831335901215861)
  ·
    refine ⟨11810336913827937740738987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125976927080831335901215861 11810336913827937740738987)
    ·
      refine ⟨17715505370741906611108481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11810336913827937740738987 17715505370741906611108481)
      ·
        refine ⟨13286629028056429958331361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17715505370741906611108481 13286629028056429958331361)
        ·
          refine ⟨9964971771042322468748521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13286629028056429958331361 9964971771042322468748521)
          ·
            refine ⟨7473728828281741851561391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9964971771042322468748521 7473728828281741851561391)
            ·
              refine ⟨11210593242422612777342087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473728828281741851561391 11210593242422612777342087)
              ·
                refine ⟨16815889863633919166013131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11210593242422612777342087 16815889863633919166013131)
                ·
                  refine ⟨25223834795450878749019697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16815889863633919166013131 25223834795450878749019697)
                  ·
                    refine ⟨18917876096588159061764773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25223834795450878749019697 18917876096588159061764773)
                    ·
                      refine ⟨3547101768110279824080895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18917876096588159061764773 3547101768110279824080895)
                      ·
                        rfl

theorem cell23_6907956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_6907956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907956 prefixEnd_6907956 := by exact prefixLift 6907956
  have htrace : WordTrace (prefixWord ++ tailWord_6907956) baseStart_6907956 baseEnd_6907956 := by
    simpa [prefixWord, tailWord_6907956, baseEnd_6907956] using wordTrace_append hprefix tailTrace_6907956
  have hstable : (prefixWord ++ tailWord_6907956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907956).length < 2 ^ (prefixWord ++ tailWord_6907956).sum := by decide
  have hdescent : baseEnd_6907956 < baseStart_6907956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907966 : List Nat := [4, 2, 1, 3, 3, 1, 2, 7]
def baseStart_6907966 : Nat := 118140960795 + 6907966 * 2 ^ 59
def prefixEnd_6907966 : Nat := 4983230072969 + 3 ^ 40 * 6907966 * 2
def baseEnd_6907966 : Nat := 131374329737660177220587

theorem tailTrace_6907966 : CollatzResearch.WordTrace tailWord_6907966 prefixEnd_6907966 131374329737660177220587 := by
  unfold tailWord_6907966
  simp only [CollatzResearch.WordTrace]
  refine ⟨31494277361453305438786969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167969479261084295673530501 31494277361453305438786969)
  ·
    refine ⟨23620708021089979079090227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31494277361453305438786969 23620708021089979079090227)
    ·
      refine ⟨35431062031634968618635341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23620708021089979079090227 35431062031634968618635341)
      ·
        refine ⟨13286648261863113231988253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35431062031634968618635341 13286648261863113231988253)
        ·
          refine ⟨4982493098198667461995595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13286648261863113231988253 4982493098198667461995595)
          ·
            refine ⟨7473739647298001192993393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982493098198667461995595 7473739647298001192993393)
            ·
              refine ⟨5605304735473500894745045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7473739647298001192993393 5605304735473500894745045)
              ·
                refine ⟨131374329737660177220587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5605304735473500894745045 131374329737660177220587)
                ·
                  rfl

theorem cell23_6907966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_6907966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907966 prefixEnd_6907966 := by exact prefixLift 6907966
  have htrace : WordTrace (prefixWord ++ tailWord_6907966) baseStart_6907966 baseEnd_6907966 := by
    simpa [prefixWord, tailWord_6907966, baseEnd_6907966] using wordTrace_append hprefix tailTrace_6907966
  have hstable : (prefixWord ++ tailWord_6907966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907966).length < 2 ^ (prefixWord ++ tailWord_6907966).sum := by decide
  have hdescent : baseEnd_6907966 < baseStart_6907966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907985 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_6907985 : Nat := 118140960795 + 6907985 * 2 ^ 59
def prefixEnd_6907985 : Nat := 4983230072969 + 3 ^ 40 * 6907985 * 2
def baseEnd_6907985 : Nat := 3547116659049260210618261

theorem tailTrace_6907985 : CollatzResearch.WordTrace tailWord_6907985 prefixEnd_6907985 3547116659049260210618261 := by
  unfold tailWord_6907985
  simp only [CollatzResearch.WordTrace]
  refine ⟨251954911878557609755237409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167969941252371739836824939 251954911878557609755237409)
  ·
    refine ⟨188966183908918207316428057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251954911878557609755237409 188966183908918207316428057)
    ·
      refine ⟨141724637931688655487321043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188966183908918207316428057 141724637931688655487321043)
      ·
        refine ⟨212586956897532983230981565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141724637931688655487321043 212586956897532983230981565)
        ·
          refine ⟨79720108836574868711618087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212586956897532983230981565 79720108836574868711618087)
          ·
            refine ⟨119580163254862303067427131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79720108836574868711618087 119580163254862303067427131)
            ·
              refine ⟨179370244882293454601140697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119580163254862303067427131 179370244882293454601140697)
              ·
                refine ⟨134527683661720090950855523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179370244882293454601140697 134527683661720090950855523)
                ·
                  refine ⟨201791525492580136426283285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134527683661720090950855523 201791525492580136426283285)
                  ·
                    refine ⟨9458977757464693894982029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201791525492580136426283285 9458977757464693894982029)
                    ·
                      refine ⟨3547116659049260210618261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458977757464693894982029 3547116659049260210618261)
                      ·
                        rfl

theorem cell23_6907985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_6907985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907985 prefixEnd_6907985 := by exact prefixLift 6907985
  have htrace : WordTrace (prefixWord ++ tailWord_6907985) baseStart_6907985 baseEnd_6907985 := by
    simpa [prefixWord, tailWord_6907985, baseEnd_6907985] using wordTrace_append hprefix tailTrace_6907985
  have hstable : (prefixWord ++ tailWord_6907985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907985).length < 2 ^ (prefixWord ++ tailWord_6907985).sum := by decide
  have hdescent : baseEnd_6907985 < baseStart_6907985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908010 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_6908010 : Nat := 118140960795 + 6908010 * 2 ^ 59
def prefixEnd_6908010 : Nat := 4983230072969 + 3 ^ 40 * 6908010 * 2
def baseEnd_6908010 : Nat := 3547129496065622612805647

theorem tailTrace_6908010 : CollatzResearch.WordTrace tailWord_6908010 prefixEnd_6908010 3547129496065622612805647 := by
  unfold tailWord_6908010
  simp only [CollatzResearch.WordTrace]
  refine ⟨62988955925866759756224371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167970549135644692683264989 62988955925866759756224371)
  ·
    refine ⟨94483433888800139634336557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62988955925866759756224371 94483433888800139634336557)
    ·
      refine ⟨35431287708300052362876209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94483433888800139634336557 35431287708300052362876209)
      ·
        refine ⟨26573465781225039272157157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35431287708300052362876209 26573465781225039272157157)
        ·
          refine ⟨4982524833979694863529467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26573465781225039272157157 4982524833979694863529467)
          ·
            refine ⟨7473787250969542295294201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982524833979694863529467 7473787250969542295294201)
            ·
              refine ⟨5605340438227156721470651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7473787250969542295294201 5605340438227156721470651)
              ·
                refine ⟨8408010657340735082205977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605340438227156721470651 8408010657340735082205977)
                ·
                  refine ⟨6306007993005551311654483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8408010657340735082205977 6306007993005551311654483)
                  ·
                    refine ⟨9459011989508326967481725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6306007993005551311654483 9459011989508326967481725)
                    ·
                      refine ⟨3547129496065622612805647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9459011989508326967481725 3547129496065622612805647)
                      ·
                        rfl

theorem cell23_6908010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_6908010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908010 prefixEnd_6908010 := by exact prefixLift 6908010
  have htrace : WordTrace (prefixWord ++ tailWord_6908010) baseStart_6908010 baseEnd_6908010 := by
    simpa [prefixWord, tailWord_6908010, baseEnd_6908010] using wordTrace_append hprefix tailTrace_6908010
  have hstable : (prefixWord ++ tailWord_6908010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908010).length < 2 ^ (prefixWord ++ tailWord_6908010).sum := by decide
  have hdescent : baseEnd_6908010 < baseStart_6908010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908016 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 2, 2, 2]
def baseStart_6908016 : Nat := 118140960795 + 6908016 * 2 ^ 59
def prefixEnd_6908016 : Nat := 4983230072969 + 3 ^ 40 * 6908016 * 2
def baseEnd_6908016 : Nat := 3547132576949549589330619

theorem tailTrace_6908016 : CollatzResearch.WordTrace tailWord_6908016 prefixEnd_6908016 3547132576949549589330619 := by
  unfold tailWord_6908016
  simp only [CollatzResearch.WordTrace]
  refine ⟨125978021270722651024807951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167970695027630201366410601 125978021270722651024807951)
  ·
    refine ⟨188967031906083976537211927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125978021270722651024807951 188967031906083976537211927)
    ·
      refine ⟨283450547859125964805817891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188967031906083976537211927 283450547859125964805817891)
      ·
        refine ⟨425175821788688947208726837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283450547859125964805817891 425175821788688947208726837)
        ·
          refine ⟨39860233292689588800818141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 425175821788688947208726837 39860233292689588800818141)
          ·
            refine ⟨14947587484758595800306803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39860233292689588800818141 14947587484758595800306803)
            ·
              refine ⟨22421381227137893700460205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14947587484758595800306803 22421381227137893700460205)
              ·
                refine ⟨8408017960176710137672577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22421381227137893700460205 8408017960176710137672577)
                ·
                  refine ⟨6306013470132532603254433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8408017960176710137672577 6306013470132532603254433)
                  ·
                    refine ⟨4729510102599399452440825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6306013470132532603254433 4729510102599399452440825)
                    ·
                      refine ⟨3547132576949549589330619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729510102599399452440825 3547132576949549589330619)
                      ·
                        rfl

theorem cell23_6908016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 2, 2].length) (baseStart_6908016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908016 prefixEnd_6908016 := by exact prefixLift 6908016
  have htrace : WordTrace (prefixWord ++ tailWord_6908016) baseStart_6908016 baseEnd_6908016 := by
    simpa [prefixWord, tailWord_6908016, baseEnd_6908016] using wordTrace_append hprefix tailTrace_6908016
  have hstable : (prefixWord ++ tailWord_6908016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908016).length < 2 ^ (prefixWord ++ tailWord_6908016).sum := by decide
  have hdescent : baseEnd_6908016 < baseStart_6908016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908095 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 8]
def baseStart_6908095 : Nat := 118140960795 + 6908095 * 2 ^ 59
def prefixEnd_6908095 : Nat := 4983230072969 + 3 ^ 40 * 6908095 * 2
def baseEnd_6908095 : Nat := 394130349102361642249195

theorem tailTrace_6908095 : CollatzResearch.WordTrace tailWord_6908095 prefixEnd_6908095 394130349102361642249195 := by
  unfold tailWord_6908095
  simp only [CollatzResearch.WordTrace]
  refine ⟨251958923908159098541741739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167972615938772732361161159 251958923908159098541741739)
  ·
    refine ⟨377938385862238647812612609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251958923908159098541741739 377938385862238647812612609)
    ·
      refine ⟨283453789396678985859459457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377938385862238647812612609 283453789396678985859459457)
      ·
        refine ⟨212590342047509239394594593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283453789396678985859459457 212590342047509239394594593)
        ·
          refine ⟨159442756535631929545945945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212590342047509239394594593 159442756535631929545945945)
          ·
            refine ⟨119582067401723947159459459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159442756535631929545945945 119582067401723947159459459)
            ·
              refine ⟨179373101102585920739189189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119582067401723947159459459 179373101102585920739189189)
              ·
                refine ⟨33632456456734860138597973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179373101102585920739189189 33632456456734860138597973)
                ·
                  refine ⟨394130349102361642249195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33632456456734860138597973 394130349102361642249195)
                  ·
                    rfl

theorem cell23_6908095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 8].length) (baseStart_6908095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908095 prefixEnd_6908095 := by exact prefixLift 6908095
  have htrace : WordTrace (prefixWord ++ tailWord_6908095) baseStart_6908095 baseEnd_6908095 := by
    simpa [prefixWord, tailWord_6908095, baseEnd_6908095] using wordTrace_append hprefix tailTrace_6908095
  have hstable : (prefixWord ++ tailWord_6908095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908095).length < 2 ^ (prefixWord ++ tailWord_6908095).sum := by decide
  have hdescent : baseEnd_6908095 < baseStart_6908095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908129 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 6]
def baseStart_6908129 : Nat := 118140960795 + 6908129 * 2 ^ 59
def prefixEnd_6908129 : Nat := 4983230072969 + 3 ^ 40 * 6908129 * 2
def baseEnd_6908129 : Nat := 394132288918167516357511

theorem tailTrace_6908129 : CollatzResearch.WordTrace tailWord_6908129 prefixEnd_6908129 394132288918167516357511 := by
  unfold tailWord_6908129
  simp only [CollatzResearch.WordTrace]
  refine ⟨251960163990035922348479441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167973442660023948232319627 251960163990035922348479441)
  ·
    refine ⟨188970122992526941761359581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251960163990035922348479441 188970122992526941761359581)
    ·
      refine ⟨70863796122197603160509843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188970122992526941761359581 70863796122197603160509843)
      ·
        refine ⟨106295694183296404740764765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70863796122197603160509843 106295694183296404740764765)
        ·
          refine ⟨39860885318736151777786787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106295694183296404740764765 39860885318736151777786787)
          ·
            refine ⟨59791327978104227666680181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39860885318736151777786787 59791327978104227666680181)
            ·
              refine ⟨5605436997947271343751267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59791327978104227666680181 5605436997947271343751267)
              ·
                refine ⟨8408155496920907015626901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605436997947271343751267 8408155496920907015626901)
                ·
                  refine ⟨394132288918167516357511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8408155496920907015626901 394132288918167516357511)
                  ·
                    rfl

theorem cell23_6908129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 6].length) (baseStart_6908129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908129 prefixEnd_6908129 := by exact prefixLift 6908129
  have htrace : WordTrace (prefixWord ++ tailWord_6908129) baseStart_6908129 baseEnd_6908129 := by
    simpa [prefixWord, tailWord_6908129, baseEnd_6908129] using wordTrace_append hprefix tailTrace_6908129
  have hstable : (prefixWord ++ tailWord_6908129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908129).length < 2 ^ (prefixWord ++ tailWord_6908129).sum := by decide
  have hdescent : baseEnd_6908129 < baseStart_6908129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908139 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 3]
def baseStart_6908139 : Nat := 118140960795 + 6908139 * 2 ^ 59
def prefixEnd_6908139 : Nat := 4983230072969 + 3 ^ 40 * 6908139 * 2
def baseEnd_6908139 : Nat := 3547195735070052608092553

theorem tailTrace_6908139 : CollatzResearch.WordTrace tailWord_6908139 prefixEnd_6908139 3547195735070052608092553 := by
  unfold tailWord_6908139
  simp only [CollatzResearch.WordTrace]
  refine ⟨251960528719999694056343471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167973685813333129370895647 251960528719999694056343471)
  ·
    refine ⟨377940793079999541084515207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251960528719999694056343471 377940793079999541084515207)
    ·
      refine ⟨566911189619999311626772811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377940793079999541084515207 566911189619999311626772811)
      ·
        refine ⟨850366784429998967440159217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566911189619999311626772811 850366784429998967440159217)
        ·
          refine ⟨637775088322499225580119413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850366784429998967440159217 637775088322499225580119413)
          ·
            refine ⟨59791414530234302398136195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 637775088322499225580119413 59791414530234302398136195)
            ·
              refine ⟨89687121795351453597204293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59791414530234302398136195 89687121795351453597204293)
              ·
                refine ⟨16816335336628397549475805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89687121795351453597204293 16816335336628397549475805)
                ·
                  refine ⟨6306125751235649081053427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16816335336628397549475805 6306125751235649081053427)
                  ·
                    refine ⟨9459188626853473621580141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6306125751235649081053427 9459188626853473621580141)
                    ·
                      refine ⟨3547195735070052608092553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9459188626853473621580141 3547195735070052608092553)
                      ·
                        rfl

theorem cell23_6908139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 3].length) (baseStart_6908139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908139 prefixEnd_6908139 := by exact prefixLift 6908139
  have htrace : WordTrace (prefixWord ++ tailWord_6908139) baseStart_6908139 baseEnd_6908139 := by
    simpa [prefixWord, tailWord_6908139, baseEnd_6908139] using wordTrace_append hprefix tailTrace_6908139
  have hstable : (prefixWord ++ tailWord_6908139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908139).length < 2 ^ (prefixWord ++ tailWord_6908139).sum := by decide
  have hdescent : baseEnd_6908139 < baseStart_6908139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908196 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_6908196 : Nat := 118140960795 + 6908196 * 2 ^ 59
def prefixEnd_6908196 : Nat := 4983230072969 + 3 ^ 40 * 6908196 * 2
def baseEnd_6908196 : Nat := 3547225003467358885079791

theorem tailTrace_6908196 : CollatzResearch.WordTrace tailWord_6908196 prefixEnd_6908196 3547225003467358885079791 := by
  unfold tailWord_6908196
  simp only [CollatzResearch.WordTrace]
  refine ⟨125981303840396596395584221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167975071787195461860778961 125981303840396596395584221)
  ·
    refine ⟨47242988940148723648344083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125981303840396596395584221 47242988940148723648344083)
    ·
      refine ⟨70864483410223085472516125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47242988940148723648344083 70864483410223085472516125)
      ·
        refine ⟨26574181278833657052193547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70864483410223085472516125 26574181278833657052193547)
        ·
          refine ⟨39861271918250485578290321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26574181278833657052193547 39861271918250485578290321)
          ·
            refine ⟨29895953938687864183717741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39861271918250485578290321 29895953938687864183717741)
            ·
              refine ⟨11210982727007949068894153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29895953938687864183717741 11210982727007949068894153)
              ·
                refine ⟨8408237045255961801670615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11210982727007949068894153 8408237045255961801670615)
                ·
                  refine ⟨12612355567883942702505923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8408237045255961801670615 12612355567883942702505923)
                  ·
                    refine ⟨18918533351825914053758885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12612355567883942702505923 18918533351825914053758885)
                    ·
                      refine ⟨3547225003467358885079791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18918533351825914053758885 3547225003467358885079791)
                      ·
                        rfl

theorem cell23_6908196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_6908196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908196 prefixEnd_6908196 := by exact prefixLift 6908196
  have htrace : WordTrace (prefixWord ++ tailWord_6908196) baseStart_6908196 baseEnd_6908196 := by
    simpa [prefixWord, tailWord_6908196, baseEnd_6908196] using wordTrace_append hprefix tailTrace_6908196
  have hstable : (prefixWord ++ tailWord_6908196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908196).length < 2 ^ (prefixWord ++ tailWord_6908196).sum := by decide
  have hdescent : baseEnd_6908196 < baseStart_6908196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908232 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 2, 7]
def baseStart_6908232 : Nat := 118140960795 + 6908232 * 2 ^ 59
def prefixEnd_6908232 : Nat := 4983230072969 + 3 ^ 40 * 6908232 * 2
def baseEnd_6908232 : Nat := 1182414496256973581409875

theorem tailTrace_6908232 : CollatzResearch.WordTrace tailWord_6908232 prefixEnd_6908232 1182414496256973581409875 := by
  unfold tailWord_6908232
  simp only [CollatzResearch.WordTrace]
  refine ⟨125981960354331385469739475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167975947139108513959652633 125981960354331385469739475)
  ·
    refine ⟨188972940531497078204609213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125981960354331385469739475 188972940531497078204609213)
    ·
      refine ⟨70864852699311404326728455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188972940531497078204609213 70864852699311404326728455)
      ·
        refine ⟨106297279048967106490092683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70864852699311404326728455 106297279048967106490092683)
        ·
          refine ⟨159445918573450659735139025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106297279048967106490092683 159445918573450659735139025)
          ·
            refine ⟨119584438930087994801354269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159445918573450659735139025 119584438930087994801354269)
            ·
              refine ⟨44844164598782998050507851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119584438930087994801354269 44844164598782998050507851)
              ·
                refine ⟨67266246898174497075761777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44844164598782998050507851 67266246898174497075761777)
                ·
                  refine ⟨50449685173630872806821333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67266246898174497075761777 50449685173630872806821333)
                  ·
                    refine ⟨1182414496256973581409875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50449685173630872806821333 1182414496256973581409875)
                    ·
                      rfl

theorem cell23_6908232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_6908232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908232 prefixEnd_6908232 := by exact prefixLift 6908232
  have htrace : WordTrace (prefixWord ++ tailWord_6908232) baseStart_6908232 baseEnd_6908232 := by
    simpa [prefixWord, tailWord_6908232, baseEnd_6908232] using wordTrace_append hprefix tailTrace_6908232
  have hstable : (prefixWord ++ tailWord_6908232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908232).length < 2 ^ (prefixWord ++ tailWord_6908232).sum := by decide
  have hdescent : baseEnd_6908232 < baseStart_6908232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908282 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_6908282 : Nat := 118140960795 + 6908282 * 2 ^ 59
def prefixEnd_6908282 : Nat := 4983230072969 + 3 ^ 40 * 6908282 * 2
def baseEnd_6908282 : Nat := 3547269162803645548604395

theorem tailTrace_6908282 : CollatzResearch.WordTrace tailWord_6908282 prefixEnd_6908282 3547269162803645548604395 := by
  unfold tailWord_6908282
  simp only [CollatzResearch.WordTrace]
  refine ⟨62991436089620407369699775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167977162905654419652532733 62991436089620407369699775)
  ·
    refine ⟨94487154134430611054549663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62991436089620407369699775 94487154134430611054549663)
    ·
      refine ⟨141730731201645916581824495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94487154134430611054549663 141730731201645916581824495)
      ·
        refine ⟨212596096802468874872736743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141730731201645916581824495 212596096802468874872736743)
        ·
          refine ⟨318894145203703312309105115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212596096802468874872736743 318894145203703312309105115)
          ·
            refine ⟨478341217805554968463657673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318894145203703312309105115 478341217805554968463657673)
            ·
              refine ⟨358755913354166226347743255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478341217805554968463657673 358755913354166226347743255)
              ·
                refine ⟨538133870031249339521614883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358755913354166226347743255 538133870031249339521614883)
                ·
                  refine ⟨807200805046874009282422325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538133870031249339521614883 807200805046874009282422325)
                  ·
                    refine ⟨75675075473144438370227093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 807200805046874009282422325 75675075473144438370227093)
                    ·
                      refine ⟨3547269162803645548604395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75675075473144438370227093 3547269162803645548604395)
                      ·
                        rfl

theorem cell23_6908282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_6908282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908282 prefixEnd_6908282 := by exact prefixLift 6908282
  have htrace : WordTrace (prefixWord ++ tailWord_6908282) baseStart_6908282 baseEnd_6908282 := by
    simpa [prefixWord, tailWord_6908282, baseEnd_6908282] using wordTrace_append hprefix tailTrace_6908282
  have hstable : (prefixWord ++ tailWord_6908282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908282).length < 2 ^ (prefixWord ++ tailWord_6908282).sum := by decide
  have hdescent : baseEnd_6908282 < baseStart_6908282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908299 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4]
def baseStart_6908299 : Nat := 118140960795 + 6908299 * 2 ^ 59
def prefixEnd_6908299 : Nat := 4983230072969 + 3 ^ 40 * 6908299 * 2
def baseEnd_6908299 : Nat := 3547277891974771982091817

theorem tailTrace_6908299 : CollatzResearch.WordTrace tailWord_6908299 prefixEnd_6908299 3547277891974771982091817 := by
  unfold tailWord_6908299
  simp only [CollatzResearch.WordTrace]
  refine ⟨251966364399420041382167951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167977576266280027588111967 251966364399420041382167951)
  ·
    refine ⟨377949546599130062073251927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251966364399420041382167951 377949546599130062073251927)
    ·
      refine ⟨566924319898695093109877891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377949546599130062073251927 566924319898695093109877891)
      ·
        refine ⟨850386479848042639664816837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566924319898695093109877891 850386479848042639664816837)
        ·
          refine ⟨159447464971507994937153157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 850386479848042639664816837 159447464971507994937153157)
          ·
            refine ⟨29896399682157749050716217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159447464971507994937153157 29896399682157749050716217)
            ·
              refine ⟨22422299761618311788037163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29896399682157749050716217 22422299761618311788037163)
              ·
                refine ⟨33633449642427467682055745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22422299761618311788037163 33633449642427467682055745)
                ·
                  refine ⟨25225087231820600761541809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33633449642427467682055745 25225087231820600761541809)
                  ·
                    refine ⟨18918815423865450571156357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25225087231820600761541809 18918815423865450571156357)
                    ·
                      refine ⟨3547277891974771982091817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18918815423865450571156357 3547277891974771982091817)
                      ·
                        rfl

theorem cell23_6908299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_6908299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908299 prefixEnd_6908299 := by exact prefixLift 6908299
  have htrace : WordTrace (prefixWord ++ tailWord_6908299) baseStart_6908299 baseEnd_6908299 := by
    simpa [prefixWord, tailWord_6908299, baseEnd_6908299] using wordTrace_append hprefix tailTrace_6908299
  have hstable : (prefixWord ++ tailWord_6908299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908299).length < 2 ^ (prefixWord ++ tailWord_6908299).sum := by decide
  have hdescent : baseEnd_6908299 < baseStart_6908299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908343 : List Nat := [1, 1, 3, 1, 3, 4, 3, 2, 5]
def baseStart_6908343 : Nat := 118140960795 + 6908343 * 2 ^ 59
def prefixEnd_6908343 : Nat := 4983230072969 + 3 ^ 40 * 6908343 * 2
def baseEnd_6908343 : Nat := 394144498347063312215735

theorem tailTrace_6908343 : CollatzResearch.WordTrace tailWord_6908343 prefixEnd_6908343 394144498347063312215735 := by
  unfold tailWord_6908343
  simp only [CollatzResearch.WordTrace]
  refine ⟨251967969211260636896769683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167978646140840424597846455 251967969211260636896769683)
  ·
    refine ⟨377951953816890955345154525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251967969211260636896769683 377951953816890955345154525)
    ·
      refine ⟨141731982681334108254432947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377951953816890955345154525 141731982681334108254432947)
      ·
        refine ⟨212597974022001162381649421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141731982681334108254432947 212597974022001162381649421)
        ·
          refine ⟨79724240258250435893118533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212597974022001162381649421 79724240258250435893118533)
          ·
            refine ⟨14948295048421956729959725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79724240258250435893118533 14948295048421956729959725)
            ·
              refine ⟨5605610643158233773734897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14948295048421956729959725 5605610643158233773734897)
              ·
                refine ⟨4204207982368675330301173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5605610643158233773734897 4204207982368675330301173)
                ·
                  refine ⟨394144498347063312215735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4204207982368675330301173 394144498347063312215735)
                  ·
                    rfl

theorem cell23_6908343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 5].length) (baseStart_6908343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908343 prefixEnd_6908343 := by exact prefixLift 6908343
  have htrace : WordTrace (prefixWord ++ tailWord_6908343) baseStart_6908343 baseEnd_6908343 := by
    simpa [prefixWord, tailWord_6908343, baseEnd_6908343] using wordTrace_append hprefix tailTrace_6908343
  have hstable : (prefixWord ++ tailWord_6908343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908343).length < 2 ^ (prefixWord ++ tailWord_6908343).sum := by decide
  have hdescent : baseEnd_6908343 < baseStart_6908343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908349 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6908349 : Nat := 118140960795 + 6908349 * 2 ^ 59
def prefixEnd_6908349 : Nat := 4983230072969 + 3 ^ 40 * 6908349 * 2
def baseEnd_6908349 : Nat := 3547303566007496786466587

theorem tailTrace_6908349 : CollatzResearch.WordTrace tailWord_6908349 prefixEnd_6908349 3547303566007496786466587 := by
  unfold tailWord_6908349
  simp only [CollatzResearch.WordTrace]
  refine ⟨251968188049238899921488101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167978792032825933280992067 251968188049238899921488101)
  ·
    refine ⟨47244035259232293735279019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251968188049238899921488101 47244035259232293735279019)
    ·
      refine ⟨70866052888848440602918529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47244035259232293735279019 70866052888848440602918529)
      ·
        refine ⟨53149539666636330452188897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70866052888848440602918529 53149539666636330452188897)
        ·
          refine ⟨39862154749977247839141673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53149539666636330452188897 39862154749977247839141673)
          ·
            refine ⟨29896616062482935879356255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39862154749977247839141673 29896616062482935879356255)
            ·
              refine ⟨44844924093724403819034383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29896616062482935879356255 44844924093724403819034383)
              ·
                refine ⟨67267386140586605728551575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44844924093724403819034383 67267386140586605728551575)
                ·
                  refine ⟨100901079210879908592827363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67267386140586605728551575 100901079210879908592827363)
                  ·
                    refine ⟨151351618816319862889241045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100901079210879908592827363 151351618816319862889241045)
                    ·
                      refine ⟨3547303566007496786466587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151351618816319862889241045 3547303566007496786466587)
                      ·
                        rfl

theorem cell23_6908349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6908349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908349 prefixEnd_6908349 := by exact prefixLift 6908349
  have htrace : WordTrace (prefixWord ++ tailWord_6908349) baseStart_6908349 baseEnd_6908349 := by
    simpa [prefixWord, tailWord_6908349, baseEnd_6908349] using wordTrace_append hprefix tailTrace_6908349
  have hstable : (prefixWord ++ tailWord_6908349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908349).length < 2 ^ (prefixWord ++ tailWord_6908349).sum := by decide
  have hdescent : baseEnd_6908349 < baseStart_6908349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908376 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 4, 4, 2]
def baseStart_6908376 : Nat := 118140960795 + 6908376 * 2 ^ 59
def prefixEnd_6908376 : Nat := 4983230072969 + 3 ^ 40 * 6908376 * 2
def baseEnd_6908376 : Nat := 3547317429985168180828963

theorem tailTrace_6908376 : CollatzResearch.WordTrace tailWord_6908376 prefixEnd_6908376 3547317429985168180828963 := by
  unfold tailWord_6908376
  simp only [CollatzResearch.WordTrace]
  refine ⟨125984586410070541766360491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167979448546760722355147321 125984586410070541766360491)
  ·
    refine ⟨188976879615105812649540737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125984586410070541766360491 188976879615105812649540737)
    ·
      refine ⟨141732659711329359487155553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188976879615105812649540737 141732659711329359487155553)
      ·
        refine ⟨106299494783497019615366665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141732659711329359487155553 106299494783497019615366665)
        ·
          refine ⟨79724621087622764711524999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106299494783497019615366665 79724621087622764711524999)
          ·
            refine ⟨119586931631434147067287499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79724621087622764711524999 119586931631434147067287499)
            ·
              refine ⟨179380397447151220600931249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119586931631434147067287499 179380397447151220600931249)
              ·
                refine ⟨134535298085363415450698437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179380397447151220600931249 134535298085363415450698437)
                ·
                  refine ⟨25225368391005640397005957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134535298085363415450698437 25225368391005640397005957)
                  ·
                    refine ⟨4729756573313557574438617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25225368391005640397005957 4729756573313557574438617)
                    ·
                      refine ⟨3547317429985168180828963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729756573313557574438617 3547317429985168180828963)
                      ·
                        rfl

theorem cell23_6908376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_6908376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908376 prefixEnd_6908376 := by exact prefixLift 6908376
  have htrace : WordTrace (prefixWord ++ tailWord_6908376) baseStart_6908376 baseEnd_6908376 := by
    simpa [prefixWord, tailWord_6908376, baseEnd_6908376] using wordTrace_append hprefix tailTrace_6908376
  have hstable : (prefixWord ++ tailWord_6908376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908376).length < 2 ^ (prefixWord ++ tailWord_6908376).sum := by decide
  have hdescent : baseEnd_6908376 < baseStart_6908376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908396 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_6908396 : Nat := 118140960795 + 6908396 * 2 ^ 59
def prefixEnd_6908396 : Nat := 4983230072969 + 3 ^ 40 * 6908396 * 2
def baseEnd_6908396 : Nat := 3547327699598258102578871

theorem tailTrace_6908396 : CollatzResearch.WordTrace tailWord_6908396 prefixEnd_6908396 3547327699598258102578871 := by
  unfold tailWord_6908396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125984951140034313474224521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167979934853379084632299361 125984951140034313474224521)
  ·
    refine ⟨94488713355025735105668391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125984951140034313474224521 94488713355025735105668391)
    ·
      refine ⟨141733070032538602658502587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94488713355025735105668391 141733070032538602658502587)
      ·
        refine ⟨212599605048807903987753881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141733070032538602658502587 212599605048807903987753881)
        ·
          refine ⟨159449703786605927990815411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212599605048807903987753881 159449703786605927990815411)
          ·
            refine ⟨239174555679908891986223117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159449703786605927990815411 239174555679908891986223117)
            ·
              refine ⟨89690458379965834494833669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239174555679908891986223117 89690458379965834494833669)
              ·
                refine ⟨16816960946243593967781313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89690458379965834494833669 16816960946243593967781313)
                ·
                  refine ⟨12612720709682695475835985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16816960946243593967781313 12612720709682695475835985)
                  ·
                    refine ⟨9459540532262021606876989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12612720709682695475835985 9459540532262021606876989)
                    ·
                      refine ⟨3547327699598258102578871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9459540532262021606876989 3547327699598258102578871)
                      ·
                        rfl

theorem cell23_6908396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_6908396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908396 prefixEnd_6908396 := by exact prefixLift 6908396
  have htrace : WordTrace (prefixWord ++ tailWord_6908396) baseStart_6908396 baseEnd_6908396 := by
    simpa [prefixWord, tailWord_6908396, baseEnd_6908396] using wordTrace_append hprefix tailTrace_6908396
  have hstable : (prefixWord ++ tailWord_6908396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908396).length < 2 ^ (prefixWord ++ tailWord_6908396).sum := by decide
  have hdescent : baseEnd_6908396 < baseStart_6908396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908403 : List Nat := [1, 1, 1, 2, 2, 2, 5, 4, 1, 4]
def baseStart_6908403 : Nat := 118140960795 + 6908403 * 2 ^ 59
def prefixEnd_6908403 : Nat := 4983230072969 + 3 ^ 40 * 6908403 * 2
def baseEnd_6908403 : Nat := 1182443764654279858397113

theorem tailTrace_6908403 : CollatzResearch.WordTrace tailWord_6908403 prefixEnd_6908403 1182443764654279858397113 := by
  unfold tailWord_6908403
  simp only [CollatzResearch.WordTrace]
  refine ⟨251970157591043267143953863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167980105060695511429302575 251970157591043267143953863)
  ·
    refine ⟨377955236386564900715930795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251970157591043267143953863 377955236386564900715930795)
    ·
      refine ⟨566932854579847351073896193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377955236386564900715930795 566932854579847351073896193)
      ·
        refine ⟨425199640934885513305422145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566932854579847351073896193 425199640934885513305422145)
        ·
          refine ⟨318899730701164134979066609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425199640934885513305422145 318899730701164134979066609)
          ·
            refine ⟨239174798025873101234299957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318899730701164134979066609 239174798025873101234299957)
            ·
              refine ⟨22422637314925603240715621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239174798025873101234299957 22422637314925603240715621)
              ·
                refine ⟨4204244496548550607634179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22422637314925603240715621 4204244496548550607634179)
                ·
                  refine ⟨6306366744822825911451269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4204244496548550607634179 6306366744822825911451269)
                  ·
                    refine ⟨1182443764654279858397113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6306366744822825911451269 1182443764654279858397113)
                    ·
                      rfl

theorem cell23_6908403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 4].length) (baseStart_6908403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908403 prefixEnd_6908403 := by exact prefixLift 6908403
  have htrace : WordTrace (prefixWord ++ tailWord_6908403) baseStart_6908403 baseEnd_6908403 := by
    simpa [prefixWord, tailWord_6908403, baseEnd_6908403] using wordTrace_append hprefix tailTrace_6908403
  have hstable : (prefixWord ++ tailWord_6908403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908403).length < 2 ^ (prefixWord ++ tailWord_6908403).sum := by decide
  have hdescent : baseEnd_6908403 < baseStart_6908403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908430 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_6908430 : Nat := 118140960795 + 6908430 * 2 ^ 59
def prefixEnd_6908430 : Nat := 4983230072969 + 3 ^ 40 * 6908430 * 2
def baseEnd_6908430 : Nat := 3547345157940510969553715

theorem tailTrace_6908430 : CollatzResearch.WordTrace tailWord_6908430 prefixEnd_6908430 3547345157940510969553715 := by
  unfold tailWord_6908430
  simp only [CollatzResearch.WordTrace]
  refine ⟨31496392795243181344398343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167980761574630300503457829 31496392795243181344398343)
  ·
    refine ⟨47244589192864772016597515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31496392795243181344398343 47244589192864772016597515)
    ·
      refine ⟨70866883789297158024896273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47244589192864772016597515 70866883789297158024896273)
      ·
        refine ⟨53150162841972868518672205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70866883789297158024896273 53150162841972868518672205)
        ·
          refine ⟨19931311065739825694502077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53150162841972868518672205 19931311065739825694502077)
          ·
            refine ⟨7474241649652434635438279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19931311065739825694502077 7474241649652434635438279)
            ·
              refine ⟨11211362474478651953157419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7474241649652434635438279 11211362474478651953157419)
              ·
                refine ⟨16817043711717977929736129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11211362474478651953157419 16817043711717977929736129)
                ·
                  refine ⟨12612782783788483447302097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16817043711717977929736129 12612782783788483447302097)
                  ·
                    refine ⟨9459587087841362585476573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12612782783788483447302097 9459587087841362585476573)
                    ·
                      refine ⟨3547345157940510969553715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9459587087841362585476573 3547345157940510969553715)
                      ·
                        rfl

theorem cell23_6908430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_6908430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908430 prefixEnd_6908430 := by exact prefixLift 6908430
  have htrace : WordTrace (prefixWord ++ tailWord_6908430) baseStart_6908430 baseEnd_6908430 := by
    simpa [prefixWord, tailWord_6908430, baseEnd_6908430] using wordTrace_append hprefix tailTrace_6908430
  have hstable : (prefixWord ++ tailWord_6908430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908430).length < 2 ^ (prefixWord ++ tailWord_6908430).sum := by decide
  have hdescent : baseEnd_6908430 < baseStart_6908430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908453 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 2, 3, 2]
def baseStart_6908453 : Nat := 118140960795 + 6908453 * 2 ^ 59
def prefixEnd_6908453 : Nat := 4983230072969 + 3 ^ 40 * 6908453 * 2
def baseEnd_6908453 : Nat := 3547356967995564379566109

theorem tailTrace_6908453 : CollatzResearch.WordTrace tailWord_6908453 prefixEnd_6908453 3547356967995564379566109 := by
  unfold tailWord_6908453
  simp only [CollatzResearch.WordTrace]
  refine ⟨251971981240862125683274013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167981320827241417122182675 251971981240862125683274013)
  ·
    refine ⟨94489492965323297131227755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251971981240862125683274013 94489492965323297131227755)
    ·
      refine ⟨141734239447984945696841633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94489492965323297131227755 141734239447984945696841633)
      ·
        refine ⟨106300679585988709272631225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141734239447984945696841633 106300679585988709272631225)
        ·
          refine ⟨79725509689491531954473419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106300679585988709272631225 79725509689491531954473419)
          ·
            refine ⟨119588264534237297931710129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79725509689491531954473419 119588264534237297931710129)
            ·
              refine ⟨89691198400677973448782597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119588264534237297931710129 89691198400677973448782597)
              ·
                refine ⟨16817099700127120021646737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89691198400677973448782597 16817099700127120021646737)
                ·
                  refine ⟨12612824775095340016235053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16817099700127120021646737 12612824775095340016235053)
                  ·
                    refine ⟨4729809290660752506088145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12612824775095340016235053 4729809290660752506088145)
                    ·
                      refine ⟨3547356967995564379566109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729809290660752506088145 3547356967995564379566109)
                      ·
                        rfl

theorem cell23_6908453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_6908453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908453 prefixEnd_6908453 := by exact prefixLift 6908453
  have htrace : WordTrace (prefixWord ++ tailWord_6908453) baseStart_6908453 baseEnd_6908453 := by
    simpa [prefixWord, tailWord_6908453, baseEnd_6908453] using wordTrace_append hprefix tailTrace_6908453
  have hstable : (prefixWord ++ tailWord_6908453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908453).length < 2 ^ (prefixWord ++ tailWord_6908453).sum := by decide
  have hdescent : baseEnd_6908453 < baseStart_6908453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908459 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 3, 6]
def baseStart_6908459 : Nat := 118140960795 + 6908459 * 2 ^ 59
def prefixEnd_6908459 : Nat := 4983230072969 + 3 ^ 40 * 6908459 * 2
def baseEnd_6908459 : Nat := 1182453349626497118697027

theorem tailTrace_6908459 : CollatzResearch.WordTrace tailWord_6908459 prefixEnd_6908459 1182453349626497118697027 := by
  unfold tailWord_6908459
  simp only [CollatzResearch.WordTrace]
  refine ⟨251972200078840388707992431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167981466719226925805328287 251972200078840388707992431)
  ·
    refine ⟨377958300118260583061988647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251972200078840388707992431 377958300118260583061988647)
    ·
      refine ⟨566937450177390874592982971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377958300118260583061988647 566937450177390874592982971)
      ·
        refine ⟨850406175266086311889474457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566937450177390874592982971 850406175266086311889474457)
        ·
          refine ⟨637804631449564733917105843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850406175266086311889474457 637804631449564733917105843)
          ·
            refine ⟨956706947174347100875658765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637804631449564733917105843 956706947174347100875658765)
            ·
              refine ⟨358765105190380162828372037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 956706947174347100875658765 358765105190380162828372037)
              ·
                refine ⟨67268457223196280530319757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358765105190380162828372037 67268457223196280530319757)
                ·
                  refine ⟨25225671458698605198869909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67268457223196280530319757 25225671458698605198869909)
                  ·
                    refine ⟨1182453349626497118697027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25225671458698605198869909 1182453349626497118697027)
                    ·
                      rfl

theorem cell23_6908459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 6].length) (baseStart_6908459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908459 prefixEnd_6908459 := by exact prefixLift 6908459
  have htrace : WordTrace (prefixWord ++ tailWord_6908459) baseStart_6908459 baseEnd_6908459 := by
    simpa [prefixWord, tailWord_6908459, baseEnd_6908459] using wordTrace_append hprefix tailTrace_6908459
  have hstable : (prefixWord ++ tailWord_6908459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908459).length < 2 ^ (prefixWord ++ tailWord_6908459).sum := by decide
  have hdescent : baseEnd_6908459 < baseStart_6908459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908466 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_6908466 : Nat := 118140960795 + 6908466 * 2 ^ 59
def prefixEnd_6908466 : Nat := 4983230072969 + 3 ^ 40 * 6908466 * 2
def baseEnd_6908466 : Nat := 3547363643244072828703549

theorem tailTrace_6908466 : CollatzResearch.WordTrace tailWord_6908466 prefixEnd_6908466 3547363643244072828703549 := by
  unfold tailWord_6908466
  simp only [CollatzResearch.WordTrace]
  refine ⟨62993113847453757225874313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167981636926543352602331501 62993113847453757225874313)
  ·
    refine ⟨47244835385590317919405735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62993113847453757225874313 47244835385590317919405735)
    ·
      refine ⟨70867253078385476879108603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47244835385590317919405735 70867253078385476879108603)
      ·
        refine ⟨106300879617578215318662905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70867253078385476879108603 106300879617578215318662905)
        ·
          refine ⟨79725659713183661488997179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106300879617578215318662905 79725659713183661488997179)
          ·
            refine ⟨119588489569775492233495769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79725659713183661488997179 119588489569775492233495769)
            ·
              refine ⟨89691367177331619175121827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119588489569775492233495769 89691367177331619175121827)
              ·
                refine ⟨134537050765997428762682741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89691367177331619175121827 134537050765997428762682741)
                ·
                  refine ⟨12612848509312258946501507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134537050765997428762682741 12612848509312258946501507)
                  ·
                    refine ⟨18919272763968388419752261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12612848509312258946501507 18919272763968388419752261)
                    ·
                      refine ⟨3547363643244072828703549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18919272763968388419752261 3547363643244072828703549)
                      ·
                        rfl

theorem cell23_6908466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_6908466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908466 prefixEnd_6908466 := by exact prefixLift 6908466
  have htrace : WordTrace (prefixWord ++ tailWord_6908466) baseStart_6908466 baseEnd_6908466 := by
    simpa [prefixWord, tailWord_6908466, baseEnd_6908466] using wordTrace_append hprefix tailTrace_6908466
  have hstable : (prefixWord ++ tailWord_6908466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908466).length < 2 ^ (prefixWord ++ tailWord_6908466).sum := by decide
  have hdescent : baseEnd_6908466 < baseStart_6908466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908470 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_6908470 : Nat := 118140960795 + 6908470 * 2 ^ 59
def prefixEnd_6908470 : Nat := 4983230072969 + 3 ^ 40 * 6908470 * 2
def baseEnd_6908470 : Nat := 3547365697166690813053531

theorem tailTrace_6908470 : CollatzResearch.WordTrace tailWord_6908470 prefixEnd_6908470 3547365697166690813053531 := by
  unfold tailWord_6908470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748287580112533599165179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167981734187867025057761909 15748287580112533599165179)
  ·
    refine ⟨23622431370168800398747769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15748287580112533599165179 23622431370168800398747769)
    ·
      refine ⟨17716823527626600299060827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23622431370168800398747769 17716823527626600299060827)
      ·
        refine ⟨26575235291439900448591241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17716823527626600299060827 26575235291439900448591241)
        ·
          refine ⟨19931426468579925336443431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26575235291439900448591241 19931426468579925336443431)
          ·
            refine ⟨29897139702869888004665147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19931426468579925336443431 29897139702869888004665147)
            ·
              refine ⟨44845709554304832006997721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29897139702869888004665147 44845709554304832006997721)
              ·
                refine ⟨33634282165728624005248291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44845709554304832006997721 33634282165728624005248291)
                ·
                  refine ⟨50451423248592936007872437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33634282165728624005248291 50451423248592936007872437)
                  ·
                    refine ⟨4729820929555587750738041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50451423248592936007872437 4729820929555587750738041)
                    ·
                      refine ⟨3547365697166690813053531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729820929555587750738041 3547365697166690813053531)
                      ·
                        rfl

theorem cell23_6908470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_6908470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908470 prefixEnd_6908470 := by exact prefixLift 6908470
  have htrace : WordTrace (prefixWord ++ tailWord_6908470) baseStart_6908470 baseEnd_6908470 := by
    simpa [prefixWord, tailWord_6908470, baseEnd_6908470] using wordTrace_append hprefix tailTrace_6908470
  have hstable : (prefixWord ++ tailWord_6908470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908470).length < 2 ^ (prefixWord ++ tailWord_6908470).sum := by decide
  have hdescent : baseEnd_6908470 < baseStart_6908470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908503 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_6908503 : Nat := 118140960795 + 6908503 * 2 ^ 59
def prefixEnd_6908503 : Nat := 4983230072969 + 3 ^ 40 * 6908503 * 2
def baseEnd_6908503 : Nat := 3547382642028289183940879

theorem tailTrace_6908503 : CollatzResearch.WordTrace tailWord_6908503 prefixEnd_6908503 3547382642028289183940879 := by
  unfold tailWord_6908503
  simp only [CollatzResearch.WordTrace]
  refine ⟨251973804890680984222594163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167982536593787322815062775 251973804890680984222594163)
  ·
    refine ⟨377960707336021476333891245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251973804890680984222594163 377960707336021476333891245)
    ·
      refine ⟨141735265251008053625209217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377960707336021476333891245 141735265251008053625209217)
      ·
        refine ⟨106301448938256040218906913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141735265251008053625209217 106301448938256040218906913)
        ·
          refine ⟨79726086703692030164180185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106301448938256040218906913 79726086703692030164180185)
          ·
            refine ⟨59794565027769022623135139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79726086703692030164180185 59794565027769022623135139)
            ·
              refine ⟨89691847541653533934702709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59794565027769022623135139 89691847541653533934702709)
              ·
                refine ⟨8408610707030018806378379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89691847541653533934702709 8408610707030018806378379)
                ·
                  refine ⟨12612916060545028209567569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8408610707030018806378379 12612916060545028209567569)
                  ·
                    refine ⟨9459687045408771157175677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12612916060545028209567569 9459687045408771157175677)
                    ·
                      refine ⟨3547382642028289183940879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9459687045408771157175677 3547382642028289183940879)
                      ·
                        rfl

theorem cell23_6908503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_6908503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908503 prefixEnd_6908503 := by exact prefixLift 6908503
  have htrace : WordTrace (prefixWord ++ tailWord_6908503) baseStart_6908503 baseEnd_6908503 := by
    simpa [prefixWord, tailWord_6908503, baseEnd_6908503] using wordTrace_append hprefix tailTrace_6908503
  have hstable : (prefixWord ++ tailWord_6908503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908503).length < 2 ^ (prefixWord ++ tailWord_6908503).sum := by decide
  have hdescent : baseEnd_6908503 < baseStart_6908503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908534 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6908534 : Nat := 118140960795 + 6908534 * 2 ^ 59
def prefixEnd_6908534 : Nat := 4983230072969 + 3 ^ 40 * 6908534 * 2
def baseEnd_6908534 : Nat := 3547398559928578562653237

theorem tailTrace_6908534 : CollatzResearch.WordTrace tailWord_6908534 prefixEnd_6908534 3547398559928578562653237 := by
  unfold tailWord_6908534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748433472098042282310791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167983290369045784344648437 15748433472098042282310791)
  ·
    refine ⟨23622650208147063423466187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15748433472098042282310791 23622650208147063423466187)
    ·
      refine ⟨35433975312220595135199281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23622650208147063423466187 35433975312220595135199281)
      ·
        refine ⟨26575481484165446351399461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35433975312220595135199281 26575481484165446351399461)
        ·
          refine ⟨4982902778281021190887399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26575481484165446351399461 4982902778281021190887399)
          ·
            refine ⟨7474354167421531786331099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982902778281021190887399 7474354167421531786331099)
            ·
              refine ⟨11211531251132297679496649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7474354167421531786331099 11211531251132297679496649)
              ·
                refine ⟨8408648438349223259622487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11211531251132297679496649 8408648438349223259622487)
                ·
                  refine ⟨12612972657523834889433731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8408648438349223259622487 12612972657523834889433731)
                  ·
                    refine ⟨18919458986285752334150597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12612972657523834889433731 18919458986285752334150597)
                    ·
                      refine ⟨3547398559928578562653237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18919458986285752334150597 3547398559928578562653237)
                      ·
                        rfl

theorem cell23_6908534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6908534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908534 prefixEnd_6908534 := by exact prefixLift 6908534
  have htrace : WordTrace (prefixWord ++ tailWord_6908534) baseStart_6908534 baseEnd_6908534 := by
    simpa [prefixWord, tailWord_6908534, baseEnd_6908534] using wordTrace_append hprefix tailTrace_6908534
  have hstable : (prefixWord ++ tailWord_6908534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908534).length < 2 ^ (prefixWord ++ tailWord_6908534).sum := by decide
  have hdescent : baseEnd_6908534 < baseStart_6908534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908643 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 1, 7]
def baseStart_6908643 : Nat := 118140960795 + 6908643 * 2 ^ 59
def prefixEnd_6908643 : Nat := 4983230072969 + 3 ^ 40 * 6908643 * 2
def baseEnd_6908643 : Nat := 1182484843106639545396745

theorem tailTrace_6908643 : CollatzResearch.WordTrace tailWord_6908643 prefixEnd_6908643 1182484843106639545396745 := by
  unfold tailWord_6908643
  simp only [CollatzResearch.WordTrace]
  refine ⟨251978911110173788132690583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167985940740115858755127055 251978911110173788132690583)
  ·
    refine ⟨377968366665260682199035875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251978911110173788132690583 377968366665260682199035875)
    ·
      refine ⟨566952549997891023298553813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377968366665260682199035875 566952549997891023298553813)
      ·
        refine ⟨13287950390575570858559855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 566952549997891023298553813 13287950390575570858559855)
        ·
          refine ⟨19931925585863356287839783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13287950390575570858559855 19931925585863356287839783)
          ·
            refine ⟨29897888378795034431759675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19931925585863356287839783 29897888378795034431759675)
            ·
              refine ⟨44846832568192551647639513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29897888378795034431759675 44846832568192551647639513)
              ·
                refine ⟨33635124426144413735729635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44846832568192551647639513 33635124426144413735729635)
                ·
                  refine ⟨50452686639216620603594453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33635124426144413735729635 50452686639216620603594453)
                  ·
                    refine ⟨1182484843106639545396745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50452686639216620603594453 1182484843106639545396745)
                    ·
                      rfl

theorem cell23_6908643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 7].length) (baseStart_6908643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908643 prefixEnd_6908643 := by exact prefixLift 6908643
  have htrace : WordTrace (prefixWord ++ tailWord_6908643) baseStart_6908643 baseEnd_6908643 := by
    simpa [prefixWord, tailWord_6908643, baseEnd_6908643] using wordTrace_append hprefix tailTrace_6908643
  have hstable : (prefixWord ++ tailWord_6908643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908643).length < 2 ^ (prefixWord ++ tailWord_6908643).sum := by decide
  have hdescent : baseEnd_6908643 < baseStart_6908643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908656 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 2, 8]
def baseStart_6908656 : Nat := 118140960795 + 6908656 * 2 ^ 59
def prefixEnd_6908656 : Nat := 4983230072969 + 3 ^ 40 * 6908656 * 2
def baseEnd_6908656 : Nat := 1182487068189475695109225

theorem tailTrace_6908656 : CollatzResearch.WordTrace tailWord_6908656 prefixEnd_6908656 1182487068189475695109225 := by
  unfold tailWord_6908656
  simp only [CollatzResearch.WordTrace]
  refine ⟨125989692629563345676456911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167986256839417794235275881 125989692629563345676456911)
  ·
    refine ⟨188984538944345018514685367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125989692629563345676456911 188984538944345018514685367)
    ·
      refine ⟨283476808416517527772028051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188984538944345018514685367 283476808416517527772028051)
      ·
        refine ⟨425215212624776291658042077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283476808416517527772028051 425215212624776291658042077)
        ·
          refine ⟨159455704734291109371765779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425215212624776291658042077 159455704734291109371765779)
          ·
            refine ⟨239183557101436664057648669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159455704734291109371765779 239183557101436664057648669)
            ·
              refine ⟨89693833913038749021618251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239183557101436664057648669 89693833913038749021618251)
              ·
                refine ⟨134540750869558123532427377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89693833913038749021618251 134540750869558123532427377)
                ·
                  refine ⟨100905563152168592649320533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134540750869558123532427377 100905563152168592649320533)
                  ·
                    refine ⟨1182487068189475695109225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100905563152168592649320533 1182487068189475695109225)
                    ·
                      rfl

theorem cell23_6908656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_6908656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908656 prefixEnd_6908656 := by exact prefixLift 6908656
  have htrace : WordTrace (prefixWord ++ tailWord_6908656) baseStart_6908656 baseEnd_6908656 := by
    simpa [prefixWord, tailWord_6908656, baseEnd_6908656] using wordTrace_append hprefix tailTrace_6908656
  have hstable : (prefixWord ++ tailWord_6908656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908656).length < 2 ^ (prefixWord ++ tailWord_6908656).sum := by decide
  have hdescent : baseEnd_6908656 < baseStart_6908656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908663 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_6908663 : Nat := 118140960795 + 6908663 * 2 ^ 59
def prefixEnd_6908663 : Nat := 4983230072969 + 3 ^ 40 * 6908663 * 2
def baseEnd_6908663 : Nat := 3547464798933008557940143

theorem tailTrace_6908663 : CollatzResearch.WordTrace tailWord_6908663 prefixEnd_6908663 3547464798933008557940143 := by
  unfold tailWord_6908663
  simp only [CollatzResearch.WordTrace]
  refine ⟨251979640570101331548418643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167986427046734221032279095 251979640570101331548418643)
  ·
    refine ⟨377969460855151997322627965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251979640570101331548418643 377969460855151997322627965)
    ·
      refine ⟨141738547820681998995985487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377969460855151997322627965 141738547820681998995985487)
      ·
        refine ⟨212607821731022998493978231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141738547820681998995985487 212607821731022998493978231)
        ·
          refine ⟨318911732596534497740967347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212607821731022998493978231 318911732596534497740967347)
          ·
            refine ⟨478367598894801746611451021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318911732596534497740967347 478367598894801746611451021)
            ·
              refine ⟨179387849585550654979294133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478367598894801746611451021 179387849585550654979294133)
              ·
                refine ⟨16817610898645373904308825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179387849585550654979294133 16817610898645373904308825)
                ·
                  refine ⟨12613208173984030428231619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16817610898645373904308825 12613208173984030428231619)
                  ·
                    refine ⟨18919812260976045642347429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12613208173984030428231619 18919812260976045642347429)
                    ·
                      refine ⟨3547464798933008557940143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18919812260976045642347429 3547464798933008557940143)
                      ·
                        rfl

theorem cell23_6908663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_6908663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908663 prefixEnd_6908663 := by exact prefixLift 6908663
  have htrace : WordTrace (prefixWord ++ tailWord_6908663) baseStart_6908663 baseEnd_6908663 := by
    simpa [prefixWord, tailWord_6908663, baseEnd_6908663] using wordTrace_append hprefix tailTrace_6908663
  have hstable : (prefixWord ++ tailWord_6908663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908663).length < 2 ^ (prefixWord ++ tailWord_6908663).sum := by decide
  have hdescent : baseEnd_6908663 < baseStart_6908663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908680 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_6908680 : Nat := 118140960795 + 6908680 * 2 ^ 59
def prefixEnd_6908680 : Nat := 4983230072969 + 3 ^ 40 * 6908680 * 2
def baseEnd_6908680 : Nat := 3547473528104134991427565

theorem tailTrace_6908680 : CollatzResearch.WordTrace tailWord_6908680 prefixEnd_6908680 3547473528104134991427565 := by
  unfold tailWord_6908680
  simp only [CollatzResearch.WordTrace]
  refine ⟨125990130305519871725893747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167986840407359828967858329 125990130305519871725893747)
  ·
    refine ⟨188985195458279807588840621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125990130305519871725893747 188985195458279807588840621)
    ·
      refine ⟨70869448296854927845815233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188985195458279807588840621 70869448296854927845815233)
      ·
        refine ⟨53152086222641195884361425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70869448296854927845815233 53152086222641195884361425)
        ·
          refine ⟨39864064666980896913271069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53152086222641195884361425 39864064666980896913271069)
          ·
            refine ⟨14949024250117836342476651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39864064666980896913271069 14949024250117836342476651)
            ·
              refine ⟨22423536375176754513714977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14949024250117836342476651 22423536375176754513714977)
              ·
                refine ⟨16817652281382565885286233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22423536375176754513714977 16817652281382565885286233)
                ·
                  refine ⟨12613239211036924413964675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16817652281382565885286233 12613239211036924413964675)
                  ·
                    refine ⟨18919858816555386620947013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12613239211036924413964675 18919858816555386620947013)
                    ·
                      refine ⟨3547473528104134991427565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18919858816555386620947013 3547473528104134991427565)
                      ·
                        rfl

theorem cell23_6908680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_6908680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908680 prefixEnd_6908680 := by exact prefixLift 6908680
  have htrace : WordTrace (prefixWord ++ tailWord_6908680) baseStart_6908680 baseEnd_6908680 := by
    simpa [prefixWord, tailWord_6908680, baseEnd_6908680] using wordTrace_append hprefix tailTrace_6908680
  have hstable : (prefixWord ++ tailWord_6908680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908680).length < 2 ^ (prefixWord ++ tailWord_6908680).sum := by decide
  have hdescent : baseEnd_6908680 < baseStart_6908680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908714 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6908714 : Nat := 118140960795 + 6908714 * 2 ^ 59
def prefixEnd_6908714 : Nat := 4983230072969 + 3 ^ 40 * 6908714 * 2
def baseEnd_6908714 : Nat := 3547490986446387858402409

theorem tailTrace_6908714 : CollatzResearch.WordTrace tailWord_6908714 prefixEnd_6908714 3547490986446387858402409 := by
  unfold tailWord_6908714
  simp only [CollatzResearch.WordTrace]
  refine ⟨62995375173229141814631299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167987667128611044839016797 62995375173229141814631299)
  ·
    refine ⟨94493062759843712721946949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62995375173229141814631299 94493062759843712721946949)
    ·
      refine ⟨17717449267470696135365053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94493062759843712721946949 17717449267470696135365053)
      ·
        refine ⟨6644043475301511050761895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17717449267470696135365053 6644043475301511050761895)
        ·
          refine ⟨9966065212952266576142843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6644043475301511050761895 9966065212952266576142843)
          ·
            refine ⟨14949097819428399864214265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9966065212952266576142843 14949097819428399864214265)
            ·
              refine ⟨11211823364571299898160699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14949097819428399864214265 11211823364571299898160699)
              ·
                refine ⟨16817735046856949847241049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11211823364571299898160699 16817735046856949847241049)
                ·
                  refine ⟨12613301285142712385430787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16817735046856949847241049 12613301285142712385430787)
                  ·
                    refine ⟨18919951927714068578146181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12613301285142712385430787 18919951927714068578146181)
                    ·
                      refine ⟨3547490986446387858402409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18919951927714068578146181 3547490986446387858402409)
                      ·
                        rfl

theorem cell23_6908714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6908714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908714 prefixEnd_6908714 := by exact prefixLift 6908714
  have htrace : WordTrace (prefixWord ++ tailWord_6908714) baseStart_6908714 baseEnd_6908714 := by
    simpa [prefixWord, tailWord_6908714, baseEnd_6908714] using wordTrace_append hprefix tailTrace_6908714
  have hstable : (prefixWord ++ tailWord_6908714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908714).length < 2 ^ (prefixWord ++ tailWord_6908714).sum := by decide
  have hdescent : baseEnd_6908714 < baseStart_6908714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908764 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6908764 : Nat := 118140960795 + 6908764 * 2 ^ 59
def prefixEnd_6908764 : Nat := 4983230072969 + 3 ^ 40 * 6908764 * 2
def baseEnd_6908764 : Nat := 3547516660479112662777179

theorem tailTrace_6908764 : CollatzResearch.WordTrace tailWord_6908764 prefixEnd_6908764 3547516660479112662777179 := by
  unfold tailWord_6908764
  simp only [CollatzResearch.WordTrace]
  refine ⟨125991662171367712898922673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167988882895156950531896897 125991662171367712898922673)
  ·
    refine ⟨94493746628525784674192005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125991662171367712898922673 94493746628525784674192005)
    ·
      refine ⟨17717577492848584626411001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94493746628525784674192005 17717577492848584626411001)
      ·
        refine ⟨13288183119636438469808251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17717577492848584626411001 13288183119636438469808251)
        ·
          refine ⟨19932274679454657704712377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13288183119636438469808251 19932274679454657704712377)
          ·
            refine ⟨14949206009590993278534283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19932274679454657704712377 14949206009590993278534283)
            ·
              refine ⟨22423809014386489917801425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14949206009590993278534283 22423809014386489917801425)
              ·
                refine ⟨16817856760789867438351069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22423809014386489917801425 16817856760789867438351069)
                ·
                  refine ⟨6306696285296200289381651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16817856760789867438351069 6306696285296200289381651)
                  ·
                    refine ⟨9460044427944300434072477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6306696285296200289381651 9460044427944300434072477)
                    ·
                      refine ⟨3547516660479112662777179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9460044427944300434072477 3547516660479112662777179)
                      ·
                        rfl

theorem cell23_6908764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6908764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908764 prefixEnd_6908764 := by exact prefixLift 6908764
  have htrace : WordTrace (prefixWord ++ tailWord_6908764) baseStart_6908764 baseEnd_6908764 := by
    simpa [prefixWord, tailWord_6908764, baseEnd_6908764] using wordTrace_append hprefix tailTrace_6908764
  have hstable : (prefixWord ++ tailWord_6908764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908764).length < 2 ^ (prefixWord ++ tailWord_6908764).sum := by decide
  have hdescent : baseEnd_6908764 < baseStart_6908764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908780 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_6908780 : Nat := 118140960795 + 6908780 * 2 ^ 59
def prefixEnd_6908780 : Nat := 4983230072969 + 3 ^ 40 * 6908780 * 2
def baseEnd_6908780 : Nat := 1182508292056528200059035

theorem tailTrace_6908780 : CollatzResearch.WordTrace tailWord_6908780 prefixEnd_6908780 1182508292056528200059035 := by
  unfold tailWord_6908780
  simp only [CollatzResearch.WordTrace]
  refine ⟨125991953955338730265213897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167989271940451640353618529 125991953955338730265213897)
  ·
    refine ⟨94493965466504047698910423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125991953955338730265213897 94493965466504047698910423)
    ·
      refine ⟨141740948199756071548365635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94493965466504047698910423 141740948199756071548365635)
      ·
        refine ⟨212611422299634107322548453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141740948199756071548365635 212611422299634107322548453)
        ·
          refine ⟨39864641681181395122977835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212611422299634107322548453 39864641681181395122977835)
          ·
            refine ⟨59796962521772092684466753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39864641681181395122977835 59796962521772092684466753)
            ·
              refine ⟨44847721891329069513350065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59796962521772092684466753 44847721891329069513350065)
              ·
                refine ⟨33635791418496802135012549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44847721891329069513350065 33635791418496802135012549)
                ·
                  refine ⟨6306710890968150400314853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33635791418496802135012549 6306710890968150400314853)
                  ·
                    refine ⟨1182508292056528200059035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6306710890968150400314853 1182508292056528200059035)
                    ·
                      rfl

theorem cell23_6908780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_6908780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908780 prefixEnd_6908780 := by exact prefixLift 6908780
  have htrace : WordTrace (prefixWord ++ tailWord_6908780) baseStart_6908780 baseEnd_6908780 := by
    simpa [prefixWord, tailWord_6908780, baseEnd_6908780] using wordTrace_append hprefix tailTrace_6908780
  have hstable : (prefixWord ++ tailWord_6908780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908780).length < 2 ^ (prefixWord ++ tailWord_6908780).sum := by decide
  have hdescent : baseEnd_6908780 < baseStart_6908780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908787 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 1, 1, 4]
def baseStart_6908787 : Nat := 118140960795 + 6908787 * 2 ^ 59
def prefixEnd_6908787 : Nat := 4983230072969 + 3 ^ 40 * 6908787 * 2
def baseEnd_6908787 : Nat := 3547528470534166072789573

theorem tailTrace_6908787 : CollatzResearch.WordTrace tailWord_6908787 prefixEnd_6908787 3547528470534166072789573 := by
  unfold tailWord_6908787
  simp only [CollatzResearch.WordTrace]
  refine ⟨251984163221652100725932615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167989442147768067150621743 251984163221652100725932615)
  ·
    refine ⟨377976244832478151088898923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251984163221652100725932615 377976244832478151088898923)
    ·
      refine ⟨566964367248717226633348385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377976244832478151088898923 566964367248717226633348385)
      ·
        refine ⟨425223275436537919975011289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566964367248717226633348385 425223275436537919975011289)
        ·
          refine ⟨318917456577403439981258467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425223275436537919975011289 318917456577403439981258467)
          ·
            refine ⟨478376184866105159971887701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318917456577403439981258467 478376184866105159971887701)
            ·
              refine ⟨5605970916399669843420559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 478376184866105159971887701 5605970916399669843420559)
              ·
                refine ⟨8408956374599504765130839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5605970916399669843420559 8408956374599504765130839)
                ·
                  refine ⟨12613434561899257147696259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8408956374599504765130839 12613434561899257147696259)
                  ·
                    refine ⟨18920151842848885721544389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12613434561899257147696259 18920151842848885721544389)
                    ·
                      refine ⟨3547528470534166072789573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18920151842848885721544389 3547528470534166072789573)
                      ·
                        rfl

theorem cell23_6908787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 1, 4].length) (baseStart_6908787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908787 prefixEnd_6908787 := by exact prefixLift 6908787
  have htrace : WordTrace (prefixWord ++ tailWord_6908787) baseStart_6908787 baseEnd_6908787 := by
    simpa [prefixWord, tailWord_6908787, baseEnd_6908787] using wordTrace_append hprefix tailTrace_6908787
  have hstable : (prefixWord ++ tailWord_6908787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908787).length < 2 ^ (prefixWord ++ tailWord_6908787).sum := by decide
  have hdescent : baseEnd_6908787 < baseStart_6908787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908793 : List Nat := [1, 2, 1, 3, 2, 4, 10]
def baseStart_6908793 : Nat := 118140960795 + 6908793 * 2 ^ 59
def prefixEnd_6908793 : Nat := 4983230072969 + 3 ^ 40 * 6908793 * 2
def baseEnd_6908793 : Nat := 43796685819976457398945

theorem tailTrace_6908793 : CollatzResearch.WordTrace tailWord_6908793 prefixEnd_6908793 43796685819976457398945 := by
  unfold tailWord_6908793
  simp only [CollatzResearch.WordTrace]
  refine ⟨251984382059630363750651033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167989588039753575833767355 251984382059630363750651033)
  ·
    refine ⟨188988286544722772812988275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251984382059630363750651033 188988286544722772812988275)
    ·
      refine ⟨283482429817084159219482413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188988286544722772812988275 283482429817084159219482413)
      ·
        refine ⟨106305911181406559707305905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283482429817084159219482413 106305911181406559707305905)
        ·
          refine ⟨79729433386054919780479429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106305911181406559707305905 79729433386054919780479429)
          ·
            refine ⟨14949268759885297458839893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79729433386054919780479429 14949268759885297458839893)
            ·
              refine ⟨43796685819976457398945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14949268759885297458839893 43796685819976457398945)
              ·
                rfl

theorem cell23_6908793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 10].length) (baseStart_6908793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908793 prefixEnd_6908793 := by exact prefixLift 6908793
  have htrace : WordTrace (prefixWord ++ tailWord_6908793) baseStart_6908793 baseEnd_6908793 := by
    simpa [prefixWord, tailWord_6908793, baseEnd_6908793] using wordTrace_append hprefix tailTrace_6908793
  have hstable : (prefixWord ++ tailWord_6908793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908793).length < 2 ^ (prefixWord ++ tailWord_6908793).sum := by decide
  have hdescent : baseEnd_6908793 < baseStart_6908793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908797 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_6908797 : Nat := 118140960795 + 6908797 * 2 ^ 59
def prefixEnd_6908797 : Nat := 4983230072969 + 3 ^ 40 * 6908797 * 2
def baseEnd_6908797 : Nat := 1182511201780237011221509

theorem tailTrace_6908797 : CollatzResearch.WordTrace tailWord_6908797 prefixEnd_6908797 1182511201780237011221509 := by
  unfold tailWord_6908797
  simp only [CollatzResearch.WordTrace]
  refine ⟨251984527951615872433796645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167989685301077248289197763 251984527951615872433796645)
  ·
    refine ⟨47247098990927976081336871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251984527951615872433796645 47247098990927976081336871)
    ·
      refine ⟨70870648486391964122005307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47247098990927976081336871 70870648486391964122005307)
      ·
        refine ⟨106305972729587946183007961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70870648486391964122005307 106305972729587946183007961)
        ·
          refine ⟨79729479547190959637255971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106305972729587946183007961 79729479547190959637255971)
          ·
            refine ⟨119594219320786439455883957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79729479547190959637255971 119594219320786439455883957)
            ·
              refine ⟨11211958061323728698989121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119594219320786439455883957 11211958061323728698989121)
              ·
                refine ⟨8408968545992796524241841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11211958061323728698989121 8408968545992796524241841)
                ·
                  refine ⟨6306726409494597393181381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8408968545992796524241841 6306726409494597393181381)
                  ·
                    refine ⟨1182511201780237011221509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6306726409494597393181381 1182511201780237011221509)
                    ·
                      rfl

theorem cell23_6908797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_6908797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908797 prefixEnd_6908797 := by exact prefixLift 6908797
  have htrace : WordTrace (prefixWord ++ tailWord_6908797) baseStart_6908797 baseEnd_6908797 := by
    simpa [prefixWord, tailWord_6908797, baseEnd_6908797] using wordTrace_append hprefix tailTrace_6908797
  have hstable : (prefixWord ++ tailWord_6908797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908797).length < 2 ^ (prefixWord ++ tailWord_6908797).sum := by decide
  have hdescent : baseEnd_6908797 < baseStart_6908797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908911 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 2, 2, 2]
def baseStart_6908911 : Nat := 118140960795 + 6908911 * 2 ^ 59
def prefixEnd_6908911 : Nat := 4983230072969 + 3 ^ 40 * 6908911 * 2
def baseEnd_6908911 : Nat := 3547592142135323587639003

theorem tailTrace_6908911 : CollatzResearch.WordTrace tailWord_6908911 prefixEnd_6908911 3547592142135323587639003 := by
  unfold tailWord_6908911
  simp only [CollatzResearch.WordTrace]
  refine ⟨251988685873202869903446587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167992457248801913268964391 251988685873202869903446587)
  ·
    refine ⟨377983028809804304855169881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251988685873202869903446587 377983028809804304855169881)
    ·
      refine ⟨283487271607353228641377411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377983028809804304855169881 283487271607353228641377411)
      ·
        refine ⟨425230907411029842962066117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283487271607353228641377411 425230907411029842962066117)
        ·
          refine ⟨79730795139568095555387397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425230907411029842962066117 79730795139568095555387397)
          ·
            refine ⟨14949524088669017916635137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79730795139568095555387397 14949524088669017916635137)
            ·
              refine ⟨11212143066501763437476353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14949524088669017916635137 11212143066501763437476353)
              ·
                refine ⟨8409107299876322578107265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11212143066501763437476353 8409107299876322578107265)
                ·
                  refine ⟨6306830474907241933580449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8409107299876322578107265 6306830474907241933580449)
                  ·
                    refine ⟨4730122856180431450185337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6306830474907241933580449 4730122856180431450185337)
                    ·
                      refine ⟨3547592142135323587639003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730122856180431450185337 3547592142135323587639003)
                      ·
                        rfl

theorem cell23_6908911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 2, 2].length) (baseStart_6908911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908911 prefixEnd_6908911 := by exact prefixLift 6908911
  have htrace : WordTrace (prefixWord ++ tailWord_6908911) baseStart_6908911 baseEnd_6908911 := by
    simpa [prefixWord, tailWord_6908911, baseEnd_6908911] using wordTrace_append hprefix tailTrace_6908911
  have hstable : (prefixWord ++ tailWord_6908911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908911).length < 2 ^ (prefixWord ++ tailWord_6908911).sum := by decide
  have hdescent : baseEnd_6908911 < baseStart_6908911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6908984 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 2, 4, 2]
def baseStart_6908984 : Nat := 118140960795 + 6908984 * 2 ^ 59
def prefixEnd_6908984 : Nat := 4983230072969 + 3 ^ 40 * 6908984 * 2
def baseEnd_6908984 : Nat := 3547629626223101802026167

theorem tailTrace_6908984 : CollatzResearch.WordTrace tailWord_6908984 prefixEnd_6908984 3547629626223101802026167 := by
  unfold tailWord_6908984
  simp only [CollatzResearch.WordTrace]
  refine ⟨125995674200969201685427003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167994232267958935580569337 125995674200969201685427003)
  ·
    refine ⟨188993511301453802528140505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125995674200969201685427003 188993511301453802528140505)
    ·
      refine ⟨141745133476090351896105379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188993511301453802528140505 141745133476090351896105379)
      ·
        refine ⟨212617700214135527844158069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141745133476090351896105379 212617700214135527844158069)
        ·
          refine ⟨19932909395075205735389819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212617700214135527844158069 19932909395075205735389819)
          ·
            refine ⟨29899364092612808603084729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19932909395075205735389819 29899364092612808603084729)
            ·
              refine ⟨22424523069459606452313547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29899364092612808603084729 22424523069459606452313547)
              ·
                refine ⟨33636784604189409678470321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22424523069459606452313547 33636784604189409678470321)
                ·
                  refine ⟨25227588453142057258852741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33636784604189409678470321 25227588453142057258852741)
                  ·
                    refine ⟨4730172834964135736034889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25227588453142057258852741 4730172834964135736034889)
                    ·
                      refine ⟨3547629626223101802026167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730172834964135736034889 3547629626223101802026167)
                      ·
                        rfl

theorem cell23_6908984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_6908984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6908984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6908984 prefixEnd_6908984 := by exact prefixLift 6908984
  have htrace : WordTrace (prefixWord ++ tailWord_6908984) baseStart_6908984 baseEnd_6908984 := by
    simpa [prefixWord, tailWord_6908984, baseEnd_6908984] using wordTrace_append hprefix tailTrace_6908984
  have hstable : (prefixWord ++ tailWord_6908984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6908984).length < 2 ^ (prefixWord ++ tailWord_6908984).sum := by decide
  have hdescent : baseEnd_6908984 < baseStart_6908984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6908984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909067 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 6, 4]
def baseStart_6909067 : Nat := 118140960795 + 6909067 * 2 ^ 59
def prefixEnd_6909067 : Nat := 4983230072969 + 3 ^ 40 * 6909067 * 2
def baseEnd_6909067 : Nat := 1182557415039141659096095

theorem tailTrace_6909067 : CollatzResearch.WordTrace tailWord_6909067 prefixEnd_6909067 1182557415039141659096095 := by
  unfold tailWord_6909067
  simp only [CollatzResearch.WordTrace]
  refine ⟨251994375660637708546125455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167996250440425139030750303 251994375660637708546125455)
  ·
    refine ⟨377991563490956562819188183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251994375660637708546125455 377991563490956562819188183)
    ·
      refine ⟨566987345236434844228782275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377991563490956562819188183 566987345236434844228782275)
      ·
        refine ⟨850481017854652266343173413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566987345236434844228782275 850481017854652266343173413)
        ·
          refine ⟨159465190847747299939345015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 850481017854652266343173413 159465190847747299939345015)
          ·
            refine ⟨239197786271620949909017523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159465190847747299939345015 239197786271620949909017523)
            ·
              refine ⟨358796679407431424863526285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239197786271620949909017523 358796679407431424863526285)
              ·
                refine ⟨134548754777786784323822357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358796679407431424863526285 134548754777786784323822357)
                ·
                  refine ⟨6306972880208755515179173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134548754777786784323822357 6306972880208755515179173)
                  ·
                    refine ⟨1182557415039141659096095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6306972880208755515179173 1182557415039141659096095)
                    ·
                      rfl

theorem cell23_6909067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 4].length) (baseStart_6909067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909067 prefixEnd_6909067 := by exact prefixLift 6909067
  have htrace : WordTrace (prefixWord ++ tailWord_6909067) baseStart_6909067 baseEnd_6909067 := by
    simpa [prefixWord, tailWord_6909067, baseEnd_6909067] using wordTrace_append hprefix tailTrace_6909067
  have hstable : (prefixWord ++ tailWord_6909067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909067).length < 2 ^ (prefixWord ++ tailWord_6909067).sum := by decide
  have hdescent : baseEnd_6909067 < baseStart_6909067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909077 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_6909077 : Nat := 118140960795 + 6909077 * 2 ^ 59
def prefixEnd_6909077 : Nat := 4983230072969 + 3 ^ 40 * 6909077 * 2
def baseEnd_6909077 : Nat := 3547677379923969938163239

theorem tailTrace_6909077 : CollatzResearch.WordTrace tailWord_6909077 prefixEnd_6909077 3547677379923969938163239 := by
  unfold tailWord_6909077
  simp only [CollatzResearch.WordTrace]
  refine ⟨251994740390601480253989485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167996493593734320169326323 251994740390601480253989485)
  ·
    refine ⟨94498027646475555095246057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251994740390601480253989485 94498027646475555095246057)
    ·
      refine ⟨70873520734856666321434543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94498027646475555095246057 70873520734856666321434543)
      ·
        refine ⟨106310281102284999482151815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70873520734856666321434543 106310281102284999482151815)
        ·
          refine ⟨159465421653427499223227723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106310281102284999482151815 159465421653427499223227723)
          ·
            refine ⟨239198132480141248834841585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159465421653427499223227723 239198132480141248834841585)
            ·
              refine ⟨179398599360105936626131189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239198132480141248834841585 179398599360105936626131189)
              ·
                refine ⟨16818618690009931558699799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179398599360105936626131189 16818618690009931558699799)
                ·
                  refine ⟨25227928035014897338049699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16818618690009931558699799 25227928035014897338049699)
                  ·
                    refine ⟨37841892052522346007074549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25227928035014897338049699 37841892052522346007074549)
                    ·
                      refine ⟨3547677379923969938163239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37841892052522346007074549 3547677379923969938163239)
                      ·
                        rfl

theorem cell23_6909077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_6909077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909077 prefixEnd_6909077 := by exact prefixLift 6909077
  have htrace : WordTrace (prefixWord ++ tailWord_6909077) baseStart_6909077 baseEnd_6909077 := by
    simpa [prefixWord, tailWord_6909077, baseEnd_6909077] using wordTrace_append hprefix tailTrace_6909077
  have hstable : (prefixWord ++ tailWord_6909077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909077).length < 2 ^ (prefixWord ++ tailWord_6909077).sum := by decide
  have hdescent : baseEnd_6909077 < baseStart_6909077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909101 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_6909101 : Nat := 118140960795 + 6909101 * 2 ^ 59
def prefixEnd_6909101 : Nat := 4983230072969 + 3 ^ 40 * 6909101 * 2
def baseEnd_6909101 : Nat := 1182563234486559281421043

theorem tailTrace_6909101 : CollatzResearch.WordTrace tailWord_6909101 prefixEnd_6909101 1182563234486559281421043 := by
  unfold tailWord_6909101
  simp only [CollatzResearch.WordTrace]
  refine ⟨251995615742514532352863157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167997077161676354901908771 251995615742514532352863157)
  ·
    refine ⟨23624588975860737408080921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251995615742514532352863157 23624588975860737408080921)
    ·
      refine ⟨17718441731895553056060691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23624588975860737408080921 17718441731895553056060691)
      ·
        refine ⟨26577662597843329584091037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17718441731895553056060691 26577662597843329584091037)
        ·
          refine ⟨9966623474191248594034139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26577662597843329584091037 9966623474191248594034139)
          ·
            refine ⟨14949935211286872891051209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9966623474191248594034139 14949935211286872891051209)
            ·
              refine ⟨11212451408465154668288407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14949935211286872891051209 11212451408465154668288407)
              ·
                refine ⟨16818677112697732002432611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11212451408465154668288407 16818677112697732002432611)
                ·
                  refine ⟨25228015669046598003648917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16818677112697732002432611 25228015669046598003648917)
                  ·
                    refine ⟨1182563234486559281421043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25228015669046598003648917 1182563234486559281421043)
                    ·
                      rfl

theorem cell23_6909101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_6909101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909101 prefixEnd_6909101 := by exact prefixLift 6909101
  have htrace : WordTrace (prefixWord ++ tailWord_6909101) baseStart_6909101 baseEnd_6909101 := by
    simpa [prefixWord, tailWord_6909101, baseEnd_6909101] using wordTrace_append hprefix tailTrace_6909101
  have hstable : (prefixWord ++ tailWord_6909101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909101).length < 2 ^ (prefixWord ++ tailWord_6909101).sum := by decide
  have hdescent : baseEnd_6909101 < baseStart_6909101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909121 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6909121 : Nat := 118140960795 + 6909121 * 2 ^ 59
def prefixEnd_6909121 : Nat := 4983230072969 + 3 ^ 40 * 6909121 * 2
def baseEnd_6909121 : Nat := 3547699973072767766013037

theorem tailTrace_6909121 : CollatzResearch.WordTrace tailWord_6909121 prefixEnd_6909121 3547699973072767766013037 := by
  unfold tailWord_6909121
  simp only [CollatzResearch.WordTrace]
  refine ⟨251996345202442075768591217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167997563468294717179060811 251996345202442075768591217)
  ·
    refine ⟨188997258901831556826443413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251996345202442075768591217 188997258901831556826443413)
    ·
      refine ⟨8859246511023354226239535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188997258901831556826443413 8859246511023354226239535)
      ·
        refine ⟨13288869766535031339359303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8859246511023354226239535 13288869766535031339359303)
        ·
          refine ⟨19933304649802547009038955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13288869766535031339359303 19933304649802547009038955)
          ·
            refine ⟨29899956974703820513558433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19933304649802547009038955 29899956974703820513558433)
            ·
              refine ⟨22424967731027865385168825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29899956974703820513558433 22424967731027865385168825)
              ·
                refine ⟨16818725798270899038876619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22424967731027865385168825 16818725798270899038876619)
                ·
                  refine ⟨25228088697406348558314929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16818725798270899038876619 25228088697406348558314929)
                  ·
                    refine ⟨18921066523054761418736197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25228088697406348558314929 18921066523054761418736197)
                    ·
                      refine ⟨3547699973072767766013037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18921066523054761418736197 3547699973072767766013037)
                      ·
                        rfl

theorem cell23_6909121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6909121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909121 prefixEnd_6909121 := by exact prefixLift 6909121
  have htrace : WordTrace (prefixWord ++ tailWord_6909121) baseStart_6909121 baseEnd_6909121 := by
    simpa [prefixWord, tailWord_6909121, baseEnd_6909121] using wordTrace_append hprefix tailTrace_6909121
  have hstable : (prefixWord ++ tailWord_6909121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909121).length < 2 ^ (prefixWord ++ tailWord_6909121).sum := by decide
  have hdescent : baseEnd_6909121 < baseStart_6909121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909122 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6909122 : Nat := 118140960795 + 6909122 * 2 ^ 59
def prefixEnd_6909122 : Nat := 4983230072969 + 3 ^ 40 * 6909122 * 2
def baseEnd_6909122 : Nat := 1182566828851140754033511

theorem tailTrace_6909122 : CollatzResearch.WordTrace tailWord_6909122 prefixEnd_6909122 1182566828851140754033511 := by
  unfold tailWord_6909122
  simp only [CollatzResearch.WordTrace]
  refine ⟨62999095418859613234844405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167997587783625635292918413 62999095418859613234844405)
  ·
    refine ⟨5906165195518088740766663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62999095418859613234844405 5906165195518088740766663)
    ·
      refine ⟨8859247793277133111149995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5906165195518088740766663 8859247793277133111149995)
      ·
        refine ⟨13288871689915699666724993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8859247793277133111149995 13288871689915699666724993)
        ·
          refine ⟨9966653767436774750043745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13288871689915699666724993 9966653767436774750043745)
          ·
            refine ⟨7474990325577581062532809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9966653767436774750043745 7474990325577581062532809)
            ·
              refine ⟨5606242744183185796899607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7474990325577581062532809 5606242744183185796899607)
              ·
                refine ⟨8409364116274778695349411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606242744183185796899607 8409364116274778695349411)
                ·
                  refine ⟨12614046174412168043024117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8409364116274778695349411 12614046174412168043024117)
                  ·
                    refine ⟨1182566828851140754033511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12614046174412168043024117 1182566828851140754033511)
                    ·
                      rfl

theorem cell23_6909122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6909122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909122 prefixEnd_6909122 := by exact prefixLift 6909122
  have htrace : WordTrace (prefixWord ++ tailWord_6909122) baseStart_6909122 baseEnd_6909122 := by
    simpa [prefixWord, tailWord_6909122, baseEnd_6909122] using wordTrace_append hprefix tailTrace_6909122
  have hstable : (prefixWord ++ tailWord_6909122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909122).length < 2 ^ (prefixWord ++ tailWord_6909122).sum := by decide
  have hdescent : baseEnd_6909122 < baseStart_6909122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909142 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6909142 : Nat := 118140960795 + 6909142 * 2 ^ 59
def prefixEnd_6909142 : Nat := 4983230072969 + 3 ^ 40 * 6909142 * 2
def baseEnd_6909142 : Nat := 3547710756166512183850441

theorem tailTrace_6909142 : CollatzResearch.WordTrace tailWord_6909142 prefixEnd_6909142 3547710756166512183850441 := by
  unfold tailWord_6909142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15749819445960374772194105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167998074090243997570070453 15749819445960374772194105)
  ·
    refine ⟨11812364584470281079145579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15749819445960374772194105 11812364584470281079145579)
    ·
      refine ⟨17718546876705421618718369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11812364584470281079145579 17718546876705421618718369)
      ·
        refine ⟨13288910157529066214038777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17718546876705421618718369 13288910157529066214038777)
        ·
          refine ⟨9966682618146799660529083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13288910157529066214038777 9966682618146799660529083)
          ·
            refine ⟨14950023927220199490793625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9966682618146799660529083 14950023927220199490793625)
            ·
              refine ⟨11212517945415149618095219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14950023927220199490793625 11212517945415149618095219)
              ·
                refine ⟨16818776918122724427142829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11212517945415149618095219 16818776918122724427142829)
                ·
                  refine ⟨6307041344296021660178561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16818776918122724427142829 6307041344296021660178561)
                  ·
                    refine ⟨4730281008222016245133921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6307041344296021660178561 4730281008222016245133921)
                    ·
                      refine ⟨3547710756166512183850441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730281008222016245133921 3547710756166512183850441)
                      ·
                        rfl

theorem cell23_6909142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6909142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909142 prefixEnd_6909142 := by exact prefixLift 6909142
  have htrace : WordTrace (prefixWord ++ tailWord_6909142) baseStart_6909142 baseEnd_6909142 := by
    simpa [prefixWord, tailWord_6909142, baseEnd_6909142] using wordTrace_append hprefix tailTrace_6909142
  have hstable : (prefixWord ++ tailWord_6909142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909142).length < 2 ^ (prefixWord ++ tailWord_6909142).sum := by decide
  have hdescent : baseEnd_6909142 < baseStart_6909142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909198 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_6909198 : Nat := 118140960795 + 6909198 * 2 ^ 59
def prefixEnd_6909198 : Nat := 4983230072969 + 3 ^ 40 * 6909198 * 2
def baseEnd_6909198 : Nat := 3547739511083163964750183

theorem tailTrace_6909198 : CollatzResearch.WordTrace tailWord_6909198 prefixEnd_6909198 3547739511083163964750183 := by
  unfold tailWord_6909198
  simp only [CollatzResearch.WordTrace]
  refine ⟨31499894202895389739893031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167999435748775411946096165 31499894202895389739893031)
  ·
    refine ⟨47249841304343084609839547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31499894202895389739893031 47249841304343084609839547)
    ·
      refine ⟨70874761956514626914759321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47249841304343084609839547 70874761956514626914759321)
      ·
        refine ⟨53156071467385970186069491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70874761956514626914759321 53156071467385970186069491)
        ·
          refine ⟨79734107201078955279104237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53156071467385970186069491 79734107201078955279104237)
          ·
            refine ⟨29900290200404608229664089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79734107201078955279104237 29900290200404608229664089)
            ·
              refine ⟨22425217650303456172248067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29900290200404608229664089 22425217650303456172248067)
              ·
                refine ⟨33637826475455184258372101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22425217650303456172248067 33637826475455184258372101)
                ·
                  refine ⟨6307092464147847048444769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33637826475455184258372101 6307092464147847048444769)
                  ·
                    refine ⟨4730319348110885286333577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6307092464147847048444769 4730319348110885286333577)
                    ·
                      refine ⟨3547739511083163964750183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730319348110885286333577 3547739511083163964750183)
                      ·
                        rfl

theorem cell23_6909198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_6909198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909198 prefixEnd_6909198 := by exact prefixLift 6909198
  have htrace : WordTrace (prefixWord ++ tailWord_6909198) baseStart_6909198 baseEnd_6909198 := by
    simpa [prefixWord, tailWord_6909198, baseEnd_6909198] using wordTrace_append hprefix tailTrace_6909198
  have hstable : (prefixWord ++ tailWord_6909198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909198).length < 2 ^ (prefixWord ++ tailWord_6909198).sum := by decide
  have hdescent : baseEnd_6909198 < baseStart_6909198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909215 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 2, 2, 2]
def baseStart_6909215 : Nat := 118140960795 + 6909215 * 2 ^ 59
def prefixEnd_6909215 : Nat := 4983230072969 + 3 ^ 40 * 6909215 * 2
def baseEnd_6909215 : Nat := 3547748240254290398237605

theorem tailTrace_6909215 : CollatzResearch.WordTrace tailWord_6909215 prefixEnd_6909215 3547748240254290398237605 := by
  unfold tailWord_6909215
  simp only [CollatzResearch.WordTrace]
  refine ⟨251999773664101529822513099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167999849109401019881675399 251999773664101529822513099)
  ·
    refine ⟨377999660496152294733769649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251999773664101529822513099 377999660496152294733769649)
    ·
      refine ⟨283499745372114221050327237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377999660496152294733769649 283499745372114221050327237)
      ·
        refine ⟨53156202257271416446936357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283499745372114221050327237 53156202257271416446936357)
        ·
          refine ⟨9966787923238390583800567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53156202257271416446936357 9966787923238390583800567)
          ·
            refine ⟨14950181884857585875700851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9966787923238390583800567 14950181884857585875700851)
            ·
              refine ⟨22425272827286378813551277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14950181884857585875700851 22425272827286378813551277)
              ·
                refine ⟨8409477310232392055081729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22425272827286378813551277 8409477310232392055081729)
                ·
                  refine ⟨6307107982674294041311297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8409477310232392055081729 6307107982674294041311297)
                  ·
                    refine ⟨4730330987005720530983473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6307107982674294041311297 4730330987005720530983473)
                    ·
                      refine ⟨3547748240254290398237605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730330987005720530983473 3547748240254290398237605)
                      ·
                        rfl

theorem cell23_6909215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_6909215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909215 prefixEnd_6909215 := by exact prefixLift 6909215
  have htrace : WordTrace (prefixWord ++ tailWord_6909215) baseStart_6909215 baseEnd_6909215 := by
    simpa [prefixWord, tailWord_6909215, baseEnd_6909215] using wordTrace_append hprefix tailTrace_6909215
  have hstable : (prefixWord ++ tailWord_6909215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909215).length < 2 ^ (prefixWord ++ tailWord_6909215).sum := by decide
  have hdescent : baseEnd_6909215 < baseStart_6909215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909227 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5]
def baseStart_6909227 : Nat := 118140960795 + 6909227 * 2 ^ 59
def prefixEnd_6909227 : Nat := 4983230072969 + 3 ^ 40 * 6909227 * 2
def baseEnd_6909227 : Nat := 3547754402022144351287549

theorem tailTrace_6909227 : CollatzResearch.WordTrace tailWord_6909227 prefixEnd_6909227 3547754402022144351287549 := by
  unfold tailWord_6909227
  simp only [CollatzResearch.WordTrace]
  refine ⟨252000211340058055871949935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168000140893372037247966623 252000211340058055871949935)
  ·
    refine ⟨378000317010087083807924903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252000211340058055871949935 378000317010087083807924903)
    ·
      refine ⟨567000475515130625711887355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378000317010087083807924903 567000475515130625711887355)
      ·
        refine ⟨850500713272695938567831033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567000475515130625711887355 850500713272695938567831033)
        ·
          refine ⟨637875534954521953925873275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850500713272695938567831033 637875534954521953925873275)
          ·
            refine ⟨956813302431782930888809913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637875534954521953925873275 956813302431782930888809913)
            ·
              refine ⟨717609976823837198166607435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956813302431782930888809913 717609976823837198166607435)
              ·
                refine ⟨1076414965235755797249911153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717609976823837198166607435 1076414965235755797249911153)
                ·
                  refine ⟨807311223926816847937433365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1076414965235755797249911153 807311223926816847937433365)
                  ·
                    refine ⟨37842713621569539747067189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 807311223926816847937433365 37842713621569539747067189)
                    ·
                      refine ⟨3547754402022144351287549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37842713621569539747067189 3547754402022144351287549)
                      ·
                        rfl

theorem cell23_6909227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_6909227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909227 prefixEnd_6909227 := by exact prefixLift 6909227
  have htrace : WordTrace (prefixWord ++ tailWord_6909227) baseStart_6909227 baseEnd_6909227 := by
    simpa [prefixWord, tailWord_6909227, baseEnd_6909227] using wordTrace_append hprefix tailTrace_6909227
  have hstable : (prefixWord ++ tailWord_6909227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909227).length < 2 ^ (prefixWord ++ tailWord_6909227).sum := by decide
  have hdescent : baseEnd_6909227 < baseStart_6909227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909244 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_6909244 : Nat := 118140960795 + 6909244 * 2 ^ 59
def prefixEnd_6909244 : Nat := 4983230072969 + 3 ^ 40 * 6909244 * 2
def baseEnd_6909244 : Nat := 3547763131193270784774971

theorem tailTrace_6909244 : CollatzResearch.WordTrace tailWord_6909244 prefixEnd_6909244 3547763131193270784774971 := by
  unfold tailWord_6909244
  simp only [CollatzResearch.WordTrace]
  refine ⟨126000415690498233887659393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168000554253997645183545857 126000415690498233887659393)
  ·
    refine ⟨94500311767873675415744545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126000415690498233887659393 94500311767873675415744545)
    ·
      refine ⟨70875233825905256561808409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94500311767873675415744545 70875233825905256561808409)
      ·
        refine ⟨53156425369428942421356307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70875233825905256561808409 53156425369428942421356307)
        ·
          refine ⟨79734638054143413632034461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53156425369428942421356307 79734638054143413632034461)
          ·
            refine ⟨29900489270303780112012923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79734638054143413632034461 29900489270303780112012923)
            ·
              refine ⟨44850733905455670168019385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29900489270303780112012923 44850733905455670168019385)
              ·
                refine ⟨33638050429091752626014539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44850733905455670168019385 33638050429091752626014539)
                ·
                  refine ⟨50457075643637628939021809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33638050429091752626014539 50457075643637628939021809)
                  ·
                    refine ⟨37842806732728221704266357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50457075643637628939021809 37842806732728221704266357)
                    ·
                      refine ⟨3547763131193270784774971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37842806732728221704266357 3547763131193270784774971)
                      ·
                        rfl

theorem cell23_6909244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_6909244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909244 prefixEnd_6909244 := by exact prefixLift 6909244
  have htrace : WordTrace (prefixWord ++ tailWord_6909244) baseStart_6909244 baseEnd_6909244 := by
    simpa [prefixWord, tailWord_6909244, baseEnd_6909244] using wordTrace_append hprefix tailTrace_6909244
  have hstable : (prefixWord ++ tailWord_6909244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909244).length < 2 ^ (prefixWord ++ tailWord_6909244).sum := by decide
  have hdescent : baseEnd_6909244 < baseStart_6909244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909271 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 1, 6, 2]
def baseStart_6909271 : Nat := 118140960795 + 6909271 * 2 ^ 59
def prefixEnd_6909271 : Nat := 4983230072969 + 3 ^ 40 * 6909271 * 2
def baseEnd_6909271 : Nat := 3547776995170942179137347

theorem tailTrace_6909271 : CollatzResearch.WordTrace tailWord_6909271 prefixEnd_6909271 3547776995170942179137347 := by
  unfold tailWord_6909271
  simp only [CollatzResearch.WordTrace]
  refine ⟨252001816151898651386551667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168001210767932434257701111 252001816151898651386551667)
  ·
    refine ⟨378002724227847977079827501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252001816151898651386551667 378002724227847977079827501)
    ·
      refine ⟨141751021585442991404935313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378002724227847977079827501 141751021585442991404935313)
      ·
        refine ⟨106313266189082243553701485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141751021585442991404935313 106313266189082243553701485)
        ·
          refine ⟨39867474820905841332638057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106313266189082243553701485 39867474820905841332638057)
          ·
            refine ⟨29900606115679380999478543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39867474820905841332638057 29900606115679380999478543)
            ·
              refine ⟨44850909173519071499217815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29900606115679380999478543 44850909173519071499217815)
              ·
                refine ⟨67276363760278607248826723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44850909173519071499217815 67276363760278607248826723)
                ·
                  refine ⟨100914545640417910873240085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67276363760278607248826723 100914545640417910873240085)
                  ·
                    refine ⟨4730369326894589572183129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100914545640417910873240085 4730369326894589572183129)
                    ·
                      refine ⟨3547776995170942179137347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730369326894589572183129 3547776995170942179137347)
                      ·
                        rfl

theorem cell23_6909271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_6909271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909271 prefixEnd_6909271 := by exact prefixLift 6909271
  have htrace : WordTrace (prefixWord ++ tailWord_6909271) baseStart_6909271 baseEnd_6909271 := by
    simpa [prefixWord, tailWord_6909271, baseEnd_6909271] using wordTrace_append hprefix tailTrace_6909271
  have hstable : (prefixWord ++ tailWord_6909271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909271).length < 2 ^ (prefixWord ++ tailWord_6909271).sum := by decide
  have hdescent : baseEnd_6909271 < baseStart_6909271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909304 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_6909304 : Nat := 118140960795 + 6909304 * 2 ^ 59
def prefixEnd_6909304 : Nat := 4983230072969 + 3 ^ 40 * 6909304 * 2
def baseEnd_6909304 : Nat := 3547793940032540550024695

theorem tailTrace_6909304 : CollatzResearch.WordTrace tailWord_6909304 prefixEnd_6909304 3547793940032540550024695 := by
  unfold tailWord_6909304
  simp only [CollatzResearch.WordTrace]
  refine ⟨126001509880389549011251483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168002013173852732015001977 126001509880389549011251483)
  ·
    refine ⟨189002264820584323516877225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126001509880389549011251483 189002264820584323516877225)
    ·
      refine ⟨141751698615438242637657919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189002264820584323516877225 141751698615438242637657919)
      ·
        refine ⟨212627547923157363956486879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141751698615438242637657919 212627547923157363956486879)
        ·
          refine ⟨318941321884736045934730319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212627547923157363956486879 318941321884736045934730319)
          ·
            refine ⟨478411982827104068902095479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318941321884736045934730319 478411982827104068902095479)
            ·
              refine ⟨717617974240656103353143219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478411982827104068902095479 717617974240656103353143219)
              ·
                refine ⟨1076426961360984155029714829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717617974240656103353143219 1076426961360984155029714829)
                ·
                  refine ⟨403660110510369058136143061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076426961360984155029714829 403660110510369058136143061)
                  ·
                    refine ⟨9460783840086774800065853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 403660110510369058136143061 9460783840086774800065853)
                    ·
                      refine ⟨3547793940032540550024695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9460783840086774800065853 3547793940032540550024695)
                      ·
                        rfl

theorem cell23_6909304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_6909304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909304 prefixEnd_6909304 := by exact prefixLift 6909304
  have htrace : WordTrace (prefixWord ++ tailWord_6909304) baseStart_6909304 baseEnd_6909304 := by
    simpa [prefixWord, tailWord_6909304, baseEnd_6909304] using wordTrace_append hprefix tailTrace_6909304
  have hstable : (prefixWord ++ tailWord_6909304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909304).length < 2 ^ (prefixWord ++ tailWord_6909304).sum := by decide
  have hdescent : baseEnd_6909304 < baseStart_6909304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909338 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_6909338 : Nat := 118140960795 + 6909338 * 2 ^ 59
def prefixEnd_6909338 : Nat := 4983230072969 + 3 ^ 40 * 6909338 * 2
def baseEnd_6909338 : Nat := 3547811398374793416999539

theorem tailTrace_6909338 : CollatzResearch.WordTrace tailWord_6909338 prefixEnd_6909338 3547811398374793416999539 := by
  unfold tailWord_6909338
  simp only [CollatzResearch.WordTrace]
  refine ⟨63001064960663980457310167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168002839895103947886160445 63001064960663980457310167)
  ·
    refine ⟨94501597440995970685965251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63001064960663980457310167 94501597440995970685965251)
    ·
      refine ⟨141752396161493956028947877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94501597440995970685965251 141752396161493956028947877)
      ·
        refine ⟨26578574280280116755427727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141752396161493956028947877 26578574280280116755427727)
        ·
          refine ⟨39867861420420175133141591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26578574280280116755427727 39867861420420175133141591)
          ·
            refine ⟨59801792130630262699712387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39867861420420175133141591 59801792130630262699712387)
            ·
              refine ⟨89702688195945394049568581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59801792130630262699712387 89702688195945394049568581)
              ·
                refine ⟨16819254036739761384294109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89702688195945394049568581 16819254036739761384294109)
                ·
                  refine ⟨6307220263777410519110291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16819254036739761384294109 6307220263777410519110291)
                  ·
                    refine ⟨9460830395666115778665437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6307220263777410519110291 9460830395666115778665437)
                    ·
                      refine ⟨3547811398374793416999539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9460830395666115778665437 3547811398374793416999539)
                      ·
                        rfl

theorem cell23_6909338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_6909338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909338 prefixEnd_6909338 := by exact prefixLift 6909338
  have htrace : WordTrace (prefixWord ++ tailWord_6909338) baseStart_6909338 baseEnd_6909338 := by
    simpa [prefixWord, tailWord_6909338, baseEnd_6909338] using wordTrace_append hprefix tailTrace_6909338
  have hstable : (prefixWord ++ tailWord_6909338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909338).length < 2 ^ (prefixWord ++ tailWord_6909338).sum := by decide
  have hdescent : baseEnd_6909338 < baseStart_6909338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909348 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_6909348 : Nat := 118140960795 + 6909348 * 2 ^ 59
def prefixEnd_6909348 : Nat := 4983230072969 + 3 ^ 40 * 6909348 * 2
def baseEnd_6909348 : Nat := 3547816533181338377874493

theorem tailTrace_6909348 : CollatzResearch.WordTrace tailWord_6909348 prefixEnd_6909348 3547816533181338377874493 := by
  unfold tailWord_6909348
  simp only [CollatzResearch.WordTrace]
  refine ⟨126002312286309846768552349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168003083048413129024736465 126002312286309846768552349)
  ·
    refine ⟨47250867107366192538207131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126002312286309846768552349 47250867107366192538207131)
    ·
      refine ⟨70876300661049288807310697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47250867107366192538207131 70876300661049288807310697)
      ·
        refine ⟨53157225495786966605483023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70876300661049288807310697 53157225495786966605483023)
        ·
          refine ⟨79735838243680449908224535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53157225495786966605483023 79735838243680449908224535)
          ·
            refine ⟨119603757365520674862336803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79735838243680449908224535 119603757365520674862336803)
            ·
              refine ⟨179405636048281012293505205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119603757365520674862336803 179405636048281012293505205)
              ·
                refine ⟨16819278379526344902516113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179405636048281012293505205 16819278379526344902516113)
                ·
                  refine ⟨12614458784644758676887085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16819278379526344902516113 12614458784644758676887085)
                  ·
                    refine ⟨4730422044241784503832657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12614458784644758676887085 4730422044241784503832657)
                    ·
                      refine ⟨3547816533181338377874493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730422044241784503832657 3547816533181338377874493)
                      ·
                        rfl

theorem cell23_6909348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_6909348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909348 prefixEnd_6909348 := by exact prefixLift 6909348
  have htrace : WordTrace (prefixWord ++ tailWord_6909348) baseStart_6909348 baseEnd_6909348 := by
    simpa [prefixWord, tailWord_6909348, baseEnd_6909348] using wordTrace_append hprefix tailTrace_6909348
  have hstable : (prefixWord ++ tailWord_6909348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909348).length < 2 ^ (prefixWord ++ tailWord_6909348).sum := by decide
  have hdescent : baseEnd_6909348 < baseStart_6909348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909365 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_6909365 : Nat := 118140960795 + 6909365 * 2 ^ 59
def prefixEnd_6909365 : Nat := 4983230072969 + 3 ^ 40 * 6909365 * 2
def baseEnd_6909365 : Nat := 3547825262352464811361915

theorem tailTrace_6909365 : CollatzResearch.WordTrace tailWord_6909365 prefixEnd_6909365 3547825262352464811361915 := by
  unfold tailWord_6909365
  simp only [CollatzResearch.WordTrace]
  refine ⟨252005244613558105440473549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168003496409038736960315699 252005244613558105440473549)
  ·
    refine ⟨94501966730084289540177581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252005244613558105440473549 94501966730084289540177581)
    ·
      refine ⟨35438237523781608577566593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94501966730084289540177581 35438237523781608577566593)
      ·
        refine ⟨26578678142836206433174945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35438237523781608577566593 26578678142836206433174945)
        ·
          refine ⟨19934008607127154824881209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26578678142836206433174945 19934008607127154824881209)
          ·
            refine ⟨14950506455345366118660907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19934008607127154824881209 14950506455345366118660907)
            ·
              refine ⟨22425759683018049177991361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14950506455345366118660907 22425759683018049177991361)
              ·
                refine ⟨16819319762263536883493521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22425759683018049177991361 16819319762263536883493521)
                ·
                  refine ⟨12614489821697652662620141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16819319762263536883493521 12614489821697652662620141)
                  ·
                    refine ⟨4730433683136619748482553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12614489821697652662620141 4730433683136619748482553)
                    ·
                      refine ⟨3547825262352464811361915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730433683136619748482553 3547825262352464811361915)
                      ·
                        rfl

theorem cell23_6909365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_6909365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909365 prefixEnd_6909365 := by exact prefixLift 6909365
  have htrace : WordTrace (prefixWord ++ tailWord_6909365) baseStart_6909365 baseEnd_6909365 := by
    simpa [prefixWord, tailWord_6909365, baseEnd_6909365] using wordTrace_append hprefix tailTrace_6909365
  have hstable : (prefixWord ++ tailWord_6909365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909365).length < 2 ^ (prefixWord ++ tailWord_6909365).sum := by decide
  have hdescent : baseEnd_6909365 < baseStart_6909365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909372 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6909372 : Nat := 118140960795 + 6909372 * 2 ^ 59
def prefixEnd_6909372 : Nat := 4983230072969 + 3 ^ 40 * 6909372 * 2
def baseEnd_6909372 : Nat := 3547828856717046283974383

theorem tailTrace_6909372 : CollatzResearch.WordTrace tailWord_6909372 prefixEnd_6909372 3547828856717046283974383 := by
  unfold tailWord_6909372
  simp only [CollatzResearch.WordTrace]
  refine ⟨126002749962266372817989185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168003666616355163757318913 126002749962266372817989185)
  ·
    refine ⟨94502062471699779613491889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126002749962266372817989185 94502062471699779613491889)
    ·
      refine ⟨70876546853774834710118917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94502062471699779613491889 70876546853774834710118917)
      ·
        refine ⟨13289352535082781508147297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70876546853774834710118917 13289352535082781508147297)
        ·
          refine ⟨9967014401312086131110473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13289352535082781508147297 9967014401312086131110473)
          ·
            refine ⟨7475260800984064598332855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9967014401312086131110473 7475260800984064598332855)
            ·
              refine ⟨11212891201476096897499283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475260800984064598332855 11212891201476096897499283)
              ·
                refine ⟨16819336802214145346248925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11212891201476096897499283 16819336802214145346248925)
                ·
                  refine ⟨6307251300830304504843347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16819336802214145346248925 6307251300830304504843347)
                  ·
                    refine ⟨9460876951245456757265021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6307251300830304504843347 9460876951245456757265021)
                    ·
                      refine ⟨3547828856717046283974383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9460876951245456757265021 3547828856717046283974383)
                      ·
                        rfl

theorem cell23_6909372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6909372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909372 prefixEnd_6909372 := by exact prefixLift 6909372
  have htrace : WordTrace (prefixWord ++ tailWord_6909372) baseStart_6909372 baseEnd_6909372 := by
    simpa [prefixWord, tailWord_6909372, baseEnd_6909372] using wordTrace_append hprefix tailTrace_6909372
  have hstable : (prefixWord ++ tailWord_6909372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909372).length < 2 ^ (prefixWord ++ tailWord_6909372).sum := by decide
  have hdescent : baseEnd_6909372 < baseStart_6909372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909471 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_6909471 : Nat := 118140960795 + 6909471 * 2 ^ 59
def prefixEnd_6909471 : Nat := 4983230072969 + 3 ^ 40 * 6909471 * 2
def baseEnd_6909471 : Nat := 3547879691301841396636427

theorem tailTrace_6909471 : CollatzResearch.WordTrace tailWord_6909471 prefixEnd_6909471 3547879691301841396636427 := by
  unfold tailWord_6909471
  simp only [CollatzResearch.WordTrace]
  refine ⟨252009110751174085543832267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168006073834116057029221511 252009110751174085543832267)
  ·
    refine ⟨378013666126761128315748401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252009110751174085543832267 378013666126761128315748401)
    ·
      refine ⟨283510249595070846236811301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378013666126761128315748401 283510249595070846236811301)
      ·
        refine ⟨53158171799075783669402119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283510249595070846236811301 53158171799075783669402119)
        ·
          refine ⟨79737257698613675504103179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53158171799075783669402119 79737257698613675504103179)
          ·
            refine ⟨119605886547920513256154769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79737257698613675504103179 119605886547920513256154769)
            ·
              refine ⟨89704414910940384942116077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119605886547920513256154769 89704414910940384942116077)
              ·
                refine ⟨33639155591602644353293529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89704414910940384942116077 33639155591602644353293529)
                ·
                  refine ⟨25229366693701983264970147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33639155591602644353293529 25229366693701983264970147)
                  ·
                    refine ⟨37844050040552974897455221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25229366693701983264970147 37844050040552974897455221)
                    ·
                      refine ⟨3547879691301841396636427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37844050040552974897455221 3547879691301841396636427)
                      ·
                        rfl

theorem cell23_6909471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_6909471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909471 prefixEnd_6909471 := by exact prefixLift 6909471
  have htrace : WordTrace (prefixWord ++ tailWord_6909471) baseStart_6909471 baseEnd_6909471 := by
    simpa [prefixWord, tailWord_6909471, baseEnd_6909471] using wordTrace_append hprefix tailTrace_6909471
  have hstable : (prefixWord ++ tailWord_6909471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909471).length < 2 ^ (prefixWord ++ tailWord_6909471).sum := by decide
  have hdescent : baseEnd_6909471 < baseStart_6909471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909472 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6909472 : Nat := 118140960795 + 6909472 * 2 ^ 59
def prefixEnd_6909472 : Nat := 4983230072969 + 3 ^ 40 * 6909472 * 2
def baseEnd_6909472 : Nat := 3547880204782495892723923

theorem tailTrace_6909472 : CollatzResearch.WordTrace tailWord_6909472 prefixEnd_6909472 3547880204782495892723923 := by
  unfold tailWord_6909472
  simp only [CollatzResearch.WordTrace]
  refine ⟨126004573612085231357309335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168006098149446975143079113 126004573612085231357309335)
  ·
    refine ⟨189006860418127847035964003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126004573612085231357309335 189006860418127847035964003)
    ·
      refine ⟨283510290627191770553946005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189006860418127847035964003 283510290627191770553946005)
      ·
        refine ⟨13289544873149614244716219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 283510290627191770553946005 13289544873149614244716219)
        ·
          refine ⟨19934317309724421367074329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13289544873149614244716219 19934317309724421367074329)
          ·
            refine ⟨14950737982293316025305747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19934317309724421367074329 14950737982293316025305747)
            ·
              refine ⟨22426106973439974037958621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14950737982293316025305747 22426106973439974037958621)
              ·
                refine ⟨8409790115039990264234483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22426106973439974037958621 8409790115039990264234483)
                ·
                  refine ⟨12614685172559985396351725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8409790115039990264234483 12614685172559985396351725)
                  ·
                    refine ⟨4730506939709994523631897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12614685172559985396351725 4730506939709994523631897)
                    ·
                      refine ⟨3547880204782495892723923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730506939709994523631897 3547880204782495892723923)
                      ·
                        rfl

theorem cell23_6909472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6909472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909472 prefixEnd_6909472 := by exact prefixLift 6909472
  have htrace : WordTrace (prefixWord ++ tailWord_6909472) baseStart_6909472 baseEnd_6909472 := by
    simpa [prefixWord, tailWord_6909472, baseEnd_6909472] using wordTrace_append hprefix tailTrace_6909472
  have hstable : (prefixWord ++ tailWord_6909472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909472).length < 2 ^ (prefixWord ++ tailWord_6909472).sum := by decide
  have hdescent : baseEnd_6909472 < baseStart_6909472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909491 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 7]
def baseStart_6909491 : Nat := 118140960795 + 6909491 * 2 ^ 59
def prefixEnd_6909491 : Nat := 4983230072969 + 3 ^ 40 * 6909491 * 2
def baseEnd_6909491 : Nat := 394209995657214590931815

theorem tailTrace_6909491 : CollatzResearch.WordTrace tailWord_6909491 prefixEnd_6909491 394209995657214590931815 := by
  unfold tailWord_6909491
  simp only [CollatzResearch.WordTrace]
  refine ⟨252009840211101628959560327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168006560140734419306373551 252009840211101628959560327)
  ·
    refine ⟨378014760316652443439340491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252009840211101628959560327 378014760316652443439340491)
    ·
      refine ⟨567022140474978665159010737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378014760316652443439340491 567022140474978665159010737)
      ·
        refine ⟨425266605356233998869258053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567022140474978665159010737 425266605356233998869258053)
        ·
          refine ⟨79737488504293874787985885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425266605356233998869258053 79737488504293874787985885)
          ·
            refine ⟨29901558189110203045494707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79737488504293874787985885 29901558189110203045494707)
            ·
              refine ⟨44852337283665304568242061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29901558189110203045494707 44852337283665304568242061)
              ·
                refine ⟨16819626481374489213090773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44852337283665304568242061 16819626481374489213090773)
                ·
                  refine ⟨394209995657214590931815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16819626481374489213090773 394209995657214590931815)
                  ·
                    rfl

theorem cell23_6909491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 7].length) (baseStart_6909491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909491 prefixEnd_6909491 := by exact prefixLift 6909491
  have htrace : WordTrace (prefixWord ++ tailWord_6909491) baseStart_6909491 baseEnd_6909491 := by
    simpa [prefixWord, tailWord_6909491, baseEnd_6909491] using wordTrace_append hprefix tailTrace_6909491
  have hstable : (prefixWord ++ tailWord_6909491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909491).length < 2 ^ (prefixWord ++ tailWord_6909491).sum := by decide
  have hdescent : baseEnd_6909491 < baseStart_6909491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909521 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 1, 7]
def baseStart_6909521 : Nat := 118140960795 + 6909521 * 2 ^ 59
def prefixEnd_6909521 : Nat := 4983230072969 + 3 ^ 40 * 6909521 * 2
def baseEnd_6909521 : Nat := 1182635121778188733670399

theorem tailTrace_6909521 : CollatzResearch.WordTrace tailWord_6909521 prefixEnd_6909521 1182635121778188733670399 := by
  unfold tailWord_6909521
  simp only [CollatzResearch.WordTrace]
  refine ⟨252010934400992944083152417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168007289600661962722101611 252010934400992944083152417)
  ·
    refine ⟨189008200800744708062364313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252010934400992944083152417 189008200800744708062364313)
    ·
      refine ⟨141756150600558531046773235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189008200800744708062364313 141756150600558531046773235)
      ·
        refine ⟨212634225900837796570159853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141756150600558531046773235 212634225900837796570159853)
        ·
          refine ⟨79737834712814173713809945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212634225900837796570159853 79737834712814173713809945)
          ·
            refine ⟨59803376034610630285357459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79737834712814173713809945 59803376034610630285357459)
            ·
              refine ⟨89705064051915945428036189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59803376034610630285357459 89705064051915945428036189)
              ·
                refine ⟨33639399019468479535513571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89705064051915945428036189 33639399019468479535513571)
                ·
                  refine ⟨50459098529202719303270357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33639399019468479535513571 50459098529202719303270357)
                  ·
                    refine ⟨1182635121778188733670399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50459098529202719303270357 1182635121778188733670399)
                    ·
                      rfl

theorem cell23_6909521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_6909521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909521 prefixEnd_6909521 := by exact prefixLift 6909521
  have htrace : WordTrace (prefixWord ++ tailWord_6909521) baseStart_6909521 baseEnd_6909521 := by
    simpa [prefixWord, tailWord_6909521, baseEnd_6909521] using wordTrace_append hprefix tailTrace_6909521
  have hstable : (prefixWord ++ tailWord_6909521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909521).length < 2 ^ (prefixWord ++ tailWord_6909521).sum := by decide
  have hdescent : baseEnd_6909521 < baseStart_6909521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909528 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 7, 2]
def baseStart_6909528 : Nat := 118140960795 + 6909528 * 2 ^ 59
def prefixEnd_6909528 : Nat := 4983230072969 + 3 ^ 40 * 6909528 * 2
def baseEnd_6909528 : Nat := 3547908959699147673623665

theorem tailTrace_6909528 : CollatzResearch.WordTrace tailWord_6909528 prefixEnd_6909528 3547908959699147673623665 := by
  unfold tailWord_6909528
  simp only [CollatzResearch.WordTrace]
  refine ⟨126005594855983792139328619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168007459807978389519104825 126005594855983792139328619)
  ·
    refine ⟨189008392283975688208992929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126005594855983792139328619 189008392283975688208992929)
    ·
      refine ⟨141756294212981766156744697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189008392283975688208992929 141756294212981766156744697)
      ·
        refine ⟨106317220659736324617558523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141756294212981766156744697 106317220659736324617558523)
        ·
          refine ⟨159475830989604486926337785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106317220659736324617558523 159475830989604486926337785)
          ·
            refine ⟨119606873242203365194753339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159475830989604486926337785 119606873242203365194753339)
            ·
              refine ⟨179410309863305047792130009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119606873242203365194753339 179410309863305047792130009)
              ·
                refine ⟨134557732397478785844097507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179410309863305047792130009 134557732397478785844097507)
                ·
                  refine ⟨201836598596218178766146261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134557732397478785844097507 201836598596218178766146261)
                  ·
                    refine ⟨4730545279598863564831553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 201836598596218178766146261 4730545279598863564831553)
                    ·
                      refine ⟨3547908959699147673623665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730545279598863564831553 3547908959699147673623665)
                      ·
                        rfl

theorem cell23_6909528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_6909528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909528 prefixEnd_6909528 := by exact prefixLift 6909528
  have htrace : WordTrace (prefixWord ++ tailWord_6909528) baseStart_6909528 baseEnd_6909528 := by
    simpa [prefixWord, tailWord_6909528, baseEnd_6909528] using wordTrace_append hprefix tailTrace_6909528
  have hstable : (prefixWord ++ tailWord_6909528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909528).length < 2 ^ (prefixWord ++ tailWord_6909528).sum := by decide
  have hdescent : baseEnd_6909528 < baseStart_6909528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909568 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 5, 4]
def baseStart_6909568 : Nat := 118140960795 + 6909568 * 2 ^ 59
def prefixEnd_6909568 : Nat := 4983230072969 + 3 ^ 40 * 6909568 * 2
def baseEnd_6909568 : Nat := 1182643166308442505707827

theorem tailTrace_6909568 : CollatzResearch.WordTrace tailWord_6909568 prefixEnd_6909568 1182643166308442505707827 := by
  unfold tailWord_6909568
  simp only [CollatzResearch.WordTrace]
  refine ⟨126006324315911335555056679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168008432421215114073408905 126006324315911335555056679)
  ·
    refine ⟨189009486473867003332585019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126006324315911335555056679 189009486473867003332585019)
    ·
      refine ⟨283514229710800504998877529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189009486473867003332585019 283514229710800504998877529)
      ·
        refine ⟨212635672283100378749158147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283514229710800504998877529 212635672283100378749158147)
        ·
          refine ⟨318953508424650568123737221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212635672283100378749158147 318953508424650568123737221)
          ·
            refine ⟨59803782829621981523200729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318953508424650568123737221 59803782829621981523200729)
            ·
              refine ⟨44852837122216486142400547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59803782829621981523200729 44852837122216486142400547)
              ·
                refine ⟨67279255683324729213600821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44852837122216486142400547 67279255683324729213600821)
                ·
                  refine ⟨6307430220311693363775077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67279255683324729213600821 6307430220311693363775077)
                  ·
                    refine ⟨1182643166308442505707827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6307430220311693363775077 1182643166308442505707827)
                    ·
                      rfl

theorem cell23_6909568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_6909568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909568 prefixEnd_6909568 := by exact prefixLift 6909568
  have htrace : WordTrace (prefixWord ++ tailWord_6909568) baseStart_6909568 baseEnd_6909568 := by
    simpa [prefixWord, tailWord_6909568, baseEnd_6909568] using wordTrace_append hprefix tailTrace_6909568
  have hstable : (prefixWord ++ tailWord_6909568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909568).length < 2 ^ (prefixWord ++ tailWord_6909568).sum := by decide
  have hdescent : baseEnd_6909568 < baseStart_6909568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909571 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6]
def baseStart_6909571 : Nat := 118140960795 + 6909571 * 2 ^ 59
def prefixEnd_6909571 : Nat := 4983230072969 + 3 ^ 40 * 6909571 * 2
def baseEnd_6909571 : Nat := 3547931039367291005385967

theorem tailTrace_6909571 : CollatzResearch.WordTrace tailWord_6909571 prefixEnd_6909571 3547931039367291005385967 := by
  unfold tailWord_6909571
  simp only [CollatzResearch.WordTrace]
  refine ⟨252012758050811802622472567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168008505367207868414981711 252012758050811802622472567)
  ·
    refine ⟨378019137076217703933708851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252012758050811802622472567 378019137076217703933708851)
    ·
      refine ⟨567028705614326555900563277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378019137076217703933708851 567028705614326555900563277)
      ·
        refine ⟨212635764605372458462711229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567028705614326555900563277 212635764605372458462711229)
        ·
          refine ⟨79738411727014671923516711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212635764605372458462711229 79738411727014671923516711)
          ·
            refine ⟨119607617590522007885275067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79738411727014671923516711 119607617590522007885275067)
            ·
              refine ⟨179411426385783011827912601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119607617590522007885275067 179411426385783011827912601)
              ·
                refine ⟨134558569789337258870934451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179411426385783011827912601 134558569789337258870934451)
                ·
                  refine ⟨201837854684005888306401677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134558569789337258870934451 201837854684005888306401677)
                  ·
                    refine ⟨75689195506502208114900629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201837854684005888306401677 75689195506502208114900629)
                    ·
                      refine ⟨3547931039367291005385967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75689195506502208114900629 3547931039367291005385967)
                      ·
                        rfl

theorem cell23_6909571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_6909571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909571 prefixEnd_6909571 := by exact prefixLift 6909571
  have htrace : WordTrace (prefixWord ++ tailWord_6909571) baseStart_6909571 baseEnd_6909571 := by
    simpa [prefixWord, tailWord_6909571, baseEnd_6909571] using wordTrace_append hprefix tailTrace_6909571
  have hstable : (prefixWord ++ tailWord_6909571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909571).length < 2 ^ (prefixWord ++ tailWord_6909571).sum := by decide
  have hdescent : baseEnd_6909571 < baseStart_6909571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909575 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_6909575 : Nat := 118140960795 + 6909575 * 2 ^ 59
def prefixEnd_6909575 : Nat := 4983230072969 + 3 ^ 40 * 6909575 * 2
def baseEnd_6909575 : Nat := 3547933093289908989735949

theorem tailTrace_6909575 : CollatzResearch.WordTrace tailWord_6909575 prefixEnd_6909575 3547933093289908989735949 := by
  unfold tailWord_6909575
  simp only [CollatzResearch.WordTrace]
  refine ⟨252012903942797311305618179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168008602628531540870412119 252012903942797311305618179)
  ·
    refine ⟨378019355914195966958427269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252012903942797311305618179 378019355914195966958427269)
    ·
      refine ⟨70878629233911743804705113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378019355914195966958427269 70878629233911743804705113)
      ·
        refine ⟨53158971925433807853528835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70878629233911743804705113 53158971925433807853528835)
        ·
          refine ⟨79738457888150711780293253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53158971925433807853528835 79738457888150711780293253)
          ·
            refine ⟨14950960854028258458804985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79738457888150711780293253 14950960854028258458804985)
            ·
              refine ⟨11213220640521193844103739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14950960854028258458804985 11213220640521193844103739)
              ·
                refine ⟨16819830960781790766155609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11213220640521193844103739 16819830960781790766155609)
                ·
                  refine ⟨12614873220586343074616707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16819830960781790766155609 12614873220586343074616707)
                  ·
                    refine ⟨18922309830879514611925061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12614873220586343074616707 18922309830879514611925061)
                    ·
                      refine ⟨3547933093289908989735949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18922309830879514611925061 3547933093289908989735949)
                      ·
                        rfl

theorem cell23_6909575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_6909575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909575 prefixEnd_6909575 := by exact prefixLift 6909575
  have htrace : WordTrace (prefixWord ++ tailWord_6909575) baseStart_6909575 baseEnd_6909575 := by
    simpa [prefixWord, tailWord_6909575, baseEnd_6909575] using wordTrace_append hprefix tailTrace_6909575
  have hstable : (prefixWord ++ tailWord_6909575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909575).length < 2 ^ (prefixWord ++ tailWord_6909575).sum := by decide
  have hdescent : baseEnd_6909575 < baseStart_6909575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909625 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 3]
def baseStart_6909625 : Nat := 118140960795 + 6909625 * 2 ^ 59
def prefixEnd_6909625 : Nat := 4983230072969 + 3 ^ 40 * 6909625 * 2
def baseEnd_6909625 : Nat := 3547958767322633794110719

theorem tailTrace_6909625 : CollatzResearch.WordTrace tailWord_6909625 prefixEnd_6909625 3547958767322633794110719 := by
  unfold tailWord_6909625
  simp only [CollatzResearch.WordTrace]
  refine ⟨252014727592616169844938329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168009818395077446563292219 252014727592616169844938329)
  ·
    refine ⟨189011045694462127383703747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252014727592616169844938329 189011045694462127383703747)
    ·
      refine ⟨283516568541693191075555621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189011045694462127383703747 283516568541693191075555621)
      ·
        refine ⟨53159356601567473326666679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283516568541693191075555621 53159356601567473326666679)
        ·
          refine ⟨79739034902351209990000019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53159356601567473326666679 79739034902351209990000019)
          ·
            refine ⟨119608552353526814985000029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79739034902351209990000019 119608552353526814985000029)
            ·
              refine ⟨44853207132572555619375011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119608552353526814985000029 44853207132572555619375011)
              ·
                refine ⟨67279810698858833429062517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44853207132572555619375011 67279810698858833429062517)
                ·
                  refine ⟨6307482253018015633974611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67279810698858833429062517 6307482253018015633974611)
                  ·
                    refine ⟨9461223379527023450961917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6307482253018015633974611 9461223379527023450961917)
                    ·
                      refine ⟨3547958767322633794110719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9461223379527023450961917 3547958767322633794110719)
                      ·
                        rfl

theorem cell23_6909625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_6909625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909625 prefixEnd_6909625 := by exact prefixLift 6909625
  have htrace : WordTrace (prefixWord ++ tailWord_6909625) baseStart_6909625 baseEnd_6909625 := by
    simpa [prefixWord, tailWord_6909625, baseEnd_6909625] using wordTrace_append hprefix tailTrace_6909625
  have hstable : (prefixWord ++ tailWord_6909625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909625).length < 2 ^ (prefixWord ++ tailWord_6909625).sum := by decide
  have hdescent : baseEnd_6909625 < baseStart_6909625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909648 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_6909648 : Nat := 118140960795 + 6909648 * 2 ^ 59
def prefixEnd_6909648 : Nat := 4983230072969 + 3 ^ 40 * 6909648 * 2
def baseEnd_6909648 : Nat := 3547970577377687204123113

theorem tailTrace_6909648 : CollatzResearch.WordTrace tailWord_6909648 prefixEnd_6909648 3547970577377687204123113 := by
  unfold tailWord_6909648
  simp only [CollatzResearch.WordTrace]
  refine ⟨126007783235766422386512799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168010377647688563182017065 126007783235766422386512799)
  ·
    refine ⟨189011674853649633579769199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126007783235766422386512799 189011674853649633579769199)
    ·
      refine ⟨283517512280474450369653799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189011674853649633579769199 283517512280474450369653799)
      ·
        refine ⟨425276268420711675554480699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283517512280474450369653799 425276268420711675554480699)
        ·
          refine ⟨637914402631067513331721049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425276268420711675554480699 637914402631067513331721049)
          ·
            refine ⟨478435801973300634998790787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637914402631067513331721049 478435801973300634998790787)
            ·
              refine ⟨717653702959950952498186181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478435801973300634998790787 717653702959950952498186181)
              ·
                refine ⟨134560069304990803593409909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717653702959950952498186181 134560069304990803593409909)
                ·
                  refine ⟨12615006497342887836882179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134560069304990803593409909 12615006497342887836882179)
                  ·
                    refine ⟨18922509746014331755323269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12615006497342887836882179 18922509746014331755323269)
                    ·
                      refine ⟨3547970577377687204123113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18922509746014331755323269 3547970577377687204123113)
                      ·
                        rfl

theorem cell23_6909648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_6909648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909648 prefixEnd_6909648 := by exact prefixLift 6909648
  have htrace : WordTrace (prefixWord ++ tailWord_6909648) baseStart_6909648 baseEnd_6909648 := by
    simpa [prefixWord, tailWord_6909648, baseEnd_6909648] using wordTrace_append hprefix tailTrace_6909648
  have hstable : (prefixWord ++ tailWord_6909648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909648).length < 2 ^ (prefixWord ++ tailWord_6909648).sum := by decide
  have hdescent : baseEnd_6909648 < baseStart_6909648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909675 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 2, 4]
def baseStart_6909675 : Nat := 118140960795 + 6909675 * 2 ^ 59
def prefixEnd_6909675 : Nat := 4983230072969 + 3 ^ 40 * 6909675 * 2
def baseEnd_6909675 : Nat := 1182661480451786199495163

theorem tailTrace_6909675 : CollatzResearch.WordTrace tailWord_6909675 prefixEnd_6909675 1182661480451786199495163 := by
  unfold tailWord_6909675
  simp only [CollatzResearch.WordTrace]
  refine ⟨252016551242435028384258479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168011034161623352256172319 252016551242435028384258479)
  ·
    refine ⟨378024826863652542576387719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252016551242435028384258479 378024826863652542576387719)
    ·
      refine ⟨567037240295478813864581579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378024826863652542576387719 567037240295478813864581579)
      ·
        refine ⟨850555860443218220796872369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567037240295478813864581579 850555860443218220796872369)
        ·
          refine ⟨637916895332413665597654277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850555860443218220796872369 637916895332413665597654277)
          ·
            refine ⟨119609417874827562299560177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 637916895332413665597654277 119609417874827562299560177)
            ·
              refine ⟨89707063406120671724670133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119609417874827562299560177 89707063406120671724670133)
              ·
                refine ⟨8410037194323812974187825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89707063406120671724670133 8410037194323812974187825)
                ·
                  refine ⟨6307527895742859730640869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8410037194323812974187825 6307527895742859730640869)
                  ·
                    refine ⟨1182661480451786199495163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6307527895742859730640869 1182661480451786199495163)
                    ·
                      rfl

theorem cell23_6909675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 4].length) (baseStart_6909675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909675 prefixEnd_6909675 := by exact prefixLift 6909675
  have htrace : WordTrace (prefixWord ++ tailWord_6909675) baseStart_6909675 baseEnd_6909675 := by
    simpa [prefixWord, tailWord_6909675, baseEnd_6909675] using wordTrace_append hprefix tailTrace_6909675
  have hstable : (prefixWord ++ tailWord_6909675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909675).length < 2 ^ (prefixWord ++ tailWord_6909675).sum := by decide
  have hdescent : baseEnd_6909675 < baseStart_6909675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909682 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_6909682 : Nat := 118140960795 + 6909682 * 2 ^ 59
def prefixEnd_6909682 : Nat := 4983230072969 + 3 ^ 40 * 6909682 * 2
def baseEnd_6909682 : Nat := 3547988035719940071097957

theorem tailTrace_6909682 : CollatzResearch.WordTrace tailWord_6909682 prefixEnd_6909682 3547988035719940071097957 := by
  unfold tailWord_6909682
  simp only [CollatzResearch.WordTrace]
  refine ⟨63004201638352417144940825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168011204368939779053175533 63004201638352417144940825)
  ·
    refine ⟨47253151228764312858705619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63004201638352417144940825 47253151228764312858705619)
    ·
      refine ⟨70879726843146469288058429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47253151228764312858705619 70879726843146469288058429)
      ·
        refine ⟨26579897566179925983021911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70879726843146469288058429 26579897566179925983021911)
        ·
          refine ⟨39869846349269888974532867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26579897566179925983021911 39869846349269888974532867)
          ·
            refine ⟨59804769523904833461799301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39869846349269888974532867 59804769523904833461799301)
            ·
              refine ⟨11213394285732156274087369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59804769523904833461799301 11213394285732156274087369)
              ·
                refine ⟨8410045714299117205565527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11213394285732156274087369 8410045714299117205565527)
                ·
                  refine ⟨12615068571448675808348291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410045714299117205565527 12615068571448675808348291)
                  ·
                    refine ⟨18922602857173013712522437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12615068571448675808348291 18922602857173013712522437)
                    ·
                      refine ⟨3547988035719940071097957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18922602857173013712522437 3547988035719940071097957)
                      ·
                        rfl

theorem cell23_6909682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_6909682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909682 prefixEnd_6909682 := by exact prefixLift 6909682
  have htrace : WordTrace (prefixWord ++ tailWord_6909682) baseStart_6909682 baseEnd_6909682 := by
    simpa [prefixWord, tailWord_6909682, baseEnd_6909682] using wordTrace_append hprefix tailTrace_6909682
  have hstable : (prefixWord ++ tailWord_6909682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909682).length < 2 ^ (prefixWord ++ tailWord_6909682).sum := by decide
  have hdescent : baseEnd_6909682 < baseStart_6909682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909785 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_6909785 : Nat := 118140960795 + 6909785 * 2 ^ 59
def prefixEnd_6909785 : Nat := 4983230072969 + 3 ^ 40 * 6909785 * 2
def baseEnd_6909785 : Nat := 3548040924227353168109983

theorem tailTrace_6909785 : CollatzResearch.WordTrace tailWord_6909785 prefixEnd_6909785 3548040924227353168109983 := by
  unfold tailWord_6909785
  simp only [CollatzResearch.WordTrace]
  refine ⟨252020563272036517170762809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168013708848024344780508539 252020563272036517170762809)
  ·
    refine ⟨189015422454027387878072107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252020563272036517170762809 189015422454027387878072107)
    ·
      refine ⟨283523133681041081817108161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189015422454027387878072107 283523133681041081817108161)
      ·
        refine ⟨212642350260780811362831121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283523133681041081817108161 212642350260780811362831121)
        ·
          refine ⟨159481762695585608522123341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212642350260780811362831121 159481762695585608522123341)
          ·
            refine ⟨59805661010844603195796253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159481762695585608522123341 59805661010844603195796253)
            ·
              refine ⟨22427122879066726198423595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59805661010844603195796253 22427122879066726198423595)
              ·
                refine ⟨33640684318600089297635393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22427122879066726198423595 33640684318600089297635393)
                ·
                  refine ⟨25230513238950066973226545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33640684318600089297635393 25230513238950066973226545)
                  ·
                    refine ⟨18922884929212550229919909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25230513238950066973226545 18922884929212550229919909)
                    ·
                      refine ⟨3548040924227353168109983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18922884929212550229919909 3548040924227353168109983)
                      ·
                        rfl

theorem cell23_6909785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_6909785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909785 prefixEnd_6909785 := by exact prefixLift 6909785
  have htrace : WordTrace (prefixWord ++ tailWord_6909785) baseStart_6909785 baseEnd_6909785 := by
    simpa [prefixWord, tailWord_6909785, baseEnd_6909785] using wordTrace_append hprefix tailTrace_6909785
  have hstable : (prefixWord ++ tailWord_6909785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909785).length < 2 ^ (prefixWord ++ tailWord_6909785).sum := by decide
  have hdescent : baseEnd_6909785 < baseStart_6909785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909842 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_6909842 : Nat := 118140960795 + 6909842 * 2 ^ 59
def prefixEnd_6909842 : Nat := 4983230072969 + 3 ^ 40 * 6909842 * 2
def baseEnd_6909842 : Nat := 1182690064208219815032407

theorem tailTrace_6909842 : CollatzResearch.WordTrace tailWord_6909842 prefixEnd_6909842 1182690064208219815032407 := by
  unfold tailWord_6909842
  simp only [CollatzResearch.WordTrace]
  refine ⟨63005660558207503976396945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168015094821886677270391853 63005660558207503976396945)
  ·
    refine ⟨47254245418655627982297709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63005660558207503976396945 47254245418655627982297709)
    ·
      refine ⟨17720342031995860493361641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47254245418655627982297709 17720342031995860493361641)
      ·
        refine ⟨13290256523996895370021231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17720342031995860493361641 13290256523996895370021231)
        ·
          refine ⟨19935384785995343055031847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13290256523996895370021231 19935384785995343055031847)
          ·
            refine ⟨29903077178993014582547771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19935384785995343055031847 29903077178993014582547771)
            ·
              refine ⟨44854615768489521873821657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29903077178993014582547771 44854615768489521873821657)
              ·
                refine ⟨33640961826367141405366243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44854615768489521873821657 33640961826367141405366243)
                ·
                  refine ⟨50461442739550712108049365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33640961826367141405366243 50461442739550712108049365)
                  ·
                    refine ⟨1182690064208219815032407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50461442739550712108049365 1182690064208219815032407)
                    ·
                      rfl

theorem cell23_6909842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_6909842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909842 prefixEnd_6909842 := by exact prefixLift 6909842
  have htrace : WordTrace (prefixWord ++ tailWord_6909842) baseStart_6909842 baseEnd_6909842 := by
    simpa [prefixWord, tailWord_6909842, baseEnd_6909842] using wordTrace_append hprefix tailTrace_6909842
  have hstable : (prefixWord ++ tailWord_6909842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909842).length < 2 ^ (prefixWord ++ tailWord_6909842).sum := by decide
  have hdescent : baseEnd_6909842 < baseStart_6909842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909845 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_6909845 : Nat := 118140960795 + 6909845 * 2 ^ 59
def prefixEnd_6909845 : Nat := 4983230072969 + 3 ^ 40 * 6909845 * 2
def baseEnd_6909845 : Nat := 3548071733066622933359707

theorem tailTrace_6909845 : CollatzResearch.WordTrace tailWord_6909845 prefixEnd_6909845 3548071733066622933359707 := by
  unfold tailWord_6909845
  simp only [CollatzResearch.WordTrace]
  refine ⟨252022751651819147417946989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168015167767879431611964659 252022751651819147417946989)
  ·
    refine ⟨94508531869432180281730121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252022751651819147417946989 94508531869432180281730121)
    ·
      refine ⟨70881398902074135211297591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94508531869432180281730121 70881398902074135211297591)
      ·
        refine ⟨106322098353111202816946387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70881398902074135211297591 106322098353111202816946387)
        ·
          refine ⟨159483147529666804225419581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106322098353111202816946387 159483147529666804225419581)
          ·
            refine ⟨59806180323625051584532343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159483147529666804225419581 59806180323625051584532343)
            ·
              refine ⟨89709270485437577376798515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59806180323625051584532343 89709270485437577376798515)
              ·
                refine ⟨134563905728156366065197773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89709270485437577376798515 134563905728156366065197773)
                ·
                  refine ⟨50461464648058637274449165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134563905728156366065197773 50461464648058637274449165)
                  ·
                    refine ⟨18923049243021988977918437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50461464648058637274449165 18923049243021988977918437)
                    ·
                      refine ⟨3548071733066622933359707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18923049243021988977918437 3548071733066622933359707)
                      ·
                        rfl

theorem cell23_6909845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_6909845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909845 prefixEnd_6909845 := by exact prefixLift 6909845
  have htrace : WordTrace (prefixWord ++ tailWord_6909845) baseStart_6909845 baseEnd_6909845 := by
    simpa [prefixWord, tailWord_6909845, baseEnd_6909845] using wordTrace_append hprefix tailTrace_6909845
  have hstable : (prefixWord ++ tailWord_6909845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909845).length < 2 ^ (prefixWord ++ tailWord_6909845).sum := by decide
  have hdescent : baseEnd_6909845 < baseStart_6909845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909876 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_6909876 : Nat := 118140960795 + 6909876 * 2 ^ 59
def prefixEnd_6909876 : Nat := 4983230072969 + 3 ^ 40 * 6909876 * 2
def baseEnd_6909876 : Nat := 1182695883655637437357355

theorem tailTrace_6909876 : CollatzResearch.WordTrace tailWord_6909876 prefixEnd_6909876 1182695883655637437357355 := by
  unfold tailWord_6909876
  simp only [CollatzResearch.WordTrace]
  refine ⟨126011941157353419856162741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168015921543137893141550321 126011941157353419856162741)
  ·
    refine ⟨11813619483501883111515257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126011941157353419856162741 11813619483501883111515257)
    ·
      refine ⟨8860214612626412333636443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11813619483501883111515257 8860214612626412333636443)
      ·
        refine ⟨13290321918939618500454665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8860214612626412333636443 13290321918939618500454665)
        ·
          refine ⟨9967741439204713875340999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13290321918939618500454665 9967741439204713875340999)
          ·
            refine ⟨14951612158807070813011499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9967741439204713875340999 14951612158807070813011499)
            ·
              refine ⟨22427418238210606219517249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14951612158807070813011499 22427418238210606219517249)
              ·
                refine ⟨16820563678657954664637937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22427418238210606219517249 16820563678657954664637937)
                ·
                  refine ⟨12615422758993465998478453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16820563678657954664637937 12615422758993465998478453)
                  ·
                    refine ⟨1182695883655637437357355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12615422758993465998478453 1182695883655637437357355)
                    ·
                      rfl

theorem cell23_6909876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_6909876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909876 prefixEnd_6909876 := by exact prefixLift 6909876
  have htrace : WordTrace (prefixWord ++ tailWord_6909876) baseStart_6909876 baseEnd_6909876 := by
    simpa [prefixWord, tailWord_6909876, baseEnd_6909876] using wordTrace_append hprefix tailTrace_6909876
  have hstable : (prefixWord ++ tailWord_6909876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909876).length < 2 ^ (prefixWord ++ tailWord_6909876).sum := by decide
  have hdescent : baseEnd_6909876 < baseStart_6909876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909902 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_6909902 : Nat := 118140960795 + 6909902 * 2 ^ 59
def prefixEnd_6909902 : Nat := 4983230072969 + 3 ^ 40 * 6909902 * 2
def baseEnd_6909902 : Nat := 394233444607103245594105

theorem tailTrace_6909902 : CollatzResearch.WordTrace tailWord_6909902 prefixEnd_6909902 394233444607103245594105 := by
  unfold tailWord_6909902
  simp only [CollatzResearch.WordTrace]
  refine ⟨31503103826576580769096495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168016553741741764101847973 31503103826576580769096495)
  ·
    refine ⟨47254655739864871153644743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31503103826576580769096495 47254655739864871153644743)
    ·
      refine ⟨70881983609797306730467115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47254655739864871153644743 70881983609797306730467115)
      ·
        refine ⟨106322975414695960095700673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70881983609797306730467115 106322975414695960095700673)
        ·
          refine ⟨79742231561021970071775505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106322975414695960095700673 79742231561021970071775505)
          ·
            refine ⟨59806673670766477553831629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79742231561021970071775505 59806673670766477553831629)
            ·
              refine ⟨22427502626537429082686861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59806673670766477553831629 22427502626537429082686861)
              ·
                refine ⟨8410313484951535906007573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22427502626537429082686861 8410313484951535906007573)
                ·
                  refine ⟨394233444607103245594105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8410313484951535906007573 394233444607103245594105)
                  ·
                    rfl

theorem cell23_6909902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_6909902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909902 prefixEnd_6909902 := by exact prefixLift 6909902
  have htrace : WordTrace (prefixWord ++ tailWord_6909902) baseStart_6909902 baseEnd_6909902 := by
    simpa [prefixWord, tailWord_6909902, baseEnd_6909902] using wordTrace_append hprefix tailTrace_6909902
  have hstable : (prefixWord ++ tailWord_6909902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909902).length < 2 ^ (prefixWord ++ tailWord_6909902).sum := by decide
  have hdescent : baseEnd_6909902 < baseStart_6909902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909932 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_6909932 : Nat := 118140960795 + 6909932 * 2 ^ 59
def prefixEnd_6909932 : Nat := 4983230072969 + 3 ^ 40 * 6909932 * 2
def baseEnd_6909932 : Nat := 1182705468627854697657269

theorem tailTrace_6909932 : CollatzResearch.WordTrace tailWord_6909932 prefixEnd_6909932 1182705468627854697657269 := by
  unfold tailWord_6909932
  simp only [CollatzResearch.WordTrace]
  refine ⟨126012962401251980638182025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168017283201669307517576033 126012962401251980638182025)
  ·
    refine ⟨94509721800938985478636519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126012962401251980638182025 94509721800938985478636519)
    ·
      refine ⟨141764582701408478217954779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94509721800938985478636519 141764582701408478217954779)
      ·
        refine ⟨212646874052112717326932169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141764582701408478217954779 212646874052112717326932169)
        ·
          refine ⟨159485155539084537995199127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212646874052112717326932169 159485155539084537995199127)
          ·
            refine ⟨239227733308626806992798691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159485155539084537995199127 239227733308626806992798691)
            ·
              refine ⟨358841599962940210489198037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239227733308626806992798691 358841599962940210489198037)
              ·
                refine ⟨8410349999131411183340579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 358841599962940210489198037 8410349999131411183340579)
                ·
                  refine ⟨12615524998697116775010869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410349999131411183340579 12615524998697116775010869)
                  ·
                    refine ⟨1182705468627854697657269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12615524998697116775010869 1182705468627854697657269)
                    ·
                      rfl

theorem cell23_6909932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_6909932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909932 prefixEnd_6909932 := by exact prefixLift 6909932
  have htrace : WordTrace (prefixWord ++ tailWord_6909932) baseStart_6909932 baseEnd_6909932 := by
    simpa [prefixWord, tailWord_6909932, baseEnd_6909932] using wordTrace_append hprefix tailTrace_6909932
  have hstable : (prefixWord ++ tailWord_6909932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909932).length < 2 ^ (prefixWord ++ tailWord_6909932).sum := by decide
  have hdescent : baseEnd_6909932 < baseStart_6909932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909973 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_6909973 : Nat := 118140960795 + 6909973 * 2 ^ 59
def prefixEnd_6909973 : Nat := 4983230072969 + 3 ^ 40 * 6909973 * 2
def baseEnd_6909973 : Nat := 3548137458590398432559119

theorem tailTrace_6909973 : CollatzResearch.WordTrace tailWord_6909973 prefixEnd_6909973 3548137458590398432559119 := by
  unfold tailWord_6909973
  simp only [CollatzResearch.WordTrace]
  refine ⟨252027420195355425278606573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168018280130236950185737715 252027420195355425278606573)
  ·
    refine ⟨94510282573258284479477465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252027420195355425278606573 94510282573258284479477465)
    ·
      refine ⟨70882711929943713359608099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94510282573258284479477465 70882711929943713359608099)
      ·
        refine ⟨106324067894915570039412149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70882711929943713359608099 106324067894915570039412149)
        ·
          refine ⟨9967881365148334691194889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106324067894915570039412149 9967881365148334691194889)
          ·
            refine ⟨7475911023861251018396167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9967881365148334691194889 7475911023861251018396167)
            ·
              refine ⟨11213866535791876527594251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475911023861251018396167 11213866535791876527594251)
              ·
                refine ⟨16820799803687814791391377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11213866535791876527594251 16820799803687814791391377)
                ·
                  refine ⟨12615599852765861093543533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16820799803687814791391377 12615599852765861093543533)
                  ·
                    refine ⟨4730849944787197910078825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12615599852765861093543533 4730849944787197910078825)
                    ·
                      refine ⟨3548137458590398432559119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730849944787197910078825 3548137458590398432559119)
                      ·
                        rfl

theorem cell23_6909973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_6909973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909973 prefixEnd_6909973 := by exact prefixLift 6909973
  have htrace : WordTrace (prefixWord ++ tailWord_6909973) baseStart_6909973 baseEnd_6909973 := by
    simpa [prefixWord, tailWord_6909973, baseEnd_6909973] using wordTrace_append hprefix tailTrace_6909973
  have hstable : (prefixWord ++ tailWord_6909973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909973).length < 2 ^ (prefixWord ++ tailWord_6909973).sum := by decide
  have hdescent : baseEnd_6909973 < baseStart_6909973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6909986 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_6909986 : Nat := 118140960795 + 6909986 * 2 ^ 59
def prefixEnd_6909986 : Nat := 4983230072969 + 3 ^ 40 * 6909986 * 2
def baseEnd_6909986 : Nat := 3548144133838906881696559

theorem tailTrace_6909986 : CollatzResearch.WordTrace tailWord_6909986 prefixEnd_6909986 3548144133838906881696559 := by
  unfold tailWord_6909986
  simp only [CollatzResearch.WordTrace]
  refine ⟨63006973586077082124707453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168018596229538885665886541 63006973586077082124707453)
  ·
    refine ⟨23627615094778905796765295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63006973586077082124707453 23627615094778905796765295)
    ·
      refine ⟨35441422642168358695147943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23627615094778905796765295 35441422642168358695147943)
      ·
        refine ⟨53162133963252538042721915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35441422642168358695147943 53162133963252538042721915)
        ·
          refine ⟨79743200944878807064082873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53162133963252538042721915 79743200944878807064082873)
          ·
            refine ⟨59807400708659105298062155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79743200944878807064082873 59807400708659105298062155)
            ·
              refine ⟨89711101062988657947093233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59807400708659105298062155 89711101062988657947093233)
              ·
                refine ⟨67283325797241493460319925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89711101062988657947093233 67283325797241493460319925)
                ·
                  refine ⟨6307811793491390011904993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67283325797241493460319925 6307811793491390011904993)
                  ·
                    refine ⟨4730858845118542508928745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6307811793491390011904993 4730858845118542508928745)
                    ·
                      refine ⟨3548144133838906881696559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730858845118542508928745 3548144133838906881696559)
                      ·
                        rfl

theorem cell23_6909986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_6909986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6909986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6909986 prefixEnd_6909986 := by exact prefixLift 6909986
  have htrace : WordTrace (prefixWord ++ tailWord_6909986) baseStart_6909986 baseEnd_6909986 := by
    simpa [prefixWord, tailWord_6909986, baseEnd_6909986] using wordTrace_append hprefix tailTrace_6909986
  have hstable : (prefixWord ++ tailWord_6909986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6909986).length < 2 ^ (prefixWord ++ tailWord_6909986).sum := by decide
  have hdescent : baseEnd_6909986 < baseStart_6909986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6909986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910003 : List Nat := [1, 1, 1, 2, 4, 1, 4, 4, 1, 2, 2]
def baseStart_6910003 : Nat := 118140960795 + 6910003 * 2 ^ 59
def prefixEnd_6910003 : Nat := 4983230072969 + 3 ^ 40 * 6910003 * 2
def baseEnd_6910003 : Nat := 3548152863010033315183981

theorem tailTrace_6910003 : CollatzResearch.WordTrace tailWord_6910003 prefixEnd_6910003 3548152863010033315183981 := by
  unfold tailWord_6910003
  simp only [CollatzResearch.WordTrace]
  refine ⟨252028514385246740402198663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168019009590164493601465775 252028514385246740402198663)
  ·
    refine ⟨378042771577870110603297995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252028514385246740402198663 378042771577870110603297995)
    ·
      refine ⟨567064157366805165904946993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378042771577870110603297995 567064157366805165904946993)
      ·
        refine ⟨425298118025103874428710245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567064157366805165904946993 425298118025103874428710245)
        ·
          refine ⟨79743397129706976455383171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425298118025103874428710245 79743397129706976455383171)
          ·
            refine ⟨119615095694560464683074757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79743397129706976455383171 119615095694560464683074757)
            ·
              refine ⟨22427830442730087128076517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119615095694560464683074757 22427830442730087128076517)
              ·
                refine ⟨4205218208011891336514347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22427830442730087128076517 4205218208011891336514347)
                ·
                  refine ⟨6307827312017837004771521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205218208011891336514347 6307827312017837004771521)
                  ·
                    refine ⟨4730870484013377753578641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6307827312017837004771521 4730870484013377753578641)
                    ·
                      refine ⟨3548152863010033315183981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730870484013377753578641 3548152863010033315183981)
                      ·
                        rfl

theorem cell23_6910003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 2, 2].length) (baseStart_6910003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910003 prefixEnd_6910003 := by exact prefixLift 6910003
  have htrace : WordTrace (prefixWord ++ tailWord_6910003) baseStart_6910003 baseEnd_6910003 := by
    simpa [prefixWord, tailWord_6910003, baseEnd_6910003] using wordTrace_append hprefix tailTrace_6910003
  have hstable : (prefixWord ++ tailWord_6910003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910003).length < 2 ^ (prefixWord ++ tailWord_6910003).sum := by decide
  have hdescent : baseEnd_6910003 < baseStart_6910003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910052 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_6910052 : Nat := 118140960795 + 6910052 * 2 ^ 59
def prefixEnd_6910052 : Nat := 4983230072969 + 3 ^ 40 * 6910052 * 2
def baseEnd_6910052 : Nat := 1182726007854034541157085

theorem tailTrace_6910052 : CollatzResearch.WordTrace tailWord_6910052 prefixEnd_6910052 1182726007854034541157085 := by
  unfold tailWord_6910052
  simp only [CollatzResearch.WordTrace]
  refine ⟨126015150781034610885366205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168020201041379481180488273 126015150781034610885366205)
  ·
    refine ⟨47255681542887979082012327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126015150781034610885366205 47255681542887979082012327)
    ·
      refine ⟨70883522314331968623018491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47255681542887979082012327 70883522314331968623018491)
      ·
        refine ⟨106325283471497952934527737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70883522314331968623018491 106325283471497952934527737)
        ·
          refine ⟨79743962603623464700895803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106325283471497952934527737 79743962603623464700895803)
          ·
            refine ⟨119615943905435197051343705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79743962603623464700895803 119615943905435197051343705)
            ·
              refine ⟨89711957929076397788507779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119615943905435197051343705 89711957929076397788507779)
              ·
                refine ⟨134567936893614596682761669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89711957929076397788507779 134567936893614596682761669)
                ·
                  refine ⟨25231488167552736878017813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134567936893614596682761669 25231488167552736878017813)
                  ·
                    refine ⟨1182726007854034541157085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25231488167552736878017813 1182726007854034541157085)
                    ·
                      rfl

theorem cell23_6910052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_6910052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910052 prefixEnd_6910052 := by exact prefixLift 6910052
  have htrace : WordTrace (prefixWord ++ tailWord_6910052) baseStart_6910052 baseEnd_6910052 := by
    simpa [prefixWord, tailWord_6910052, baseEnd_6910052] using wordTrace_append hprefix tailTrace_6910052
  have hstable : (prefixWord ++ tailWord_6910052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910052).length < 2 ^ (prefixWord ++ tailWord_6910052).sum := by decide
  have hdescent : baseEnd_6910052 < baseStart_6910052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910070 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6910070 : Nat := 118140960795 + 6910070 * 2 ^ 59
def prefixEnd_6910070 : Nat := 4983230072969 + 3 ^ 40 * 6910070 * 2
def baseEnd_6910070 : Nat := 3548187266213884553046173

theorem tailTrace_6910070 : CollatzResearch.WordTrace tailWord_6910070 prefixEnd_6910070 3548187266213884553046173 := by
  unfold tailWord_6910070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15751934879750250677805479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168020638717336007229925109 15751934879750250677805479)
  ·
    refine ⟨23627902319625376016708219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15751934879750250677805479 23627902319625376016708219)
    ·
      refine ⟨35441853479438064025062329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23627902319625376016708219 35441853479438064025062329)
      ·
        refine ⟨26581390109578548018796747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35441853479438064025062329 26581390109578548018796747)
        ·
          refine ⟨39872085164367822028195121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26581390109578548018796747 39872085164367822028195121)
          ·
            refine ⟨29904063873275866521146341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39872085164367822028195121 29904063873275866521146341)
            ·
              refine ⟨5607011976239224972714939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29904063873275866521146341 5607011976239224972714939)
              ·
                refine ⟨8410517964358837459072409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607011976239224972714939 8410517964358837459072409)
                ·
                  refine ⟨6307888473269128094304307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8410517964358837459072409 6307888473269128094304307)
                  ·
                    refine ⟨9461832709903692141456461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6307888473269128094304307 9461832709903692141456461)
                    ·
                      refine ⟨3548187266213884553046173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9461832709903692141456461 3548187266213884553046173)
                      ·
                        rfl

theorem cell23_6910070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6910070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910070 prefixEnd_6910070 := by exact prefixLift 6910070
  have htrace : WordTrace (prefixWord ++ tailWord_6910070) baseStart_6910070 baseEnd_6910070 := by
    simpa [prefixWord, tailWord_6910070, baseEnd_6910070] using wordTrace_append hprefix tailTrace_6910070
  have hstable : (prefixWord ++ tailWord_6910070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910070).length < 2 ^ (prefixWord ++ tailWord_6910070).sum := by decide
  have hdescent : baseEnd_6910070 < baseStart_6910070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910072 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_6910072 : Nat := 118140960795 + 6910072 * 2 ^ 59
def prefixEnd_6910072 : Nat := 4983230072969 + 3 ^ 40 * 6910072 * 2
def baseEnd_6910072 : Nat := 3548188293175193545221163

theorem tailTrace_6910072 : CollatzResearch.WordTrace tailWord_6910072 prefixEnd_6910072 3548188293175193545221163 := by
  unfold tailWord_6910072
  simp only [CollatzResearch.WordTrace]
  refine ⟨126015515510998382593230235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168020687347997843457640313 126015515510998382593230235)
  ·
    refine ⟨189023273266497573889845353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126015515510998382593230235 189023273266497573889845353)
    ·
      refine ⟨141767454949873180417384015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189023273266497573889845353 141767454949873180417384015)
      ·
        refine ⟨212651182424809770626076023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141767454949873180417384015 212651182424809770626076023)
        ·
          refine ⟨318976773637214655939114035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212651182424809770626076023 318976773637214655939114035)
          ·
            refine ⟨478465160455821983908671053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318976773637214655939114035 478465160455821983908671053)
            ·
              refine ⟨179424435170933243965751645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478465160455821983908671053 179424435170933243965751645)
              ·
                refine ⟨67284163189099966487156867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179424435170933243965751645 67284163189099966487156867)
                ·
                  refine ⟨100926244783649949730735301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67284163189099966487156867 100926244783649949730735301)
                  ·
                    refine ⟨18923670896934365574512869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100926244783649949730735301 18923670896934365574512869)
                    ·
                      refine ⟨3548188293175193545221163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18923670896934365574512869 3548188293175193545221163)
                      ·
                        rfl

theorem cell23_6910072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_6910072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910072 prefixEnd_6910072 := by exact prefixLift 6910072
  have htrace : WordTrace (prefixWord ++ tailWord_6910072) baseStart_6910072 baseEnd_6910072 := by
    simpa [prefixWord, tailWord_6910072, baseEnd_6910072] using wordTrace_append hprefix tailTrace_6910072
  have hstable : (prefixWord ++ tailWord_6910072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910072).length < 2 ^ (prefixWord ++ tailWord_6910072).sum := by decide
  have hdescent : baseEnd_6910072 < baseStart_6910072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910099 : List Nat := [1, 1, 1, 2, 1, 2, 3, 7, 5]
def baseStart_6910099 : Nat := 118140960795 + 6910099 * 2 ^ 59
def prefixEnd_6910099 : Nat := 4983230072969 + 3 ^ 40 * 6910099 * 2
def baseEnd_6910099 : Nat := 394244684128096104398171

theorem tailTrace_6910099 : CollatzResearch.WordTrace tailWord_6910099 prefixEnd_6910099 394244684128096104398171 := by
  unfold tailWord_6910099
  simp only [CollatzResearch.WordTrace]
  refine ⟨252032015792898948797693351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168021343861932632531795567 252032015792898948797693351)
  ·
    refine ⟨378048023689348423196540027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252032015792898948797693351 378048023689348423196540027)
    ·
      refine ⟨567072035534022634794810041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378048023689348423196540027 567072035534022634794810041)
      ·
        refine ⟨425304026650516976096107531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567072035534022634794810041 425304026650516976096107531)
        ·
          refine ⟨637956039975775464144161297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425304026650516976096107531 637956039975775464144161297)
          ·
            refine ⟨478467029981831598108120973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637956039975775464144161297 478467029981831598108120973)
            ·
              refine ⟨179425136243186849290545365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478467029981831598108120973 179425136243186849290545365)
              ·
                refine ⟨4205276630699691780247157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179425136243186849290545365 4205276630699691780247157)
                ·
                  refine ⟨394244684128096104398171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205276630699691780247157 394244684128096104398171)
                  ·
                    rfl

theorem cell23_6910099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 5].length) (baseStart_6910099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910099 prefixEnd_6910099 := by exact prefixLift 6910099
  have htrace : WordTrace (prefixWord ++ tailWord_6910099) baseStart_6910099 baseEnd_6910099 := by
    simpa [prefixWord, tailWord_6910099, baseEnd_6910099] using wordTrace_append hprefix tailTrace_6910099
  have hstable : (prefixWord ++ tailWord_6910099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910099).length < 2 ^ (prefixWord ++ tailWord_6910099).sum := by decide
  have hdescent : baseEnd_6910099 < baseStart_6910099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910159 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 5, 4]
def baseStart_6910159 : Nat := 118140960795 + 6910159 * 2 ^ 59
def prefixEnd_6910159 : Nat := 4983230072969 + 3 ^ 40 * 6910159 * 2
def baseEnd_6910159 : Nat := 1182744321997378234944421

theorem tailTrace_6910159 : CollatzResearch.WordTrace tailWord_6910159 prefixEnd_6910159 1182744321997378234944421 := by
  unfold tailWord_6910159
  simp only [CollatzResearch.WordTrace]
  refine ⟨252034204172681579044877531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168022802781787719363251687 252034204172681579044877531)
  ·
    refine ⟨378051306259022368567316297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252034204172681579044877531 378051306259022368567316297)
    ·
      refine ⟨283538479694266776425487223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378051306259022368567316297 283538479694266776425487223)
      ·
        refine ⟨425307719541400164638230835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283538479694266776425487223 425307719541400164638230835)
        ·
          refine ⟨637961579312100246957346253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425307719541400164638230835 637961579312100246957346253)
          ·
            refine ⟨239235592242037592609004845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 637961579312100246957346253 239235592242037592609004845)
            ·
              refine ⟨89713347090764097228376817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239235592242037592609004845 89713347090764097228376817)
              ·
                refine ⟨67285010318073072921282613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89713347090764097228376817 67285010318073072921282613)
                ·
                  refine ⟨6307969717319350586370245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67285010318073072921282613 6307969717319350586370245)
                  ·
                    refine ⟨1182744321997378234944421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6307969717319350586370245 1182744321997378234944421)
                    ·
                      rfl

theorem cell23_6910159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_6910159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910159 prefixEnd_6910159 := by exact prefixLift 6910159
  have htrace : WordTrace (prefixWord ++ tailWord_6910159) baseStart_6910159 baseEnd_6910159 := by
    simpa [prefixWord, tailWord_6910159, baseEnd_6910159] using wordTrace_append hprefix tailTrace_6910159
  have hstable : (prefixWord ++ tailWord_6910159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910159).length < 2 ^ (prefixWord ++ tailWord_6910159).sum := by decide
  have hdescent : baseEnd_6910159 < baseStart_6910159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910176 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 3, 4]
def baseStart_6910176 : Nat := 118140960795 + 6910176 * 2 ^ 59
def prefixEnd_6910176 : Nat := 4983230072969 + 3 ^ 40 * 6910176 * 2
def baseEnd_6910176 : Nat := 1182747231721087046106895

theorem tailTrace_6910176 : CollatzResearch.WordTrace tailWord_6910176 prefixEnd_6910176 1182747231721087046106895 := by
  unfold tailWord_6910176
  simp only [CollatzResearch.WordTrace]
  refine ⟨126017412106809995474123191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168023216142413327298830921 126017412106809995474123191)
  ·
    refine ⟨189026118160214993211184787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126017412106809995474123191 189026118160214993211184787)
    ·
      refine ⟨283539177240322489816777181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189026118160214993211184787 283539177240322489816777181)
      ·
        refine ⟨106327191465120933681291443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283539177240322489816777181 106327191465120933681291443)
        ·
          refine ⟨159490787197681400521937165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106327191465120933681291443 159490787197681400521937165)
          ·
            refine ⟨59809045199130525195726437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159490787197681400521937165 59809045199130525195726437)
            ·
              refine ⟨11214195974836973474198707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59809045199130525195726437 11214195974836973474198707)
              ·
                refine ⟨16821293962255460211298061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11214195974836973474198707 16821293962255460211298061)
                ·
                  refine ⟨6307985235845797579236773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16821293962255460211298061 6307985235845797579236773)
                  ·
                    refine ⟨1182747231721087046106895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6307985235845797579236773 1182747231721087046106895)
                    ·
                      rfl

theorem cell23_6910176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_6910176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910176 prefixEnd_6910176 := by exact prefixLift 6910176
  have htrace : WordTrace (prefixWord ++ tailWord_6910176) baseStart_6910176 baseEnd_6910176 := by
    simpa [prefixWord, tailWord_6910176, baseEnd_6910176] using wordTrace_append hprefix tailTrace_6910176
  have hstable : (prefixWord ++ tailWord_6910176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910176).length < 2 ^ (prefixWord ++ tailWord_6910176).sum := by decide
  have hdescent : baseEnd_6910176 < baseStart_6910176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910183 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6910183 : Nat := 118140960795 + 6910183 * 2 ^ 59
def prefixEnd_6910183 : Nat := 4983230072969 + 3 ^ 40 * 6910183 * 2
def baseEnd_6910183 : Nat := 3548245289527842610933153

theorem tailTrace_6910183 : CollatzResearch.WordTrace tailWord_6910183 prefixEnd_6910183 3548245289527842610933153 := by
  unfold tailWord_6910183
  simp only [CollatzResearch.WordTrace]
  refine ⟨252035079524594631143751203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168023386349729754095834135 252035079524594631143751203)
  ·
    refine ⟨378052619286891946715626805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252035079524594631143751203 378052619286891946715626805)
    ·
      refine ⟨35442433058146120004590013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 378052619286891946715626805 35442433058146120004590013)
      ·
        refine ⟨13290912396804795001721255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35442433058146120004590013 13290912396804795001721255)
        ·
          refine ⟨19936368595207192502581883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13290912396804795001721255 19936368595207192502581883)
          ·
            refine ⟨29904552892810788753872825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19936368595207192502581883 29904552892810788753872825)
            ·
              refine ⟨22428414669608091565404619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29904552892810788753872825 22428414669608091565404619)
              ·
                refine ⟨33642622004412137348106929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22428414669608091565404619 33642622004412137348106929)
                ·
                  refine ⟨25231966503309103011080197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33642622004412137348106929 25231966503309103011080197)
                  ·
                    refine ⟨4730993719370456814577537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25231966503309103011080197 4730993719370456814577537)
                    ·
                      refine ⟨3548245289527842610933153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4730993719370456814577537 3548245289527842610933153)
                      ·
                        rfl

theorem cell23_6910183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6910183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910183 prefixEnd_6910183 := by exact prefixLift 6910183
  have htrace : WordTrace (prefixWord ++ tailWord_6910183) baseStart_6910183 baseEnd_6910183 := by
    simpa [prefixWord, tailWord_6910183, baseEnd_6910183] using wordTrace_append hprefix tailTrace_6910183
  have hstable : (prefixWord ++ tailWord_6910183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910183).length < 2 ^ (prefixWord ++ tailWord_6910183).sum := by decide
  have hdescent : baseEnd_6910183 < baseStart_6910183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910256 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4]
def baseStart_6910256 : Nat := 118140960795 + 6910256 * 2 ^ 59
def prefixEnd_6910256 : Nat := 4983230072969 + 3 ^ 40 * 6910256 * 2
def baseEnd_6910256 : Nat := 3548282773615620825320317

theorem tailTrace_6910256 : CollatzResearch.WordTrace tailWord_6910256 prefixEnd_6910256 3548282773615620825320317 := by
  unfold tailWord_6910256
  simp only [CollatzResearch.WordTrace]
  refine ⟨126018871026665082305579311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168025161368886776407439081 126018871026665082305579311)
  ·
    refine ⟨189028306539997623458368967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126018871026665082305579311 189028306539997623458368967)
    ·
      refine ⟨283542459809996435187553451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189028306539997623458368967 283542459809996435187553451)
      ·
        refine ⟨425313689714994652781330177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283542459809996435187553451 425313689714994652781330177)
        ·
          refine ⟨318985267286245989585997633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425313689714994652781330177 318985267286245989585997633)
          ·
            refine ⟨239238950464684492189498225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318985267286245989585997633 239238950464684492189498225)
            ·
              refine ⟨179429212848513369142123669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239238950464684492189498225 179429212848513369142123669)
              ·
                refine ⟨8410744352274064178537047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179429212848513369142123669 8410744352274064178537047)
                ·
                  refine ⟨12616116528411096267805571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410744352274064178537047 12616116528411096267805571)
                  ·
                    refine ⟨18924174792616644401708357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12616116528411096267805571 18924174792616644401708357)
                    ·
                      refine ⟨3548282773615620825320317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18924174792616644401708357 3548282773615620825320317)
                      ·
                        rfl

theorem cell23_6910256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_6910256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910256 prefixEnd_6910256 := by exact prefixLift 6910256
  have htrace : WordTrace (prefixWord ++ tailWord_6910256) baseStart_6910256 baseEnd_6910256 := by
    simpa [prefixWord, tailWord_6910256, baseEnd_6910256] using wordTrace_append hprefix tailTrace_6910256
  have hstable : (prefixWord ++ tailWord_6910256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910256).length < 2 ^ (prefixWord ++ tailWord_6910256).sum := by decide
  have hdescent : baseEnd_6910256 < baseStart_6910256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910260 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_6910260 : Nat := 118140960795 + 6910260 * 2 ^ 59
def prefixEnd_6910260 : Nat := 4983230072969 + 3 ^ 40 * 6910260 * 2
def baseEnd_6910260 : Nat := 3548284827538238809670299

theorem tailTrace_6910260 : CollatzResearch.WordTrace tailWord_6910260 prefixEnd_6910260 3548284827538238809670299 := by
  unfold tailWord_6910260
  simp only [CollatzResearch.WordTrace]
  refine ⟨126018943972657836647152117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168025258630210448862869489 126018943972657836647152117)
  ·
    refine ⟨11814275997436672185670511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126018943972657836647152117 11814275997436672185670511)
    ·
      refine ⟨17721413996155008278505767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11814275997436672185670511 17721413996155008278505767)
      ·
        refine ⟨26582120994232512417758651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17721413996155008278505767 26582120994232512417758651)
        ·
          refine ⟨39873181491348768626637977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26582120994232512417758651 39873181491348768626637977)
          ·
            refine ⟨29904886118511576469978483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39873181491348768626637977 29904886118511576469978483)
            ·
              refine ⟨44857329177767364704967725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29904886118511576469978483 44857329177767364704967725)
              ·
                refine ⟨16821498441662761764362897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44857329177767364704967725 16821498441662761764362897)
                ·
                  refine ⟨12616123831247071323272173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16821498441662761764362897 12616123831247071323272173)
                  ·
                    refine ⟨4731046436717651746227065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12616123831247071323272173 4731046436717651746227065)
                    ·
                      refine ⟨3548284827538238809670299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731046436717651746227065 3548284827538238809670299)
                      ·
                        rfl

theorem cell23_6910260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_6910260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910260 prefixEnd_6910260 := by exact prefixLift 6910260
  have htrace : WordTrace (prefixWord ++ tailWord_6910260) baseStart_6910260 baseEnd_6910260 := by
    simpa [prefixWord, tailWord_6910260, baseEnd_6910260] using wordTrace_append hprefix tailTrace_6910260
  have hstable : (prefixWord ++ tailWord_6910260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910260).length < 2 ^ (prefixWord ++ tailWord_6910260).sum := by decide
  have hdescent : baseEnd_6910260 < baseStart_6910260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910266 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_6910266 : Nat := 118140960795 + 6910266 * 2 ^ 59
def prefixEnd_6910266 : Nat := 4983230072969 + 3 ^ 40 * 6910266 * 2
def baseEnd_6910266 : Nat := 1182762636140721928731757

theorem tailTrace_6910266 : CollatzResearch.WordTrace tailWord_6910266 prefixEnd_6910266 1182762636140721928731757 := by
  unfold tailWord_6910266
  simp only [CollatzResearch.WordTrace]
  refine ⟨63009526695823484079755663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168025404522195957546015101 63009526695823484079755663)
  ·
    refine ⟨94514290043735226119633495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63009526695823484079755663 94514290043735226119633495)
    ·
      refine ⟨141771435065602839179450243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94514290043735226119633495 141771435065602839179450243)
      ·
        refine ⟨212657152598404258769175365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141771435065602839179450243 212657152598404258769175365)
        ·
          refine ⟨39873216112200798519220381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212657152598404258769175365 39873216112200798519220381)
          ·
            refine ⟨14952456042075299444707643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39873216112200798519220381 14952456042075299444707643)
            ·
              refine ⟨22428684063112949167061465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14952456042075299444707643 22428684063112949167061465)
              ·
                refine ⟨16821513047334711875296099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22428684063112949167061465 16821513047334711875296099)
                ·
                  refine ⟨25232269571002067812944149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16821513047334711875296099 25232269571002067812944149)
                  ·
                    refine ⟨1182762636140721928731757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25232269571002067812944149 1182762636140721928731757)
                    ·
                      rfl

theorem cell23_6910266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_6910266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910266 prefixEnd_6910266 := by exact prefixLift 6910266
  have htrace : WordTrace (prefixWord ++ tailWord_6910266) baseStart_6910266 baseEnd_6910266 := by
    simpa [prefixWord, tailWord_6910266, baseEnd_6910266] using wordTrace_append hprefix tailTrace_6910266
  have hstable : (prefixWord ++ tailWord_6910266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910266).length < 2 ^ (prefixWord ++ tailWord_6910266).sum := by decide
  have hdescent : baseEnd_6910266 < baseStart_6910266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910270 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_6910270 : Nat := 118140960795 + 6910270 * 2 ^ 59
def prefixEnd_6910270 : Nat := 4983230072969 + 3 ^ 40 * 6910270 * 2
def baseEnd_6910270 : Nat := 1182763320781594590181751

theorem tailTrace_6910270 : CollatzResearch.WordTrace tailWord_6910270 prefixEnd_6910270 1182763320781594590181751 := by
  unfold tailWord_6910270
  simp only [CollatzResearch.WordTrace]
  refine ⟨31504781584409930625271033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168025501783519630001445509 31504781584409930625271033)
  ·
    refine ⟨23628586188307447968953275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31504781584409930625271033 23628586188307447968953275)
    ·
      refine ⟨35442879282461171953429913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23628586188307447968953275 35442879282461171953429913)
      ·
        refine ⟨26582159461845878965072435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35442879282461171953429913 26582159461845878965072435)
        ·
          refine ⟨39873239192768818447608653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26582159461845878965072435 39873239192768818447608653)
          ·
            refine ⟨14952464697288306917853245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39873239192768818447608653 14952464697288306917853245)
            ·
              refine ⟨5607174261483115094194967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14952464697288306917853245 5607174261483115094194967)
              ·
                refine ⟨8410761392224672641292451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607174261483115094194967 8410761392224672641292451)
                ·
                  refine ⟨12616142088337008961938677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410761392224672641292451 12616142088337008961938677)
                  ·
                    refine ⟨1182763320781594590181751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12616142088337008961938677 1182763320781594590181751)
                    ·
                      rfl

theorem cell23_6910270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_6910270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910270 prefixEnd_6910270 := by exact prefixLift 6910270
  have htrace : WordTrace (prefixWord ++ tailWord_6910270) baseStart_6910270 baseEnd_6910270 := by
    simpa [prefixWord, tailWord_6910270, baseEnd_6910270] using wordTrace_append hprefix tailTrace_6910270
  have hstable : (prefixWord ++ tailWord_6910270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910270).length < 2 ^ (prefixWord ++ tailWord_6910270).sum := by decide
  have hdescent : baseEnd_6910270 < baseStart_6910270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910300 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_6910300 : Nat := 118140960795 + 6910300 * 2 ^ 59
def prefixEnd_6910300 : Nat := 4983230072969 + 3 ^ 40 * 6910300 * 2
def baseEnd_6910300 : Nat := 1182768455588139551056705

theorem tailTrace_6910300 : CollatzResearch.WordTrace tailWord_6910300 prefixEnd_6910300 1182768455588139551056705 := by
  unfold tailWord_6910300
  simp only [CollatzResearch.WordTrace]
  refine ⟨126019673432585380062880177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168026231243447173417173569 126019673432585380062880177)
  ·
    refine ⟨94514755074439035047160133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126019673432585380062880177 94514755074439035047160133)
    ·
      refine ⟨17721516576457319071342525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94514755074439035047160133 17721516576457319071342525)
      ·
        refine ⟨6645568716171494651753447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17721516576457319071342525 6645568716171494651753447)
        ·
          refine ⟨9968353074257241977630171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6645568716171494651753447 9968353074257241977630171)
          ·
            refine ⟨14952529611385862966445257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968353074257241977630171 14952529611385862966445257)
            ·
              refine ⟨11214397208539397224833943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14952529611385862966445257 11214397208539397224833943)
              ·
                refine ⟨16821595812809095837250915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11214397208539397224833943 16821595812809095837250915)
                ·
                  refine ⟨25232393719213643755876373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16821595812809095837250915 25232393719213643755876373)
                  ·
                    refine ⟨1182768455588139551056705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25232393719213643755876373 1182768455588139551056705)
                    ·
                      rfl

theorem cell23_6910300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_6910300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910300 prefixEnd_6910300 := by exact prefixLift 6910300
  have htrace : WordTrace (prefixWord ++ tailWord_6910300) baseStart_6910300 baseEnd_6910300 := by
    simpa [prefixWord, tailWord_6910300, baseEnd_6910300] using wordTrace_append hprefix tailTrace_6910300
  have hstable : (prefixWord ++ tailWord_6910300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910300).length < 2 ^ (prefixWord ++ tailWord_6910300).sum := by decide
  have hdescent : baseEnd_6910300 < baseStart_6910300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910426 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_6910426 : Nat := 118140960795 + 6910426 * 2 ^ 59
def prefixEnd_6910426 : Nat := 4983230072969 + 3 ^ 40 * 6910426 * 2
def baseEnd_6910426 : Nat := 3548370065326885160194535

theorem tailTrace_6910426 : CollatzResearch.WordTrace tailWord_6910426 prefixEnd_6910426 3548370065326885160194535 := by
  unfold tailWord_6910426
  simp only [CollatzResearch.WordTrace]
  refine ⟨63010985615678570911211783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168029294975142855763231421 63010985615678570911211783)
  ·
    refine ⟨94516478423517856366817675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63010985615678570911211783 94516478423517856366817675)
    ·
      refine ⟨141774717635276784550226513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94516478423517856366817675 141774717635276784550226513)
      ·
        refine ⟨106331038226457588412669885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141774717635276784550226513 106331038226457588412669885)
        ·
          refine ⟨39874139334921595654751207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106331038226457588412669885 39874139334921595654751207)
          ·
            refine ⟨59811209002382393482126811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39874139334921595654751207 59811209002382393482126811)
            ·
              refine ⟨89716813503573590223190217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59811209002382393482126811 89716813503573590223190217)
              ·
                refine ⟨67287610127680192667392663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89716813503573590223190217 67287610127680192667392663)
                ·
                  refine ⟨100931415191520289001088995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67287610127680192667392663 100931415191520289001088995)
                  ·
                    refine ⟨151397122787280433501633493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100931415191520289001088995 151397122787280433501633493)
                    ·
                      refine ⟨3548370065326885160194535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151397122787280433501633493 3548370065326885160194535)
                      ·
                        rfl

theorem cell23_6910426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_6910426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910426 prefixEnd_6910426 := by exact prefixLift 6910426
  have htrace : WordTrace (prefixWord ++ tailWord_6910426) baseStart_6910426 baseEnd_6910426 := by
    simpa [prefixWord, tailWord_6910426, baseEnd_6910426] using wordTrace_append hprefix tailTrace_6910426
  have hstable : (prefixWord ++ tailWord_6910426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910426).length < 2 ^ (prefixWord ++ tailWord_6910426).sum := by decide
  have hdescent : baseEnd_6910426 < baseStart_6910426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910433 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 2, 5]
def baseStart_6910433 : Nat := 118140960795 + 6910433 * 2 ^ 59
def prefixEnd_6910433 : Nat := 4983230072969 + 3 ^ 40 * 6910433 * 2
def baseEnd_6910433 : Nat := 1182791219897155544269001

theorem tailTrace_6910433 : CollatzResearch.WordTrace tailWord_6910433 prefixEnd_6910433 1182791219897155544269001 := by
  unfold tailWord_6910433
  simp only [CollatzResearch.WordTrace]
  refine ⟨252044197773688923840351953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168029465182459282560234635 252044197773688923840351953)
  ·
    refine ⟨189033148330266692880263965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252044197773688923840351953 189033148330266692880263965)
    ·
      refine ⟨70887430623850009830098987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189033148330266692880263965 70887430623850009830098987)
      ·
        refine ⟨106331145935775014745148481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70887430623850009830098987 106331145935775014745148481)
        ·
          refine ⟨79748359451831261058861361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106331145935775014745148481 79748359451831261058861361)
          ·
            refine ⟨59811269588873445794146021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79748359451831261058861361 59811269588873445794146021)
            ·
              refine ⟨11214613047913771086402379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59811269588873445794146021 11214613047913771086402379)
              ·
                refine ⟨16821919571870656629603569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11214613047913771086402379 16821919571870656629603569)
                ·
                  refine ⟨12616439678902992472202677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16821919571870656629603569 12616439678902992472202677)
                  ·
                    refine ⟨1182791219897155544269001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12616439678902992472202677 1182791219897155544269001)
                    ·
                      rfl

theorem cell23_6910433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_6910433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910433 prefixEnd_6910433 := by exact prefixLift 6910433
  have htrace : WordTrace (prefixWord ++ tailWord_6910433) baseStart_6910433 baseEnd_6910433 := by
    simpa [prefixWord, tailWord_6910433, baseEnd_6910433] using wordTrace_append hprefix tailTrace_6910433
  have hstable : (prefixWord ++ tailWord_6910433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910433).length < 2 ^ (prefixWord ++ tailWord_6910433).sum := by decide
  have hdescent : baseEnd_6910433 < baseStart_6910433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910456 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_6910456 : Nat := 118140960795 + 6910456 * 2 ^ 59
def prefixEnd_6910456 : Nat := 4983230072969 + 3 ^ 40 * 6910456 * 2
def baseEnd_6910456 : Nat := 3548385469746520042819397

theorem tailTrace_6910456 : CollatzResearch.WordTrace tailWord_6910456 prefixEnd_6910456 3548385469746520042819397 := by
  unfold tailWord_6910456
  simp only [CollatzResearch.WordTrace]
  refine ⟨126022518326302799384219611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168030024435070399178959481 126022518326302799384219611)
  ·
    refine ⟨189033777489454199076329417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126022518326302799384219611 189033777489454199076329417)
    ·
      refine ⟨141775333117090649307247063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189033777489454199076329417 141775333117090649307247063)
      ·
        refine ⟨212662999675635973960870595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141775333117090649307247063 212662999675635973960870595)
        ·
          refine ⟨318994499513453960941305893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212662999675635973960870595 318994499513453960941305893)
          ·
            refine ⟨59811468658772617676494855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318994499513453960941305893 59811468658772617676494855)
            ·
              refine ⟨89717202988158926514742283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59811468658772617676494855 89717202988158926514742283)
              ·
                refine ⟨134575804482238389772113425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89717202988158926514742283 134575804482238389772113425)
                ·
                  refine ⟨100931853361678792329085069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134575804482238389772113425 100931853361678792329085069)
                  ·
                    refine ⟨37849445010629547123406901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100931853361678792329085069 37849445010629547123406901)
                    ·
                      refine ⟨3548385469746520042819397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37849445010629547123406901 3548385469746520042819397)
                      ·
                        rfl

theorem cell23_6910456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_6910456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910456 prefixEnd_6910456 := by exact prefixLift 6910456
  have htrace : WordTrace (prefixWord ++ tailWord_6910456) baseStart_6910456 baseEnd_6910456 := by
    simpa [prefixWord, tailWord_6910456, baseEnd_6910456] using wordTrace_append hprefix tailTrace_6910456
  have hstable : (prefixWord ++ tailWord_6910456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910456).length < 2 ^ (prefixWord ++ tailWord_6910456).sum := by decide
  have hdescent : baseEnd_6910456 < baseStart_6910456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910463 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 3, 4]
def baseStart_6910463 : Nat := 118140960795 + 6910463 * 2 ^ 59
def prefixEnd_6910463 : Nat := 4983230072969 + 3 ^ 40 * 6910463 * 2
def baseEnd_6910463 : Nat := 1182796354703700505143955

theorem tailTrace_6910463 : CollatzResearch.WordTrace tailWord_6910463 prefixEnd_6910463 1182796354703700505143955 := by
  unfold tailWord_6910463
  simp only [CollatzResearch.WordTrace]
  refine ⟨252045291963580238963944043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168030194642386825975962695 252045291963580238963944043)
  ·
    refine ⟨378067937945370358445916065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252045291963580238963944043 378067937945370358445916065)
    ·
      refine ⟨283550953459027768834437049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378067937945370358445916065 283550953459027768834437049)
      ·
        refine ⟨212663215094270826625827787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283550953459027768834437049 212663215094270826625827787)
        ·
          refine ⟨318994822641406239938741681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212663215094270826625827787 318994822641406239938741681)
          ·
            refine ⟨239246116981054679954056261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318994822641406239938741681 239246116981054679954056261)
            ·
              refine ⟨44858646933947752491385549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239246116981054679954056261 44858646933947752491385549)
              ·
                refine ⟨16821992600230407184269581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44858646933947752491385549 16821992600230407184269581)
                ·
                  refine ⟨6308247225086402694101093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16821992600230407184269581 6308247225086402694101093)
                  ·
                    refine ⟨1182796354703700505143955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6308247225086402694101093 1182796354703700505143955)
                    ·
                      rfl

theorem cell23_6910463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_6910463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910463 prefixEnd_6910463 := by exact prefixLift 6910463
  have htrace : WordTrace (prefixWord ++ tailWord_6910463) baseStart_6910463 baseEnd_6910463 := by
    simpa [prefixWord, tailWord_6910463, baseEnd_6910463] using wordTrace_append hprefix tailTrace_6910463
  have hstable : (prefixWord ++ tailWord_6910463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910463).length < 2 ^ (prefixWord ++ tailWord_6910463).sum := by decide
  have hdescent : baseEnd_6910463 < baseStart_6910463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910490 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_6910490 : Nat := 118140960795 + 6910490 * 2 ^ 59
def prefixEnd_6910490 : Nat := 4983230072969 + 3 ^ 40 * 6910490 * 2
def baseEnd_6910490 : Nat := 3548402928088772909794241

theorem tailTrace_6910490 : CollatzResearch.WordTrace tailWord_6910490 prefixEnd_6910490 3548402928088772909794241 := by
  unfold tailWord_6910490
  simp only [CollatzResearch.WordTrace]
  refine ⟨63011569183620605643794231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168030851156321615050117949 63011569183620605643794231)
  ·
    refine ⟨94517353775430908465691347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63011569183620605643794231 94517353775430908465691347)
    ·
      refine ⟨141776030663146362698537021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94517353775430908465691347 141776030663146362698537021)
      ·
        refine ⟨53166011498679886011951383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141776030663146362698537021 53166011498679886011951383)
        ·
          refine ⟨79749017248019829017927075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53166011498679886011951383 79749017248019829017927075)
          ·
            refine ⟨119623525872029743526890613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79749017248019829017927075 119623525872029743526890613)
            ·
              refine ⟨11214705550502788455645995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119623525872029743526890613 11214705550502788455645995)
              ·
                refine ⟨16822058325754182683468993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11214705550502788455645995 16822058325754182683468993)
                ·
                  refine ⟨12616543744315637012601745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16822058325754182683468993 12616543744315637012601745)
                  ·
                    refine ⟨9462407808236727759451309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12616543744315637012601745 9462407808236727759451309)
                    ·
                      refine ⟨3548402928088772909794241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9462407808236727759451309 3548402928088772909794241)
                      ·
                        rfl

theorem cell23_6910490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_6910490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910490 prefixEnd_6910490 := by exact prefixLift 6910490
  have htrace : WordTrace (prefixWord ++ tailWord_6910490) baseStart_6910490 baseEnd_6910490 := by
    simpa [prefixWord, tailWord_6910490, baseEnd_6910490] using wordTrace_append hprefix tailTrace_6910490
  have hstable : (prefixWord ++ tailWord_6910490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910490).length < 2 ^ (prefixWord ++ tailWord_6910490).sum := by decide
  have hdescent : baseEnd_6910490 < baseStart_6910490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910497 : List Nat := [1, 2, 3, 2, 2, 1, 4, 3, 1, 4]
def baseStart_6910497 : Nat := 118140960795 + 6910497 * 2 ^ 59
def prefixEnd_6910497 : Nat := 4983230072969 + 3 ^ 40 * 6910497 * 2
def baseEnd_6910497 : Nat := 1182802174151118127468903

theorem tailTrace_6910497 : CollatzResearch.WordTrace tailWord_6910497 prefixEnd_6910497 1182802174151118127468903 := by
  unfold tailWord_6910497
  simp only [CollatzResearch.WordTrace]
  refine ⟨252046532045457062770681745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168031021363638041847121163 252046532045457062770681745)
  ·
    refine ⟨189034899034092797078011309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252046532045457062770681745 189034899034092797078011309)
    ·
      refine ⟨70888087137784798904254241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189034899034092797078011309 70888087137784798904254241)
      ·
        refine ⟨53166065353338599178190681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70888087137784798904254241 53166065353338599178190681)
        ·
          refine ⟨39874549015003949383643011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53166065353338599178190681 39874549015003949383643011)
          ·
            refine ⟨59811823522505924075464517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39874549015003949383643011 59811823522505924075464517)
            ·
              refine ⟨11214716910469860764149597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59811823522505924075464517 11214716910469860764149597)
              ·
                refine ⟨4205518841426197786556099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11214716910469860764149597 4205518841426197786556099)
                ·
                  refine ⟨6308278262139296679834149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205518841426197786556099 6308278262139296679834149)
                  ·
                    refine ⟨1182802174151118127468903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6308278262139296679834149 1182802174151118127468903)
                    ·
                      rfl

theorem cell23_6910497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_6910497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910497 prefixEnd_6910497 := by exact prefixLift 6910497
  have htrace : WordTrace (prefixWord ++ tailWord_6910497) baseStart_6910497 baseEnd_6910497 := by
    simpa [prefixWord, tailWord_6910497, baseEnd_6910497] using wordTrace_append hprefix tailTrace_6910497
  have hstable : (prefixWord ++ tailWord_6910497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910497).length < 2 ^ (prefixWord ++ tailWord_6910497).sum := by decide
  have hdescent : baseEnd_6910497 < baseStart_6910497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910510 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_6910510 : Nat := 118140960795 + 6910510 * 2 ^ 59
def prefixEnd_6910510 : Nat := 4983230072969 + 3 ^ 40 * 6910510 * 2
def baseEnd_6910510 : Nat := 394268133077984759060461

theorem tailTrace_6910510 : CollatzResearch.WordTrace tailWord_6910510 prefixEnd_6910510 394268133077984759060461 := by
  unfold tailWord_6910510
  simp only [CollatzResearch.WordTrace]
  refine ⟨31505875774301245748863123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168031337462939977327269989 31505875774301245748863123)
  ·
    refine ⟨47258813661451868623294685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31505875774301245748863123 47258813661451868623294685)
    ·
      refine ⟨17722055123044450733735507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47258813661451868623294685 17722055123044450733735507)
      ·
        refine ⟨26583082684566676100603261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17722055123044450733735507 26583082684566676100603261)
        ·
          refine ⟨9968656006712503537726223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26583082684566676100603261 9968656006712503537726223)
          ·
            refine ⟨14952984010068755306589335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968656006712503537726223 14952984010068755306589335)
            ·
              refine ⟨22429476015103132959884003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14952984010068755306589335 22429476015103132959884003)
              ·
                refine ⟨33644214022654699439826005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22429476015103132959884003 33644214022654699439826005)
                ·
                  refine ⟨394268133077984759060461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33644214022654699439826005 394268133077984759060461)
                  ·
                    rfl

theorem cell23_6910510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_6910510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910510 prefixEnd_6910510 := by exact prefixLift 6910510
  have htrace : WordTrace (prefixWord ++ tailWord_6910510) baseStart_6910510 baseEnd_6910510 := by
    simpa [prefixWord, tailWord_6910510, baseEnd_6910510] using wordTrace_append hprefix tailTrace_6910510
  have hstable : (prefixWord ++ tailWord_6910510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910510).length < 2 ^ (prefixWord ++ tailWord_6910510).sum := by decide
  have hdescent : baseEnd_6910510 < baseStart_6910510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910540 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_6910540 : Nat := 118140960795 + 6910540 * 2 ^ 59
def prefixEnd_6910540 : Nat := 4983230072969 + 3 ^ 40 * 6910540 * 2
def baseEnd_6910540 : Nat := 1182809534040499238056337

theorem tailTrace_6910540 : CollatzResearch.WordTrace tailWord_6910540 prefixEnd_6910540 1182809534040499238056337 := by
  unfold tailWord_6910540
  simp only [CollatzResearch.WordTrace]
  refine ⟨126024050192150640557248537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168032066922867520742998049 126024050192150640557248537)
  ·
    refine ⟨94518037644112980417936403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126024050192150640557248537 94518037644112980417936403)
    ·
      refine ⟨141777056466169470626904605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94518037644112980417936403 141777056466169470626904605)
      ·
        refine ⟨53166396174813551485089227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141777056466169470626904605 53166396174813551485089227)
        ·
          refine ⟨79749594262220327227633841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53166396174813551485089227 79749594262220327227633841)
          ·
            refine ⟨59812195696665245420725381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79749594262220327227633841 59812195696665245420725381)
            ·
              refine ⟨11214786693124733516386009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59812195696665245420725381 11214786693124733516386009)
              ·
                refine ⟨8411090019843550137289507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11214786693124733516386009 8411090019843550137289507)
                ·
                  refine ⟨12616635029765325205934261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411090019843550137289507 12616635029765325205934261)
                  ·
                    refine ⟨1182809534040499238056337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12616635029765325205934261 1182809534040499238056337)
                    ·
                      rfl

theorem cell23_6910540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_6910540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910540 prefixEnd_6910540 := by exact prefixLift 6910540
  have htrace : WordTrace (prefixWord ++ tailWord_6910540) baseStart_6910540 baseEnd_6910540 := by
    simpa [prefixWord, tailWord_6910540, baseEnd_6910540] using wordTrace_append hprefix tailTrace_6910540
  have hstable : (prefixWord ++ tailWord_6910540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910540).length < 2 ^ (prefixWord ++ tailWord_6910540).sum := by decide
  have hdescent : baseEnd_6910540 < baseStart_6910540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910543 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_6910543 : Nat := 118140960795 + 6910543 * 2 ^ 59
def prefixEnd_6910543 : Nat := 4983230072969 + 3 ^ 40 * 6910543 * 2
def baseEnd_6910543 : Nat := 3548430142563461202431497

theorem tailTrace_6910543 : CollatzResearch.WordTrace tailWord_6910543 prefixEnd_6910543 3548430142563461202431497 := by
  unfold tailWord_6910543
  simp only [CollatzResearch.WordTrace]
  refine ⟨252048209803290412626856283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168032139868860275084570855 252048209803290412626856283)
  ·
    refine ⟨378072314704935618940284425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252048209803290412626856283 378072314704935618940284425)
    ·
      refine ⟨283554236028701714205213319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378072314704935618940284425 283554236028701714205213319)
      ·
        refine ⟨425331354043052571307819979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283554236028701714205213319 425331354043052571307819979)
        ·
          refine ⟨637997031064578856961729969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425331354043052571307819979 637997031064578856961729969)
          ·
            refine ⟨478497773298434142721297477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637997031064578856961729969 478497773298434142721297477)
            ·
              refine ⟨89718332493456401760243277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 478497773298434142721297477 89718332493456401760243277)
              ·
                refine ⟨33644374685046150660091229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89718332493456401760243277 33644374685046150660091229)
                ·
                  refine ⟨12616640506892306497534211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33644374685046150660091229 12616640506892306497534211)
                  ·
                    refine ⟨18924960760338459746301317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12616640506892306497534211 18924960760338459746301317)
                    ·
                      refine ⟨3548430142563461202431497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18924960760338459746301317 3548430142563461202431497)
                      ·
                        rfl

theorem cell23_6910543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_6910543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910543 prefixEnd_6910543 := by exact prefixLift 6910543
  have htrace : WordTrace (prefixWord ++ tailWord_6910543) baseStart_6910543 baseEnd_6910543 := by
    simpa [prefixWord, tailWord_6910543, baseEnd_6910543] using wordTrace_append hprefix tailTrace_6910543
  have hstable : (prefixWord ++ tailWord_6910543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910543).length < 2 ^ (prefixWord ++ tailWord_6910543).sum := by decide
  have hdescent : baseEnd_6910543 < baseStart_6910543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910560 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4]
def baseStart_6910560 : Nat := 118140960795 + 6910560 * 2 ^ 59
def prefixEnd_6910560 : Nat := 4983230072969 + 3 ^ 40 * 6910560 * 2
def baseEnd_6910560 : Nat := 3548438871734587635918919

theorem tailTrace_6910560 : CollatzResearch.WordTrace tailWord_6910560 prefixEnd_6910560 3548438871734587635918919 := by
  unfold tailWord_6910560
  simp only [CollatzResearch.WordTrace]
  refine ⟨126024414922114412265112567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168032553229485883020150089 126024414922114412265112567)
  ·
    refine ⟨189036622383171618397668851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126024414922114412265112567 189036622383171618397668851)
    ·
      refine ⟨283554933574757427596503277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189036622383171618397668851 283554933574757427596503277)
      ·
        refine ⟨106333100090534035348688729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283554933574757427596503277 106333100090534035348688729)
        ·
          refine ⟨79749825067900526511516547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106333100090534035348688729 79749825067900526511516547)
          ·
            refine ⟨119624737601850789767274821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79749825067900526511516547 119624737601850789767274821)
            ·
              refine ⟨22429638300347023081364029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119624737601850789767274821 22429638300347023081364029)
              ·
                refine ⟨8411114362630133655511511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22429638300347023081364029 8411114362630133655511511)
                ·
                  refine ⟨12616671543945200483267267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411114362630133655511511 12616671543945200483267267)
                  ·
                    refine ⟨18925007315917800724900901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12616671543945200483267267 18925007315917800724900901)
                    ·
                      refine ⟨3548438871734587635918919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18925007315917800724900901 3548438871734587635918919)
                      ·
                        rfl

theorem cell23_6910560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_6910560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910560 prefixEnd_6910560 := by exact prefixLift 6910560
  have htrace : WordTrace (prefixWord ++ tailWord_6910560) baseStart_6910560 baseEnd_6910560 := by
    simpa [prefixWord, tailWord_6910560, baseEnd_6910560] using wordTrace_append hprefix tailTrace_6910560
  have hstable : (prefixWord ++ tailWord_6910560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910560).length < 2 ^ (prefixWord ++ tailWord_6910560).sum := by decide
  have hdescent : baseEnd_6910560 < baseStart_6910560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910570 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_6910570 : Nat := 118140960795 + 6910570 * 2 ^ 59
def prefixEnd_6910570 : Nat := 4983230072969 + 3 ^ 40 * 6910570 * 2
def baseEnd_6910570 : Nat := 1182814668847044198931291

theorem tailTrace_6910570 : CollatzResearch.WordTrace tailWord_6910570 prefixEnd_6910570 1182814668847044198931291 := by
  unfold tailWord_6910570
  simp only [CollatzResearch.WordTrace]
  refine ⟨63012298643548149059522291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168032796382795064158726109 63012298643548149059522291)
  ·
    refine ⟨94518447965322223589283437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63012298643548149059522291 94518447965322223589283437)
    ·
      refine ⟨35444417986995833845981289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94518447965322223589283437 35444417986995833845981289)
      ·
        refine ⟨26583313490246875384485967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35444417986995833845981289 26583313490246875384485967)
        ·
          refine ⟨39874970235370313076728951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26583313490246875384485967 39874970235370313076728951)
          ·
            refine ⟨59812455353055469615093427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39874970235370313076728951 59812455353055469615093427)
            ·
              refine ⟨89718683029583204422640141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59812455353055469615093427 89718683029583204422640141)
              ·
                refine ⟨33644506136093701658490053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89718683029583204422640141 33644506136093701658490053)
                ·
                  refine ⟨6308344900517569060966885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33644506136093701658490053 6308344900517569060966885)
                  ·
                    refine ⟨1182814668847044198931291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6308344900517569060966885 1182814668847044198931291)
                    ·
                      rfl

theorem cell23_6910570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_6910570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910570 prefixEnd_6910570 := by exact prefixLift 6910570
  have htrace : WordTrace (prefixWord ++ tailWord_6910570) baseStart_6910570 baseEnd_6910570 := by
    simpa [prefixWord, tailWord_6910570, baseEnd_6910570] using wordTrace_append hprefix tailTrace_6910570
  have hstable : (prefixWord ++ tailWord_6910570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910570).length < 2 ^ (prefixWord ++ tailWord_6910570).sum := by decide
  have hdescent : baseEnd_6910570 < baseStart_6910570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910597 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_6910597 : Nat := 118140960795 + 6910597 * 2 ^ 59
def prefixEnd_6910597 : Nat := 4983230072969 + 3 ^ 40 * 6910597 * 2
def baseEnd_6910597 : Nat := 3548457870518803991156249

theorem tailTrace_6910597 : CollatzResearch.WordTrace tailWord_6910597 prefixEnd_6910597 3548457870518803991156249 := by
  unfold tailWord_6910597
  simp only [CollatzResearch.WordTrace]
  refine ⟨252050179345094779849322045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168033452896729853232881363 252050179345094779849322045)
  ·
    refine ⟨94518817254410542443495767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252050179345094779849322045 94518817254410542443495767)
    ·
      refine ⟨141778225881615813665243651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94518817254410542443495767 141778225881615813665243651)
      ·
        refine ⟨212667338822423720497865477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141778225881615813665243651 212667338822423720497865477)
        ·
          refine ⟨39875126029204447593349777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212667338822423720497865477 39875126029204447593349777)
          ·
            refine ⟨29906344521903335695012333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39875126029204447593349777 29906344521903335695012333)
            ·
              refine ⟨11214879195713750885629625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29906344521903335695012333 11214879195713750885629625)
              ·
                refine ⟨8411159396785313164222219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11214879195713750885629625 8411159396785313164222219)
                ·
                  refine ⟨12616739095177969746333329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411159396785313164222219 12616739095177969746333329)
                  ·
                    refine ⟨9462554321383477309749997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12616739095177969746333329 9462554321383477309749997)
                    ·
                      refine ⟨3548457870518803991156249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9462554321383477309749997 3548457870518803991156249)
                      ·
                        rfl

theorem cell23_6910597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_6910597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910597 prefixEnd_6910597 := by exact prefixLift 6910597
  have htrace : WordTrace (prefixWord ++ tailWord_6910597) baseStart_6910597 baseEnd_6910597 := by
    simpa [prefixWord, tailWord_6910597, baseEnd_6910597] using wordTrace_append hprefix tailTrace_6910597
  have hstable : (prefixWord ++ tailWord_6910597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910597).length < 2 ^ (prefixWord ++ tailWord_6910597).sum := by decide
  have hdescent : baseEnd_6910597 < baseStart_6910597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910633 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_6910633 : Nat := 118140960795 + 6910633 * 2 ^ 59
def prefixEnd_6910633 : Nat := 4983230072969 + 3 ^ 40 * 6910633 * 2
def baseEnd_6910633 : Nat := 3548476355822365850306083

theorem tailTrace_6910633 : CollatzResearch.WordTrace tailWord_6910633 prefixEnd_6910633 3548476355822365850306083 := by
  unfold tailWord_6910633
  simp only [CollatzResearch.WordTrace]
  refine ⟨252051492372964357997632553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168034328248642905331755035 252051492372964357997632553)
  ·
    refine ⟨189038619279723268498224415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252051492372964357997632553 189038619279723268498224415)
    ·
      refine ⟨283557928919584902747336623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189038619279723268498224415 283557928919584902747336623)
      ·
        refine ⟨425336893379377354121004935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283557928919584902747336623 425336893379377354121004935)
        ·
          refine ⟨638005340069066031181507403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425336893379377354121004935 638005340069066031181507403)
          ·
            refine ⟨957008010103599046772261105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638005340069066031181507403 957008010103599046772261105)
            ·
              refine ⟨717756007577699285079195829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957008010103599046772261105 717756007577699285079195829)
              ·
                refine ⟨67289625710409307976174609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717756007577699285079195829 67289625710409307976174609)
                ·
                  refine ⟨50467219282806980982130957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67289625710409307976174609 50467219282806980982130957)
                  ·
                    refine ⟨18925207231052617868299109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50467219282806980982130957 18925207231052617868299109)
                    ·
                      refine ⟨3548476355822365850306083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18925207231052617868299109 3548476355822365850306083)
                      ·
                        rfl

theorem cell23_6910633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_6910633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910633 prefixEnd_6910633 := by exact prefixLift 6910633
  have htrace : WordTrace (prefixWord ++ tailWord_6910633) baseStart_6910633 baseEnd_6910633 := by
    simpa [prefixWord, tailWord_6910633, baseEnd_6910633] using wordTrace_append hprefix tailTrace_6910633
  have hstable : (prefixWord ++ tailWord_6910633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910633).length < 2 ^ (prefixWord ++ tailWord_6910633).sum := by decide
  have hdescent : baseEnd_6910633 < baseStart_6910633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910634 : List Nat := [3, 1, 5, 2, 1, 2, 1, 8]
def baseStart_6910634 : Nat := 118140960795 + 6910634 * 2 ^ 59
def prefixEnd_6910634 : Nat := 4983230072969 + 3 ^ 40 * 6910634 * 2
def baseEnd_6910634 : Nat := 131425069233445198014577

theorem tailTrace_6910634 : CollatzResearch.WordTrace tailWord_6910634 prefixEnd_6910634 131425069233445198014577 := by
  unfold tailWord_6910634
  simp only [CollatzResearch.WordTrace]
  refine ⟨63012882211490183792104739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168034352563973823445612637 63012882211490183792104739)
  ·
    refine ⟨94519323317235275688157109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63012882211490183792104739 94519323317235275688157109)
    ·
      refine ⟨8861186560990807095764729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94519323317235275688157109 8861186560990807095764729)
      ·
        refine ⟨6645889920743105321823547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8861186560990807095764729 6645889920743105321823547)
        ·
          refine ⟨9968834881114657982735321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6645889920743105321823547 9968834881114657982735321)
          ·
            refine ⟨7476626160835993487051491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9968834881114657982735321 7476626160835993487051491)
            ·
              refine ⟨11214939241253990230577237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7476626160835993487051491 11214939241253990230577237)
              ·
                refine ⟨131425069233445198014577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11214939241253990230577237 131425069233445198014577)
                ·
                  rfl

theorem cell23_6910634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_6910634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910634 prefixEnd_6910634 := by exact prefixLift 6910634
  have htrace : WordTrace (prefixWord ++ tailWord_6910634) baseStart_6910634 baseEnd_6910634 := by
    simpa [prefixWord, tailWord_6910634, baseEnd_6910634] using wordTrace_append hprefix tailTrace_6910634
  have hstable : (prefixWord ++ tailWord_6910634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910634).length < 2 ^ (prefixWord ++ tailWord_6910634).sum := by decide
  have hdescent : baseEnd_6910634 < baseStart_6910634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910643 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 1, 8]
def baseStart_6910643 : Nat := 118140960795 + 6910643 * 2 ^ 59
def prefixEnd_6910643 : Nat := 4983230072969 + 3 ^ 40 * 6910643 * 2
def baseEnd_6910643 : Nat := 1182827163542970270393679

theorem tailTrace_6910643 : CollatzResearch.WordTrace tailWord_6910643 prefixEnd_6910643 1182827163542970270393679 := by
  unfold tailWord_6910643
  simp only [CollatzResearch.WordTrace]
  refine ⟨252051857102928129705496583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168034571401952086470331055 252051857102928129705496583)
  ·
    refine ⟨378077785654392194558244875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252051857102928129705496583 378077785654392194558244875)
    ·
      refine ⟨567116678481588291837367313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378077785654392194558244875 567116678481588291837367313)
      ·
        refine ⟨425337508861191218878025485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567116678481588291837367313 425337508861191218878025485)
        ·
          refine ⟨159501565822946707079259557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425337508861191218878025485 159501565822946707079259557)
          ·
            refine ⟨29906543591802507577361167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159501565822946707079259557 29906543591802507577361167)
            ·
              refine ⟨44859815387703761366041751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29906543591802507577361167 44859815387703761366041751)
              ·
                refine ⟨67289723081555642049062627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44859815387703761366041751 67289723081555642049062627)
                ·
                  refine ⟨100934584622333463073593941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67289723081555642049062627 100934584622333463073593941)
                  ·
                    refine ⟨1182827163542970270393679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100934584622333463073593941 1182827163542970270393679)
                    ·
                      rfl

theorem cell23_6910643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 8].length) (baseStart_6910643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910643 prefixEnd_6910643 := by exact prefixLift 6910643
  have htrace : WordTrace (prefixWord ++ tailWord_6910643) baseStart_6910643 baseEnd_6910643 := by
    simpa [prefixWord, tailWord_6910643, baseEnd_6910643] using wordTrace_append hprefix tailTrace_6910643
  have hstable : (prefixWord ++ tailWord_6910643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910643).length < 2 ^ (prefixWord ++ tailWord_6910643).sum := by decide
  have hdescent : baseEnd_6910643 < baseStart_6910643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910654 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_6910654 : Nat := 118140960795 + 6910654 * 2 ^ 59
def prefixEnd_6910654 : Nat := 4983230072969 + 3 ^ 40 * 6910654 * 2
def baseEnd_6910654 : Nat := 3548487138916110268143487

theorem tailTrace_6910654 : CollatzResearch.WordTrace tailWord_6910654 prefixEnd_6910654 3548487138916110268143487 := by
  unfold tailWord_6910654
  simp only [CollatzResearch.WordTrace]
  refine ⟨31506532288236034823018377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168034838870592185722764677 31506532288236034823018377)
  ·
    refine ⟨23629899216177026117263783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31506532288236034823018377 23629899216177026117263783)
    ·
      refine ⟨35444848824265539175895675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23629899216177026117263783 35444848824265539175895675)
      ·
        refine ⟨53167273236398308763843513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35444848824265539175895675 53167273236398308763843513)
        ·
          refine ⟨39875454927298731572882635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53167273236398308763843513 39875454927298731572882635)
          ·
            refine ⟨59813182390948097359323953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39875454927298731572882635 59813182390948097359323953)
            ·
              refine ⟨44859886793211073019492965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59813182390948097359323953 44859886793211073019492965)
              ·
                refine ⟨8411228773727076191154931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44859886793211073019492965 8411228773727076191154931)
                ·
                  refine ⟨12616843160590614286732397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411228773727076191154931 12616843160590614286732397)
                  ·
                    refine ⟨4731316185221480357524649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12616843160590614286732397 4731316185221480357524649)
                    ·
                      refine ⟨3548487138916110268143487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731316185221480357524649 3548487138916110268143487)
                      ·
                        rfl

theorem cell23_6910654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_6910654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910654 prefixEnd_6910654 := by exact prefixLift 6910654
  have htrace : WordTrace (prefixWord ++ tailWord_6910654) baseStart_6910654 baseEnd_6910654 := by
    simpa [prefixWord, tailWord_6910654, baseEnd_6910654] using wordTrace_append hprefix tailTrace_6910654
  have hstable : (prefixWord ++ tailWord_6910654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910654).length < 2 ^ (prefixWord ++ tailWord_6910654).sum := by decide
  have hdescent : baseEnd_6910654 < baseStart_6910654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910662 : List Nat := [6, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6910662 : Nat := 118140960795 + 6910662 * 2 ^ 59
def prefixEnd_6910662 : Nat := 4983230072969 + 3 ^ 40 * 6910662 * 2
def baseEnd_6910662 : Nat := 3548491246761346236843451

theorem tailTrace_6910662 : CollatzResearch.WordTrace tailWord_6910662 prefixEnd_6910662 3548491246761346236843451 := by
  unfold tailWord_6910662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7876642190308102998451195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168035033393239530633625493 7876642190308102998451195)
  ·
    refine ⟨11814963285462154497676793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7876642190308102998451195 11814963285462154497676793)
    ·
      refine ⟨8861222464096615873257595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11814963285462154497676793 8861222464096615873257595)
      ·
        refine ⟨13291833696144923809886393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861222464096615873257595 13291833696144923809886393)
        ·
          refine ⟨9968875272108692857414795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13291833696144923809886393 9968875272108692857414795)
          ·
            refine ⟨14953312908163039286122193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968875272108692857414795 14953312908163039286122193)
            ·
              refine ⟨11214984681122279464591645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14953312908163039286122193 11214984681122279464591645)
              ·
                refine ⟨4205619255420854799221867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11214984681122279464591645 4205619255420854799221867)
                ·
                  refine ⟨6308428883131282198832801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205619255420854799221867 6308428883131282198832801)
                  ·
                    refine ⟨4731321662348461649124601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6308428883131282198832801 4731321662348461649124601)
                    ·
                      refine ⟨3548491246761346236843451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731321662348461649124601 3548491246761346236843451)
                      ·
                        rfl

theorem cell23_6910662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6910662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910662 prefixEnd_6910662 := by exact prefixLift 6910662
  have htrace : WordTrace (prefixWord ++ tailWord_6910662) baseStart_6910662 baseEnd_6910662 := by
    simpa [prefixWord, tailWord_6910662, baseEnd_6910662] using wordTrace_append hprefix tailTrace_6910662
  have hstable : (prefixWord ++ tailWord_6910662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910662).length < 2 ^ (prefixWord ++ tailWord_6910662).sum := by decide
  have hdescent : baseEnd_6910662 < baseStart_6910662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910673 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 9]
def baseStart_6910673 : Nat := 118140960795 + 6910673 * 2 ^ 59
def prefixEnd_6910673 : Nat := 4983230072969 + 3 ^ 40 * 6910673 * 2
def baseEnd_6910673 : Nat := 394277432783171743756211

theorem tailTrace_6910673 : CollatzResearch.WordTrace tailWord_6910673 prefixEnd_6910673 394277432783171743756211 := by
  unfold tailWord_6910673
  simp only [CollatzResearch.WordTrace]
  refine ⟨252052951292819444829088673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168035300861879629886059115 252052951292819444829088673)
  ·
    refine ⟨189039713469614583621816505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252052951292819444829088673 189039713469614583621816505)
    ·
      refine ⟨141779785102210937716362379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189039713469614583621816505 141779785102210937716362379)
      ·
        refine ⟨212669677653316406574543569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141779785102210937716362379 212669677653316406574543569)
        ·
          refine ⟨159502258239987304930907677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212669677653316406574543569 159502258239987304930907677)
          ·
            refine ⟨59813346839995239349090379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159502258239987304930907677 59813346839995239349090379)
            ·
              refine ⟨89720020259992859023635569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59813346839995239349090379 89720020259992859023635569)
              ·
                refine ⟨67290015194994644267726677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89720020259992859023635569 67290015194994644267726677)
                ·
                  refine ⟨394277432783171743756211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67290015194994644267726677 394277432783171743756211)
                  ·
                    rfl

theorem cell23_6910673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 9].length) (baseStart_6910673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910673 prefixEnd_6910673 := by exact prefixLift 6910673
  have htrace : WordTrace (prefixWord ++ tailWord_6910673) baseStart_6910673 baseEnd_6910673 := by
    simpa [prefixWord, tailWord_6910673, baseEnd_6910673] using wordTrace_append hprefix tailTrace_6910673
  have hstable : (prefixWord ++ tailWord_6910673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910673).length < 2 ^ (prefixWord ++ tailWord_6910673).sum := by decide
  have hdescent : baseEnd_6910673 < baseStart_6910673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910680 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_6910680 : Nat := 118140960795 + 6910680 * 2 ^ 59
def prefixEnd_6910680 : Nat := 4983230072969 + 3 ^ 40 * 6910680 * 2
def baseEnd_6910680 : Nat := 3548500489413127166418367

theorem tailTrace_6910680 : CollatzResearch.WordTrace tailWord_6910680 prefixEnd_6910680 3548500489413127166418367 := by
  unfold tailWord_6910680
  simp only [CollatzResearch.WordTrace]
  refine ⟨126026603301897042512296747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168035471069196056683062329 126026603301897042512296747)
  ·
    refine ⟨189039904952845563768445121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126026603301897042512296747 189039904952845563768445121)
    ·
      refine ⟨141779928714634172826333841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189039904952845563768445121 141779928714634172826333841)
      ·
        refine ⟨106334946535975629619750381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141779928714634172826333841 106334946535975629619750381)
        ·
          refine ⟨39875604950990861107406393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106334946535975629619750381 39875604950990861107406393)
          ·
            refine ⟨29906703713243145830554795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39875604950990861107406393 29906703713243145830554795)
            ·
              refine ⟨44860055569864718745832193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29906703713243145830554795 44860055569864718745832193)
              ·
                refine ⟨33645041677398539059374145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44860055569864718745832193 33645041677398539059374145)
                ·
                  refine ⟨25233781258048904294530609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33645041677398539059374145 25233781258048904294530609)
                  ·
                    refine ⟨18925335943536678220897957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25233781258048904294530609 18925335943536678220897957)
                    ·
                      refine ⟨3548500489413127166418367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18925335943536678220897957 3548500489413127166418367)
                      ·
                        rfl

theorem cell23_6910680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_6910680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910680 prefixEnd_6910680 := by exact prefixLift 6910680
  have htrace : WordTrace (prefixWord ++ tailWord_6910680) baseStart_6910680 baseEnd_6910680 := by
    simpa [prefixWord, tailWord_6910680, baseEnd_6910680] using wordTrace_append hprefix tailTrace_6910680
  have hstable : (prefixWord ++ tailWord_6910680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910680).length < 2 ^ (prefixWord ++ tailWord_6910680).sum := by decide
  have hdescent : baseEnd_6910680 < baseStart_6910680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910730 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_6910730 : Nat := 118140960795 + 6910730 * 2 ^ 59
def prefixEnd_6910730 : Nat := 4983230072969 + 3 ^ 40 * 6910730 * 2
def baseEnd_6910730 : Nat := 3548526163445851970793137

theorem tailTrace_6910730 : CollatzResearch.WordTrace tailWord_6910730 prefixEnd_6910730 3548526163445851970793137 := by
  unfold tailWord_6910730
  simp only [CollatzResearch.WordTrace]
  refine ⟨63013757563403235890978411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168036686835741962375942429 63013757563403235890978411)
  ·
    refine ⟨94520636345104853836467617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63013757563403235890978411 94520636345104853836467617)
    ·
      refine ⟨70890477258828640377350713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94520636345104853836467617 70890477258828640377350713)
      ·
        refine ⟨53167857944121480283013035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70890477258828640377350713 53167857944121480283013035)
        ·
          refine ⟨79751786916182220424519553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53167857944121480283013035 79751786916182220424519553)
          ·
            refine ⟨59813840187136665318389665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79751786916182220424519553 59813840187136665318389665)
            ·
              refine ⟨44860380140352498988792249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59813840187136665318389665 44860380140352498988792249)
              ·
                refine ⟨33645285105264374241594187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44860380140352498988792249 33645285105264374241594187)
                ·
                  refine ⟨50467927657896561362391281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33645285105264374241594187 50467927657896561362391281)
                  ·
                    refine ⟨37850945743422421021793461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50467927657896561362391281 37850945743422421021793461)
                    ·
                      refine ⟨3548526163445851970793137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37850945743422421021793461 3548526163445851970793137)
                      ·
                        rfl

theorem cell23_6910730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_6910730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910730 prefixEnd_6910730 := by exact prefixLift 6910730
  have htrace : WordTrace (prefixWord ++ tailWord_6910730) baseStart_6910730 baseEnd_6910730 := by
    simpa [prefixWord, tailWord_6910730, baseEnd_6910730] using wordTrace_append hprefix tailTrace_6910730
  have hstable : (prefixWord ++ tailWord_6910730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910730).length < 2 ^ (prefixWord ++ tailWord_6910730).sum := by decide
  have hdescent : baseEnd_6910730 < baseStart_6910730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910757 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 1, 6, 2]
def baseStart_6910757 : Nat := 118140960795 + 6910757 * 2 ^ 59
def prefixEnd_6910757 : Nat := 4983230072969 + 3 ^ 40 * 6910757 * 2
def baseEnd_6910757 : Nat := 3548540027423523365155513

theorem tailTrace_6910757 : CollatzResearch.WordTrace tailWord_6910757 prefixEnd_6910757 3548540027423523365155513 := by
  unfold tailWord_6910757
  simp only [CollatzResearch.WordTrace]
  refine ⟨252056015024515127175146525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168037343349676751450097683 252056015024515127175146525)
  ·
    refine ⟨94521005634193172690679947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252056015024515127175146525 94521005634193172690679947)
    ·
      refine ⟨141781508451289759036019921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94521005634193172690679947 141781508451289759036019921)
      ·
        refine ⟨106336131338467319277014941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141781508451289759036019921 106336131338467319277014941)
        ·
          refine ⟨39876049251925244728880603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106336131338467319277014941 39876049251925244728880603)
          ·
            refine ⟨59814073877887867093320905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39876049251925244728880603 59814073877887867093320905)
            ·
              refine ⟨44860555408415900319990679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59814073877887867093320905 44860555408415900319990679)
              ·
                refine ⟨67290833112623850479986019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44860555408415900319990679 67290833112623850479986019)
                ·
                  refine ⟨100936249668935775719979029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67290833112623850479986019 100936249668935775719979029)
                  ·
                    refine ⟨4731386703231364486874017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100936249668935775719979029 4731386703231364486874017)
                    ·
                      refine ⟨3548540027423523365155513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731386703231364486874017 3548540027423523365155513)
                      ·
                        rfl

theorem cell23_6910757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_6910757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910757 prefixEnd_6910757 := by exact prefixLift 6910757
  have htrace : WordTrace (prefixWord ++ tailWord_6910757) baseStart_6910757 baseEnd_6910757 := by
    simpa [prefixWord, tailWord_6910757, baseEnd_6910757] using wordTrace_append hprefix tailTrace_6910757
  have hstable : (prefixWord ++ tailWord_6910757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910757).length < 2 ^ (prefixWord ++ tailWord_6910757).sum := by decide
  have hdescent : baseEnd_6910757 < baseStart_6910757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910801 : List Nat := [1, 2, 2, 1, 6, 1, 1, 4, 1, 4]
def baseStart_6910801 : Nat := 118140960795 + 6910801 * 2 ^ 59
def prefixEnd_6910801 : Nat := 4983230072969 + 3 ^ 40 * 6910801 * 2
def baseEnd_6910801 : Nat := 1182854206857440397668437

theorem tailTrace_6910801 : CollatzResearch.WordTrace tailWord_6910801 prefixEnd_6910801 1182854206857440397668437 := by
  unfold tailWord_6910801
  simp only [CollatzResearch.WordTrace]
  refine ⟨252057619836355722689748257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168038413224237148459832171 252057619836355722689748257)
  ·
    refine ⟨189043214877266792017311193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252057619836355722689748257 189043214877266792017311193)
    ·
      refine ⟨141782411157950094012983395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189043214877266792017311193 141782411157950094012983395)
      ·
        refine ⟨212673616736925141019475093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141782411157950094012983395 212673616736925141019475093)
        ·
          refine ⟨9969075784543365985287895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 212673616736925141019475093 9969075784543365985287895)
          ·
            refine ⟨14953613676815048977931843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9969075784543365985287895 14953613676815048977931843)
            ·
              refine ⟨22430420515222573466897765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14953613676815048977931843 22430420515222573466897765)
              ·
                refine ⟨4205703846604232525043331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22430420515222573466897765 4205703846604232525043331)
                ·
                  refine ⟨6308555769906348787564997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205703846604232525043331 6308555769906348787564997)
                  ·
                    refine ⟨1182854206857440397668437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6308555769906348787564997 1182854206857440397668437)
                    ·
                      rfl

theorem cell23_6910801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_6910801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910801 prefixEnd_6910801 := by exact prefixLift 6910801
  have htrace : WordTrace (prefixWord ++ tailWord_6910801) baseStart_6910801 baseEnd_6910801 := by
    simpa [prefixWord, tailWord_6910801, baseEnd_6910801] using wordTrace_append hprefix tailTrace_6910801
  have hstable : (prefixWord ++ tailWord_6910801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910801).length < 2 ^ (prefixWord ++ tailWord_6910801).sum := by decide
  have hdescent : baseEnd_6910801 < baseStart_6910801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910824 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6910824 : Nat := 118140960795 + 6910824 * 2 ^ 59
def prefixEnd_6910824 : Nat := 4983230072969 + 3 ^ 40 * 6910824 * 2
def baseEnd_6910824 : Nat := 3548574430627374603017705

theorem tailTrace_6910824 : CollatzResearch.WordTrace tailWord_6910824 prefixEnd_6910824 3548574430627374603017705 := by
  unfold tailWord_6910824
  simp only [CollatzResearch.WordTrace]
  refine ⟨126029229357636198808917763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168038972476848265078557017 126029229357636198808917763)
  ·
    refine ⟨189043844036454298213376645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126029229357636198808917763 189043844036454298213376645)
    ·
      refine ⟨35445720756835180915008121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189043844036454298213376645 35445720756835180915008121)
      ·
        refine ⟨26584290567626385686256091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35445720756835180915008121 26584290567626385686256091)
        ·
          refine ⟨39876435851439578529384137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26584290567626385686256091 39876435851439578529384137)
          ·
            refine ⟨29907326888579683897038103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39876435851439578529384137 29907326888579683897038103)
            ·
              refine ⟨44860990332869525845557155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29907326888579683897038103 44860990332869525845557155)
              ·
                refine ⟨67291485499304288768335733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44860990332869525845557155 67291485499304288768335733)
                ·
                  refine ⟨6308576765559777072031475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67291485499304288768335733 6308576765559777072031475)
                  ·
                    refine ⟨9462865148339665608047213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6308576765559777072031475 9462865148339665608047213)
                    ·
                      refine ⟨3548574430627374603017705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9462865148339665608047213 3548574430627374603017705)
                      ·
                        rfl

theorem cell23_6910824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6910824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910824 prefixEnd_6910824 := by exact prefixLift 6910824
  have htrace : WordTrace (prefixWord ++ tailWord_6910824) baseStart_6910824 baseEnd_6910824 := by
    simpa [prefixWord, tailWord_6910824, baseEnd_6910824] using wordTrace_append hprefix tailTrace_6910824
  have hstable : (prefixWord ++ tailWord_6910824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910824).length < 2 ^ (prefixWord ++ tailWord_6910824).sum := by decide
  have hdescent : baseEnd_6910824 < baseStart_6910824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910840 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 3, 6]
def baseStart_6910840 : Nat := 118140960795 + 6910840 * 2 ^ 59
def prefixEnd_6910840 : Nat := 4983230072969 + 3 ^ 40 * 6910840 * 2
def baseEnd_6910840 : Nat := 1182860882105948846805877

theorem tailTrace_6910840 : CollatzResearch.WordTrace tailWord_6910840 prefixEnd_6910840 1182860882105948846805877 := by
  unfold tailWord_6910840
  simp only [CollatzResearch.WordTrace]
  refine ⟨126029521141607216175208987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168039361522142954900278649 126029521141607216175208987)
  ·
    refine ⟨189044281712410824262813481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126029521141607216175208987 189044281712410824262813481)
    ·
      refine ⟨141783211284308118197110111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189044281712410824262813481 141783211284308118197110111)
      ·
        refine ⟨212674816926462177295665167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141783211284308118197110111 212674816926462177295665167)
        ·
          refine ⟨319012225389693265943497751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212674816926462177295665167 319012225389693265943497751)
          ·
            refine ⟨478518338084539898915246627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319012225389693265943497751 478518338084539898915246627)
            ·
              refine ⟨717777507126809848372869941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478518338084539898915246627 717777507126809848372869941)
              ·
                refine ⟨67291641293138423284956557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717777507126809848372869941 67291641293138423284956557)
                ·
                  refine ⟨25234365484926908731858709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67291641293138423284956557 25234365484926908731858709)
                  ·
                    refine ⟨1182860882105948846805877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25234365484926908731858709 1182860882105948846805877)
                    ·
                      rfl

theorem cell23_6910840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_6910840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910840 prefixEnd_6910840 := by exact prefixLift 6910840
  have htrace : WordTrace (prefixWord ++ tailWord_6910840) baseStart_6910840 baseEnd_6910840 := by
    simpa [prefixWord, tailWord_6910840, baseEnd_6910840] using wordTrace_append hprefix tailTrace_6910840
  have hstable : (prefixWord ++ tailWord_6910840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910840).length < 2 ^ (prefixWord ++ tailWord_6910840).sum := by decide
  have hdescent : baseEnd_6910840 < baseStart_6910840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910841 : List Nat := [1, 2, 1, 3, 2, 3, 1, 5, 1, 1, 3]
def baseStart_6910841 : Nat := 118140960795 + 6910841 * 2 ^ 59
def prefixEnd_6910841 : Nat := 4983230072969 + 3 ^ 40 * 6910841 * 2
def baseEnd_6910841 : Nat := 3548583159798501036505127

theorem tailTrace_6910841 : CollatzResearch.WordTrace tailWord_6910841 prefixEnd_6910841 3548583159798501036505127 := by
  unfold tailWord_6910841
  simp only [CollatzResearch.WordTrace]
  refine ⟨252059078756210809521204377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168039385837473873014136251 252059078756210809521204377)
  ·
    refine ⟨189044309067158107140903283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252059078756210809521204377 189044309067158107140903283)
    ·
      refine ⟨283566463600737160711354925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189044309067158107140903283 283566463600737160711354925)
      ·
        refine ⟨106337423850276435266758097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283566463600737160711354925 106337423850276435266758097)
        ·
          refine ⟨79753067887707326450068573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106337423850276435266758097 79753067887707326450068573)
          ·
            refine ⟨29907400457890247418775715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79753067887707326450068573 29907400457890247418775715)
            ·
              refine ⟨44861100686835371128163573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29907400457890247418775715 44861100686835371128163573)
              ·
                refine ⟨4205728189390816043265335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44861100686835371128163573 4205728189390816043265335)
                ·
                  refine ⟨6308592284086224064898003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205728189390816043265335 6308592284086224064898003)
                  ·
                    refine ⟨9462888426129336097347005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6308592284086224064898003 9462888426129336097347005)
                    ·
                      refine ⟨3548583159798501036505127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9462888426129336097347005 3548583159798501036505127)
                      ·
                        rfl

theorem cell23_6910841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_6910841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910841 prefixEnd_6910841 := by exact prefixLift 6910841
  have htrace : WordTrace (prefixWord ++ tailWord_6910841) baseStart_6910841 baseEnd_6910841 := by
    simpa [prefixWord, tailWord_6910841, baseEnd_6910841] using wordTrace_append hprefix tailTrace_6910841
  have hstable : (prefixWord ++ tailWord_6910841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910841).length < 2 ^ (prefixWord ++ tailWord_6910841).sum := by decide
  have hdescent : baseEnd_6910841 < baseStart_6910841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910858 : List Nat := [3, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_6910858 : Nat := 118140960795 + 6910858 * 2 ^ 59
def prefixEnd_6910858 : Nat := 4983230072969 + 3 ^ 40 * 6910858 * 2
def baseEnd_6910858 : Nat := 3548591888969627469992549

theorem tailTrace_6910858 : CollatzResearch.WordTrace tailWord_6910858 prefixEnd_6910858 3548591888969627469992549 := by
  unfold tailWord_6910858
  simp only [CollatzResearch.WordTrace]
  refine ⟨63014924699287305356143307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168039799198099480949715485 63014924699287305356143307)
  ·
    refine ⟨94522387048930958034214961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63014924699287305356143307 94522387048930958034214961)
    ·
      refine ⟨70891790286698218525661221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94522387048930958034214961 70891790286698218525661221)
      ·
        refine ⟨13292210678755915973561479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70891790286698218525661221 13292210678755915973561479)
        ·
          refine ⟨19938316018133873960342219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13292210678755915973561479 19938316018133873960342219)
          ·
            refine ⟨29907474027200810940513329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19938316018133873960342219 29907474027200810940513329)
            ·
              refine ⟨22430605520400608205384997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29907474027200810940513329 22430605520400608205384997)
              ·
                refine ⟨4205738535075114038509687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22430605520400608205384997 4205738535075114038509687)
                ·
                  refine ⟨6308607802612671057764531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205738535075114038509687 6308607802612671057764531)
                  ·
                    refine ⟨9462911703919006586646797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6308607802612671057764531 9462911703919006586646797)
                    ·
                      refine ⟨3548591888969627469992549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9462911703919006586646797 3548591888969627469992549)
                      ·
                        rfl

theorem cell23_6910858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_6910858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910858 prefixEnd_6910858 := by exact prefixLift 6910858
  have htrace : WordTrace (prefixWord ++ tailWord_6910858) baseStart_6910858 baseEnd_6910858 := by
    simpa [prefixWord, tailWord_6910858, baseEnd_6910858] using wordTrace_append hprefix tailTrace_6910858
  have hstable : (prefixWord ++ tailWord_6910858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910858).length < 2 ^ (prefixWord ++ tailWord_6910858).sum := by decide
  have hdescent : baseEnd_6910858 < baseStart_6910858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910867 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 3]
def baseStart_6910867 : Nat := 118140960795 + 6910867 * 2 ^ 59
def prefixEnd_6910867 : Nat := 4983230072969 + 3 ^ 40 * 6910867 * 2
def baseEnd_6910867 : Nat := 3548596510295517934780007

theorem tailTrace_6910867 : CollatzResearch.WordTrace tailWord_6910867 prefixEnd_6910867 3548596510295517934780007 := by
  unfold tailWord_6910867
  simp only [CollatzResearch.WordTrace]
  refine ⟨252060027054116615961650855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168040018036077743974433903 252060027054116615961650855)
  ·
    refine ⟨378090040581174923942476283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252060027054116615961650855 378090040581174923942476283)
    ·
      refine ⟨567135060871762385913714425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378090040581174923942476283 567135060871762385913714425)
      ·
        refine ⟨425351295653821789435285819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567135060871762385913714425 425351295653821789435285819)
        ·
          refine ⟨638026943480732684152928729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425351295653821789435285819 638026943480732684152928729)
          ·
            refine ⟨478520207610549513114696547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638026943480732684152928729 478520207610549513114696547)
            ·
              refine ⟨717780311415824269672044821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478520207610549513114696547 717780311415824269672044821)
              ·
                refine ⟨33645952097616762640877101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 717780311415824269672044821 33645952097616762640877101)
                ·
                  refine ⟨12617232036606285990328913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33645952097616762640877101 12617232036606285990328913)
                  ·
                    refine ⟨9462924027454714492746685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12617232036606285990328913 9462924027454714492746685)
                    ·
                      refine ⟨3548596510295517934780007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9462924027454714492746685 3548596510295517934780007)
                      ·
                        rfl

theorem cell23_6910867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_6910867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910867 prefixEnd_6910867 := by exact prefixLift 6910867
  have htrace : WordTrace (prefixWord ++ tailWord_6910867) baseStart_6910867 baseEnd_6910867 := by
    simpa [prefixWord, tailWord_6910867, baseEnd_6910867] using wordTrace_append hprefix tailTrace_6910867
  have hstable : (prefixWord ++ tailWord_6910867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910867).length < 2 ^ (prefixWord ++ tailWord_6910867).sum := by decide
  have hdescent : baseEnd_6910867 < baseStart_6910867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910877 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_6910877 : Nat := 118140960795 + 6910877 * 2 ^ 59
def prefixEnd_6910877 : Nat := 4983230072969 + 3 ^ 40 * 6910877 * 2
def baseEnd_6910877 : Nat := 3548601645102062895654961

theorem tailTrace_6910877 : CollatzResearch.WordTrace tailWord_6910877 prefixEnd_6910877 3548601645102062895654961 := by
  unfold tailWord_6910877
  simp only [CollatzResearch.WordTrace]
  refine ⟨252060391784080387669514885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168040261189386925113009923 252060391784080387669514885)
  ·
    refine ⟨47261323459515072688034041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252060391784080387669514885 47261323459515072688034041)
    ·
      refine ⟨35445992594636304516025531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47261323459515072688034041 35445992594636304516025531)
      ·
        refine ⟨53168988891954456774038297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35445992594636304516025531 53168988891954456774038297)
        ·
          refine ⟨39876741668965842580528723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53168988891954456774038297 39876741668965842580528723)
          ·
            refine ⟨59815112503448763870793085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39876741668965842580528723 59815112503448763870793085)
            ·
              refine ⟨22430667188793286451547407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59815112503448763870793085 22430667188793286451547407)
              ·
                refine ⟨33646000783189929677321111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22430667188793286451547407 33646000783189929677321111)
                ·
                  refine ⟨50469001174784894515981667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33646000783189929677321111 50469001174784894515981667)
                  ·
                    refine ⟨75703501762177341773972501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50469001174784894515981667 75703501762177341773972501)
                    ·
                      refine ⟨3548601645102062895654961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75703501762177341773972501 3548601645102062895654961)
                      ·
                        rfl

theorem cell23_6910877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_6910877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910877 prefixEnd_6910877 := by exact prefixLift 6910877
  have htrace : WordTrace (prefixWord ++ tailWord_6910877) baseStart_6910877 baseEnd_6910877 := by
    simpa [prefixWord, tailWord_6910877, baseEnd_6910877] using wordTrace_append hprefix tailTrace_6910877
  have hstable : (prefixWord ++ tailWord_6910877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910877).length < 2 ^ (prefixWord ++ tailWord_6910877).sum := by decide
  have hdescent : baseEnd_6910877 < baseStart_6910877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910881 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6910881 : Nat := 118140960795 + 6910881 * 2 ^ 59
def prefixEnd_6910881 : Nat := 4983230072969 + 3 ^ 40 * 6910881 * 2
def baseEnd_6910881 : Nat := 3548603699024680880004943

theorem tailTrace_6910881 : CollatzResearch.WordTrace tailWord_6910881 prefixEnd_6910881 3548603699024680880004943 := by
  unfold tailWord_6910881
  simp only [CollatzResearch.WordTrace]
  refine ⟨252060537676065896352660497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168040358450710597568440331 252060537676065896352660497)
  ·
    refine ⟨189045403257049422264495373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252060537676065896352660497 189045403257049422264495373)
    ·
      refine ⟨70892026221393533349185765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189045403257049422264495373 70892026221393533349185765)
      ·
        refine ⟨13292254916511287502972331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70892026221393533349185765 13292254916511287502972331)
        ·
          refine ⟨19938382374766931254458497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13292254916511287502972331 19938382374766931254458497)
          ·
            refine ⟨14953786781075198440843873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19938382374766931254458497 14953786781075198440843873)
            ·
              refine ⟨11215340085806398830632905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14953786781075198440843873 11215340085806398830632905)
              ·
                refine ⟨8411505064354799122974679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11215340085806398830632905 8411505064354799122974679)
                ·
                  refine ⟨12617257596532198684462019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411505064354799122974679 12617257596532198684462019)
                  ·
                    refine ⟨18925886394798298026693029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12617257596532198684462019 18925886394798298026693029)
                    ·
                      refine ⟨3548603699024680880004943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18925886394798298026693029 3548603699024680880004943)
                      ·
                        rfl

theorem cell23_6910881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6910881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910881 prefixEnd_6910881 := by exact prefixLift 6910881
  have htrace : WordTrace (prefixWord ++ tailWord_6910881) baseStart_6910881 baseEnd_6910881 := by
    simpa [prefixWord, tailWord_6910881, baseEnd_6910881] using wordTrace_append hprefix tailTrace_6910881
  have hstable : (prefixWord ++ tailWord_6910881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910881).length < 2 ^ (prefixWord ++ tailWord_6910881).sum := by decide
  have hdescent : baseEnd_6910881 < baseStart_6910881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910902 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6910902 : Nat := 118140960795 + 6910902 * 2 ^ 59
def prefixEnd_6910902 : Nat := 4983230072969 + 3 ^ 40 * 6910902 * 2
def baseEnd_6910902 : Nat := 3548614482118425297842347

theorem tailTrace_6910902 : CollatzResearch.WordTrace tailWord_6910902 prefixEnd_6910902 3548614482118425297842347 := by
  unfold tailWord_6910902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15753831475561863558698435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168040869072659877959449973 15753831475561863558698435)
  ·
    refine ⟨23630747213342795338047653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15753831475561863558698435 23630747213342795338047653)
    ·
      refine ⟨4430765102501774125883935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23630747213342795338047653 4430765102501774125883935)
      ·
        refine ⟨6646147653752661188825903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4430765102501774125883935 6646147653752661188825903)
        ·
          refine ⟨9969221480628991783238855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6646147653752661188825903 9969221480628991783238855)
          ·
            refine ⟨14953832220943487674858283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9969221480628991783238855 14953832220943487674858283)
            ·
              refine ⟨22430748331415231512287425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14953832220943487674858283 22430748331415231512287425)
              ·
                refine ⟨16823061248561423634215569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22430748331415231512287425 16823061248561423634215569)
                ·
                  refine ⟨12617295936421067725661677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16823061248561423634215569 12617295936421067725661677)
                  ·
                    refine ⟨4731485976157900397123129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12617295936421067725661677 4731485976157900397123129)
                    ·
                      refine ⟨3548614482118425297842347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731485976157900397123129 3548614482118425297842347)
                      ·
                        rfl

theorem cell23_6910902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6910902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910902 prefixEnd_6910902 := by exact prefixLift 6910902
  have htrace : WordTrace (prefixWord ++ tailWord_6910902) baseStart_6910902 baseEnd_6910902 := by
    simpa [prefixWord, tailWord_6910902, baseEnd_6910902] using wordTrace_append hprefix tailTrace_6910902
  have hstable : (prefixWord ++ tailWord_6910902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910902).length < 2 ^ (prefixWord ++ tailWord_6910902).sum := by decide
  have hdescent : baseEnd_6910902 < baseStart_6910902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910984 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_6910984 : Nat := 118140960795 + 6910984 * 2 ^ 59
def prefixEnd_6910984 : Nat := 4983230072969 + 3 ^ 40 * 6910984 * 2
def baseEnd_6910984 : Nat := 3548656587532093977016969

theorem tailTrace_6910984 : CollatzResearch.WordTrace tailWord_6910984 prefixEnd_6910984 3548656587532093977016969 := by
  unfold tailWord_6910984
  simp only [CollatzResearch.WordTrace]
  refine ⟨126032147197346372471830003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168042862929795163295773337 126032147197346372471830003)
  ·
    refine ⟨189048220796019558707745005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126032147197346372471830003 189048220796019558707745005)
    ·
      refine ⟨70893082798507334515404377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189048220796019558707745005 70893082798507334515404377)
      ·
        refine ⟨53169812098880500886553283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70893082798507334515404377 53169812098880500886553283)
        ·
          refine ⟨79754718148320751329829925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53169812098880500886553283 79754718148320751329829925)
          ·
            refine ⟨14954009652810140874343111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79754718148320751329829925 14954009652810140874343111)
            ·
              refine ⟨22431014479215211311514667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14954009652810140874343111 22431014479215211311514667)
              ·
                refine ⟨33646521718822816967272001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22431014479215211311514667 33646521718822816967272001)
                ·
                  refine ⟨25234891289117112725454001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33646521718822816967272001 25234891289117112725454001)
                  ·
                    refine ⟨18926168466837834544090501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25234891289117112725454001 18926168466837834544090501)
                    ·
                      refine ⟨3548656587532093977016969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18926168466837834544090501 3548656587532093977016969)
                      ·
                        rfl

theorem cell23_6910984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_6910984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910984 prefixEnd_6910984 := by exact prefixLift 6910984
  have htrace : WordTrace (prefixWord ++ tailWord_6910984) baseStart_6910984 baseEnd_6910984 := by
    simpa [prefixWord, tailWord_6910984, baseEnd_6910984] using wordTrace_append hprefix tailTrace_6910984
  have hstable : (prefixWord ++ tailWord_6910984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910984).length < 2 ^ (prefixWord ++ tailWord_6910984).sum := by decide
  have hdescent : baseEnd_6910984 < baseStart_6910984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6910988 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 2, 2, 2]
def baseStart_6910988 : Nat := 118140960795 + 6910988 * 2 ^ 59
def prefixEnd_6910988 : Nat := 4983230072969 + 3 ^ 40 * 6910988 * 2
def baseEnd_6910988 : Nat := 3548658641454711961366951

theorem tailTrace_6910988 : CollatzResearch.WordTrace tailWord_6910988 prefixEnd_6910988 3548658641454711961366951 := by
  unfold tailWord_6910988
  simp only [CollatzResearch.WordTrace]
  refine ⟨126032220143339126813402809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168042960191118835751203745 126032220143339126813402809)
  ·
    refine ⟨94524165107504345110052107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126032220143339126813402809 94524165107504345110052107)
    ·
      refine ⟨141786247661256517665078161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94524165107504345110052107 141786247661256517665078161)
      ·
        refine ⟨106339685745942388248808621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141786247661256517665078161 106339685745942388248808621)
        ·
          refine ⟨39877382154728395593303233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106339685745942388248808621 39877382154728395593303233)
          ·
            refine ⟨29908036616046296694977425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39877382154728395593303233 29908036616046296694977425)
            ·
              refine ⟨22431027462034722521233069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29908036616046296694977425 22431027462034722521233069)
              ·
                refine ⟨8411635298263020945462401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22431027462034722521233069 8411635298263020945462401)
                ·
                  refine ⟨6308726473697265709096801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8411635298263020945462401 6308726473697265709096801)
                  ·
                    refine ⟨4731544855272949281822601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6308726473697265709096801 4731544855272949281822601)
                    ·
                      refine ⟨3548658641454711961366951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731544855272949281822601 3548658641454711961366951)
                      ·
                        rfl

theorem cell23_6910988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_6910988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6910988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6910988 prefixEnd_6910988 := by exact prefixLift 6910988
  have htrace : WordTrace (prefixWord ++ tailWord_6910988) baseStart_6910988 baseEnd_6910988 := by
    simpa [prefixWord, tailWord_6910988, baseEnd_6910988] using wordTrace_append hprefix tailTrace_6910988
  have hstable : (prefixWord ++ tailWord_6910988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6910988).length < 2 ^ (prefixWord ++ tailWord_6910988).sum := by decide
  have hdescent : baseEnd_6910988 < baseStart_6910988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6910988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911011 : List Nat := [1, 1, 1, 4, 3, 3, 2, 3, 5]
def baseStart_6911011 : Nat := 118140960795 + 6911011 * 2 ^ 59
def prefixEnd_6911011 : Nat := 4983230072969 + 3 ^ 40 * 6911011 * 2
def baseEnd_6911011 : Nat := 394296716834418374597705

theorem tailTrace_6911011 : CollatzResearch.WordTrace tailWord_6911011 prefixEnd_6911011 394296716834418374597705 := by
  unfold tailWord_6911011
  simp only [CollatzResearch.WordTrace]
  refine ⟨252065279165594928554892887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168043519443729952369928591 252065279165594928554892887)
  ·
    refine ⟨378097918748392392832339331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252065279165594928554892887 378097918748392392832339331)
    ·
      refine ⟨567146878122588589248508997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378097918748392392832339331 567146878122588589248508997)
      ·
        refine ⟨106340039647985360484095437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 567146878122588589248508997 106340039647985360484095437)
        ·
          refine ⟨39877514867994510181535789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106340039647985360484095437 39877514867994510181535789)
          ·
            refine ⟨14954068075497941318075921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39877514867994510181535789 14954068075497941318075921)
            ·
              refine ⟨11215551056623455988556941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14954068075497941318075921 11215551056623455988556941)
              ·
                refine ⟨4205831646233795995708853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11215551056623455988556941 4205831646233795995708853)
                ·
                  refine ⟨394296716834418374597705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205831646233795995708853 394296716834418374597705)
                  ·
                    rfl

theorem cell23_6911011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 5].length) (baseStart_6911011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911011 prefixEnd_6911011 := by exact prefixLift 6911011
  have htrace : WordTrace (prefixWord ++ tailWord_6911011) baseStart_6911011 baseEnd_6911011 := by
    simpa [prefixWord, tailWord_6911011, baseEnd_6911011] using wordTrace_append hprefix tailTrace_6911011
  have hstable : (prefixWord ++ tailWord_6911011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911011).length < 2 ^ (prefixWord ++ tailWord_6911011).sum := by decide
  have hdescent : baseEnd_6911011 < baseStart_6911011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911028 : List Nat := [2, 5, 1, 2, 1, 1, 2, 4, 5]
def baseStart_6911028 : Nat := 118140960795 + 6911028 * 2 ^ 59
def prefixEnd_6911028 : Nat := 4983230072969 + 3 ^ 40 * 6911028 * 2
def baseEnd_6911028 : Nat := 394297686742321311651863

theorem tailTrace_6911028 : CollatzResearch.WordTrace tailWord_6911028 prefixEnd_6911028 394297686742321311651863 := by
  unfold tailWord_6911028
  simp only [CollatzResearch.WordTrace]
  refine ⟨126032949603266670229130869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168043932804355560305507825 126032949603266670229130869)
  ·
    refine ⟨11815589025306250333981019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126032949603266670229130869 11815589025306250333981019)
    ·
      refine ⟨17723383537959375500971529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11815589025306250333981019 17723383537959375500971529)
      ·
        refine ⟨13292537653469531625728647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17723383537959375500971529 13292537653469531625728647)
        ·
          refine ⟨19938806480204297438592971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13292537653469531625728647 19938806480204297438592971)
          ·
            refine ⟨29908209720306446157889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19938806480204297438592971 29908209720306446157889457)
            ·
              refine ⟨22431157290229834618417093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29908209720306446157889457 22431157290229834618417093)
              ·
                refine ⟨4205841991918093990953205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22431157290229834618417093 4205841991918093990953205)
                ·
                  refine ⟨394297686742321311651863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205841991918093990953205 394297686742321311651863)
                  ·
                    rfl

theorem cell23_6911028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_6911028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911028 prefixEnd_6911028 := by exact prefixLift 6911028
  have htrace : WordTrace (prefixWord ++ tailWord_6911028) baseStart_6911028 baseEnd_6911028 := by
    simpa [prefixWord, tailWord_6911028, baseEnd_6911028] using wordTrace_append hprefix tailTrace_6911028
  have hstable : (prefixWord ++ tailWord_6911028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911028).length < 2 ^ (prefixWord ++ tailWord_6911028).sum := by decide
  have hdescent : baseEnd_6911028 < baseStart_6911028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911062 : List Nat := [5, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_6911062 : Nat := 118140960795 + 6911062 * 2 ^ 59
def prefixEnd_6911062 : Nat := 4983230072969 + 3 ^ 40 * 6911062 * 2
def baseEnd_6911062 : Nat := 394299626558127185760179

theorem tailTrace_6911062 : CollatzResearch.WordTrace tailWord_6911062 prefixEnd_6911062 394299626558127185760179 := by
  unfold tailWord_6911062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15754196205525635266562465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168044759525606776176666293 15754196205525635266562465)
  ·
    refine ⟨11815647154144226449921849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15754196205525635266562465 11815647154144226449921849)
    ·
      refine ⟨8861735365608169837441387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11815647154144226449921849 8861735365608169837441387)
      ·
        refine ⟨13292603048412254756162081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861735365608169837441387 13292603048412254756162081)
        ·
          refine ⟨9969452286309191067121561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13292603048412254756162081 9969452286309191067121561)
          ·
            refine ⟨7477089214731893300341171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9969452286309191067121561 7477089214731893300341171)
            ·
              refine ⟨11215633822097839950511757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7477089214731893300341171 11215633822097839950511757)
              ·
                refine ⟨4205862683286689981441909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11215633822097839950511757 4205862683286689981441909)
                ·
                  refine ⟨394299626558127185760179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205862683286689981441909 394299626558127185760179)
                  ·
                    rfl

theorem cell23_6911062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_6911062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911062 prefixEnd_6911062 := by exact prefixLift 6911062
  have htrace : WordTrace (prefixWord ++ tailWord_6911062) baseStart_6911062 baseEnd_6911062 := by
    simpa [prefixWord, tailWord_6911062, baseEnd_6911062] using wordTrace_append hprefix tailTrace_6911062
  have hstable : (prefixWord ++ tailWord_6911062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911062).length < 2 ^ (prefixWord ++ tailWord_6911062).sum := by decide
  have hdescent : baseEnd_6911062 < baseStart_6911062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911064 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_6911064 : Nat := 118140960795 + 6911064 * 2 ^ 59
def prefixEnd_6911064 : Nat := 4983230072969 + 3 ^ 40 * 6911064 * 2
def baseEnd_6911064 : Nat := 3548697665984453664016601

theorem tailTrace_6911064 : CollatzResearch.WordTrace tailWord_6911064 prefixEnd_6911064 3548697665984453664016601 := by
  unfold tailWord_6911064
  simp only [CollatzResearch.WordTrace]
  refine ⟨126033606117201459303286123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168044808156268612404381497 126033606117201459303286123)
  ·
    refine ⟨189050409175802188954929185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126033606117201459303286123 189050409175802188954929185)
    ·
      refine ⟨141787806881851641716196889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189050409175802188954929185 141787806881851641716196889)
      ·
        refine ⟨106340855161388731287147667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141787806881851641716196889 106340855161388731287147667)
        ·
          refine ⟨159511282742083096930721501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106340855161388731287147667 159511282742083096930721501)
          ·
            refine ⟨59816731028281161349020563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159511282742083096930721501 59816731028281161349020563)
            ·
              refine ⟨89725096542421742023530845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59816731028281161349020563 89725096542421742023530845)
              ·
                refine ⟨33646911203408153258824067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89725096542421742023530845 33646911203408153258824067)
                ·
                  refine ⟨50470366805112229888236101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33646911203408153258824067 50470366805112229888236101)
                  ·
                    refine ⟨9463193775958543104044269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50470366805112229888236101 9463193775958543104044269)
                    ·
                      refine ⟨3548697665984453664016601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9463193775958543104044269 3548697665984453664016601)
                      ·
                        rfl

theorem cell23_6911064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_6911064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911064 prefixEnd_6911064 := by exact prefixLift 6911064
  have htrace : WordTrace (prefixWord ++ tailWord_6911064) baseStart_6911064 baseEnd_6911064 := by
    simpa [prefixWord, tailWord_6911064, baseEnd_6911064] using wordTrace_append hprefix tailTrace_6911064
  have hstable : (prefixWord ++ tailWord_6911064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911064).length < 2 ^ (prefixWord ++ tailWord_6911064).sum := by decide
  have hdescent : baseEnd_6911064 < baseStart_6911064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911081 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 3]
def baseStart_6911081 : Nat := 118140960795 + 6911081 * 2 ^ 59
def prefixEnd_6911081 : Nat := 4983230072969 + 3 ^ 40 * 6911081 * 2
def baseEnd_6911081 : Nat := 3548706395155580097504023

theorem tailTrace_6911081 : CollatzResearch.WordTrace tailWord_6911081 prefixEnd_6911081 3548706395155580097504023 := by
  unfold tailWord_6911081
  simp only [CollatzResearch.WordTrace]
  refine ⟨252067832275341330509941097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168045221516894220339960731 252067832275341330509941097)
  ·
    refine ⟨189050874206505997882455823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252067832275341330509941097 189050874206505997882455823)
    ·
      refine ⟨283576311309758996823683735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189050874206505997882455823 283576311309758996823683735)
      ·
        refine ⟨425364466964638495235525603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283576311309758996823683735 425364466964638495235525603)
        ·
          refine ⟨638046700446957742853288405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425364466964638495235525603 638046700446957742853288405)
          ·
            refine ⟨14954219541725572098123947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 638046700446957742853288405 14954219541725572098123947)
            ·
              refine ⟨22431329312588358147185921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14954219541725572098123947 22431329312588358147185921)
              ·
                refine ⟨16823496984441268610389441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22431329312588358147185921 16823496984441268610389441)
                ·
                  refine ⟨12617622738330951457792081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16823496984441268610389441 12617622738330951457792081)
                  ·
                    refine ⟨9463217053748213593344061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12617622738330951457792081 9463217053748213593344061)
                    ·
                      refine ⟨3548706395155580097504023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9463217053748213593344061 3548706395155580097504023)
                      ·
                        rfl

theorem cell23_6911081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_6911081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911081 prefixEnd_6911081 := by exact prefixLift 6911081
  have htrace : WordTrace (prefixWord ++ tailWord_6911081) baseStart_6911081 baseEnd_6911081 := by
    simpa [prefixWord, tailWord_6911081, baseEnd_6911081] using wordTrace_append hprefix tailTrace_6911081
  have hstable : (prefixWord ++ tailWord_6911081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911081).length < 2 ^ (prefixWord ++ tailWord_6911081).sum := by decide
  have hdescent : baseEnd_6911081 < baseStart_6911081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911084 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 6]
def baseStart_6911084 : Nat := 118140960795 + 6911084 * 2 ^ 59
def prefixEnd_6911084 : Nat := 4983230072969 + 3 ^ 40 * 6911084 * 2
def baseEnd_6911084 : Nat := 394300881733060398418501

theorem tailTrace_6911084 : CollatzResearch.WordTrace tailWord_6911084 prefixEnd_6911084 394300881733060398418501 := by
  unfold tailWord_6911084
  simp only [CollatzResearch.WordTrace]
  refine ⟨126033970847165231011150153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168045294462886974681533537 126033970847165231011150153)
  ·
    refine ⟨94525478135373923258362615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126033970847165231011150153 94525478135373923258362615)
    ·
      refine ⟨141788217203060884887543923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94525478135373923258362615 141788217203060884887543923)
      ·
        refine ⟨212682325804591327331315885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141788217203060884887543923 212682325804591327331315885)
        ·
          refine ⟨79755872176721747749243457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212682325804591327331315885 79755872176721747749243457)
          ·
            refine ⟨59816904132541310811932593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79755872176721747749243457 59816904132541310811932593)
            ·
              refine ⟨44862678099405983108949445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59816904132541310811932593 44862678099405983108949445)
              ·
                refine ⟨8411752143638621832928021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44862678099405983108949445 8411752143638621832928021)
                ·
                  refine ⟨394300881733060398418501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8411752143638621832928021 394300881733060398418501)
                  ·
                    rfl

theorem cell23_6911084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_6911084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911084 prefixEnd_6911084 := by exact prefixLift 6911084
  have htrace : WordTrace (prefixWord ++ tailWord_6911084) baseStart_6911084 baseEnd_6911084 := by
    simpa [prefixWord, tailWord_6911084, baseEnd_6911084] using wordTrace_append hprefix tailTrace_6911084
  have hstable : (prefixWord ++ tailWord_6911084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911084).length < 2 ^ (prefixWord ++ tailWord_6911084).sum := by decide
  have hdescent : baseEnd_6911084 < baseStart_6911084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911111 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_6911111 : Nat := 118140960795 + 6911111 * 2 ^ 59
def prefixEnd_6911111 : Nat := 4983230072969 + 3 ^ 40 * 6911111 * 2
def baseEnd_6911111 : Nat := 3548721799575214980128885

theorem tailTrace_6911111 : CollatzResearch.WordTrace tailWord_6911111 prefixEnd_6911111 3548721799575214980128885 := by
  unfold tailWord_6911111
  simp only [CollatzResearch.WordTrace]
  refine ⟨252068926465232645633533187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168045950976821763755688791 252068926465232645633533187)
  ·
    refine ⟨378103389697848968450299781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252068926465232645633533187 378103389697848968450299781)
    ·
      refine ⟨70894385568346681584431209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378103389697848968450299781 70894385568346681584431209)
      ·
        refine ⟨53170789176260011188323407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70894385568346681584431209 53170789176260011188323407)
        ·
          refine ⟨79756183764390016782485111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53170789176260011188323407 79756183764390016782485111)
          ·
            refine ⟨119634275646585025173727667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79756183764390016782485111 119634275646585025173727667)
            ·
              refine ⟨179451413469877537760591501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119634275646585025173727667 179451413469877537760591501)
              ·
                refine ⟨67294280051204076660221813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179451413469877537760591501 67294280051204076660221813)
                ·
                  refine ⟨6308838754800382186895795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67294280051204076660221813 6308838754800382186895795)
                  ·
                    refine ⟨9463258132200573280343693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6308838754800382186895795 9463258132200573280343693)
                    ·
                      refine ⟨3548721799575214980128885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9463258132200573280343693 3548721799575214980128885)
                      ·
                        rfl

theorem cell23_6911111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_6911111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911111 prefixEnd_6911111 := by exact prefixLift 6911111
  have htrace : WordTrace (prefixWord ++ tailWord_6911111) baseStart_6911111 baseEnd_6911111 := by
    simpa [prefixWord, tailWord_6911111, baseEnd_6911111] using wordTrace_append hprefix tailTrace_6911111
  have hstable : (prefixWord ++ tailWord_6911111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911111).length < 2 ^ (prefixWord ++ tailWord_6911111).sum := by decide
  have hdescent : baseEnd_6911111 < baseStart_6911111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911161 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 1, 6]
def baseStart_6911161 : Nat := 118140960795 + 6911161 * 2 ^ 59
def prefixEnd_6911161 : Nat := 4983230072969 + 3 ^ 40 * 6911161 * 2
def baseEnd_6911161 : Nat := 1182915824535979928167885

theorem tailTrace_6911161 : CollatzResearch.WordTrace tailWord_6911161 prefixEnd_6911161 1182915824535979928167885 := by
  unfold tailWord_6911161
  simp only [CollatzResearch.WordTrace]
  refine ⟨252070750115051504172853337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168047166743367669448568891 252070750115051504172853337)
  ·
    refine ⟨189053062586288628129640003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252070750115051504172853337 189053062586288628129640003)
    ·
      refine ⟨283579593879432942194460005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189053062586288628129640003 283579593879432942194460005)
      ·
        refine ⟨53171173852393676661461251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283579593879432942194460005 53171173852393676661461251)
        ·
          refine ⟨79756760778590514992191877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53171173852393676661461251 79756760778590514992191877)
          ·
            refine ⟨14954392645985721561035977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79756760778590514992191877 14954392645985721561035977)
            ·
              refine ⟨11215794484489291170776983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14954392645985721561035977 11215794484489291170776983)
              ·
                refine ⟨16823691726733936756165475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11215794484489291170776983 16823691726733936756165475)
                ·
                  refine ⟨25235537590100905134248213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16823691726733936756165475 25235537590100905134248213)
                  ·
                    refine ⟨1182915824535979928167885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25235537590100905134248213 1182915824535979928167885)
                    ·
                      rfl

theorem cell23_6911161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_6911161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911161 prefixEnd_6911161 := by exact prefixLift 6911161
  have htrace : WordTrace (prefixWord ++ tailWord_6911161) baseStart_6911161 baseEnd_6911161 := by
    simpa [prefixWord, tailWord_6911161, baseEnd_6911161] using wordTrace_append hprefix tailTrace_6911161
  have hstable : (prefixWord ++ tailWord_6911161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911161).length < 2 ^ (prefixWord ++ tailWord_6911161).sum := by decide
  have hdescent : baseEnd_6911161 < baseStart_6911161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911172 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_6911172 : Nat := 118140960795 + 6911172 * 2 ^ 59
def prefixEnd_6911172 : Nat := 4983230072969 + 3 ^ 40 * 6911172 * 2
def baseEnd_6911172 : Nat := 3548753121895139241466105

theorem tailTrace_6911172 : CollatzResearch.WordTrace tailWord_6911172 prefixEnd_6911172 3548753121895139241466105 := by
  unfold tailWord_6911172
  simp only [CollatzResearch.WordTrace]
  refine ⟨126035575659005826525751885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168047434212007768701002513 126035575659005826525751885)
  ·
    refine ⟨47263340872127184947156957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126035575659005826525751885 47263340872127184947156957)
    ·
      refine ⟨17723752827047694355183859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47263340872127184947156957 17723752827047694355183859)
      ·
        refine ⟨26585629240571541532775789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17723752827047694355183859 26585629240571541532775789)
        ·
          refine ⟨9969610965214328074790921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26585629240571541532775789 9969610965214328074790921)
          ·
            refine ⟨7477208223910746056093191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9969610965214328074790921 7477208223910746056093191)
            ·
              refine ⟨11215812335866119084139787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7477208223910746056093191 11215812335866119084139787)
              ·
                refine ⟨16823718503799178626209681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11215812335866119084139787 16823718503799178626209681)
                ·
                  refine ⟨12617788877849383969657261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16823718503799178626209681 12617788877849383969657261)
                  ·
                    refine ⟨4731670829193518988621473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12617788877849383969657261 4731670829193518988621473)
                    ·
                      refine ⟨3548753121895139241466105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731670829193518988621473 3548753121895139241466105)
                      ·
                        rfl

theorem cell23_6911172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_6911172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911172 prefixEnd_6911172 := by exact prefixLift 6911172
  have htrace : WordTrace (prefixWord ++ tailWord_6911172) baseStart_6911172 baseEnd_6911172 := by
    simpa [prefixWord, tailWord_6911172, baseEnd_6911172] using wordTrace_append hprefix tailTrace_6911172
  have hstable : (prefixWord ++ tailWord_6911172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911172).length < 2 ^ (prefixWord ++ tailWord_6911172).sum := by decide
  have hdescent : baseEnd_6911172 < baseStart_6911172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911182 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_6911182 : Nat := 118140960795 + 6911182 * 2 ^ 59
def prefixEnd_6911182 : Nat := 4983230072969 + 3 ^ 40 * 6911182 * 2
def baseEnd_6911182 : Nat := 1182919418900561400780353

theorem tailTrace_6911182 : CollatzResearch.WordTrace tailWord_6911182 prefixEnd_6911182 1182919418900561400780353 := by
  unfold tailWord_6911182
  simp only [CollatzResearch.WordTrace]
  refine ⟨31508939505996928094920975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168047677365316949839578533 31508939505996928094920975)
  ·
    refine ⟨47263409258995392142381463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31508939505996928094920975 47263409258995392142381463)
    ·
      refine ⟨70895113888493088213572195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47263409258995392142381463 70895113888493088213572195)
      ·
        refine ⟨106342670832739632320358293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70895113888493088213572195 106342670832739632320358293)
        ·
          refine ⟨4984812695284670265016795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106342670832739632320358293 4984812695284670265016795)
          ·
            refine ⟨7477219042927005397525193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984812695284670265016795 7477219042927005397525193)
            ·
              refine ⟨5607914282195254048143895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7477219042927005397525193 5607914282195254048143895)
              ·
                refine ⟨8411871423292881072215843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607914282195254048143895 8411871423292881072215843)
                ·
                  refine ⟨12617807134939321608323765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411871423292881072215843 12617807134939321608323765)
                  ·
                    refine ⟨1182919418900561400780353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12617807134939321608323765 1182919418900561400780353)
                    ·
                      rfl

theorem cell23_6911182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_6911182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911182 prefixEnd_6911182 := by exact prefixLift 6911182
  have htrace : WordTrace (prefixWord ++ tailWord_6911182) baseStart_6911182 baseEnd_6911182 := by
    simpa [prefixWord, tailWord_6911182, baseEnd_6911182] using wordTrace_append hprefix tailTrace_6911182
  have hstable : (prefixWord ++ tailWord_6911182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911182).length < 2 ^ (prefixWord ++ tailWord_6911182).sum := by decide
  have hdescent : baseEnd_6911182 < baseStart_6911182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911194 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_6911194 : Nat := 118140960795 + 6911194 * 2 ^ 59
def prefixEnd_6911194 : Nat := 4983230072969 + 3 ^ 40 * 6911194 * 2
def baseEnd_6911194 : Nat := 3548764418469538155391003

theorem tailTrace_6911194 : CollatzResearch.WordTrace tailWord_6911194 prefixEnd_6911194 3548764418469538155391003 := by
  unfold tailWord_6911194
  simp only [CollatzResearch.WordTrace]
  refine ⟨63017988430982987702201159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168047969149287967205869757 63017988430982987702201159)
  ·
    refine ⟨94526982646474481553301739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63017988430982987702201159 94526982646474481553301739)
    ·
      refine ⟨141790473969711722329952609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94526982646474481553301739 141790473969711722329952609)
      ·
        refine ⟨106342855477283791747464457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141790473969711722329952609 106342855477283791747464457)
        ·
          refine ⟨79757141607962843810598343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106342855477283791747464457 79757141607962843810598343)
          ·
            refine ⟨119635712411944265715897515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79757141607962843810598343 119635712411944265715897515)
            ·
              refine ⟨179453568617916398573846273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119635712411944265715897515 179453568617916398573846273)
              ·
                refine ⟨134590176463437298930384705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179453568617916398573846273 134590176463437298930384705)
                ·
                  refine ⟨100942632347577974197788529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134590176463437298930384705 100942632347577974197788529)
                  ·
                    refine ⟨75706974260683480648341397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100942632347577974197788529 75706974260683480648341397)
                    ·
                      refine ⟨3548764418469538155391003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75706974260683480648341397 3548764418469538155391003)
                      ·
                        rfl

theorem cell23_6911194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_6911194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911194 prefixEnd_6911194 := by exact prefixLift 6911194
  have htrace : WordTrace (prefixWord ++ tailWord_6911194) baseStart_6911194 baseEnd_6911194 := by
    simpa [prefixWord, tailWord_6911194, baseEnd_6911194] using wordTrace_append hprefix tailTrace_6911194
  have hstable : (prefixWord ++ tailWord_6911194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911194).length < 2 ^ (prefixWord ++ tailWord_6911194).sum := by decide
  have hdescent : baseEnd_6911194 < baseStart_6911194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911204 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_6911204 : Nat := 118140960795 + 6911204 * 2 ^ 59
def prefixEnd_6911204 : Nat := 4983230072969 + 3 ^ 40 * 6911204 * 2
def baseEnd_6911204 : Nat := 1182923184425361038755319

theorem tailTrace_6911204 : CollatzResearch.WordTrace tailWord_6911204 prefixEnd_6911204 1182923184425361038755319 := by
  unfold tailWord_6911204
  simp only [CollatzResearch.WordTrace]
  refine ⟨126036159226947861258334333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168048212302597148344445777 126036159226947861258334333)
  ·
    refine ⟨47263559710105447971875375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126036159226947861258334333 47263559710105447971875375)
    ·
      refine ⟨70895339565158171957813063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47263559710105447971875375 70895339565158171957813063)
      ·
        refine ⟨106343009347737257936719595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70895339565158171957813063 106343009347737257936719595)
        ·
          refine ⟨159514514021605886905079393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106343009347737257936719595 159514514021605886905079393)
          ·
            refine ⟨119635885516204415178809545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159514514021605886905079393 119635885516204415178809545)
            ·
              refine ⟨89726914137153311384107159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119635885516204415178809545 89726914137153311384107159)
              ·
                refine ⟨134590371205729967076160739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89726914137153311384107159 134590371205729967076160739)
                ·
                  refine ⟨201885556808594950614241109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134590371205729967076160739 201885556808594950614241109)
                  ·
                    refine ⟨1182923184425361038755319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 201885556808594950614241109 1182923184425361038755319)
                    ·
                      rfl

theorem cell23_6911204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_6911204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911204 prefixEnd_6911204 := by exact prefixLift 6911204
  have htrace : WordTrace (prefixWord ++ tailWord_6911204) baseStart_6911204 baseEnd_6911204 := by
    simpa [prefixWord, tailWord_6911204, baseEnd_6911204] using wordTrace_append hprefix tailTrace_6911204
  have hstable : (prefixWord ++ tailWord_6911204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911204).length < 2 ^ (prefixWord ++ tailWord_6911204).sum := by decide
  have hdescent : baseEnd_6911204 < baseStart_6911204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911215 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 1, 2, 4]
def baseStart_6911215 : Nat := 118140960795 + 6911215 * 2 ^ 59
def prefixEnd_6911215 : Nat := 4983230072969 + 3 ^ 40 * 6911215 * 2
def baseEnd_6911215 : Nat := 3548775201563282573228407

theorem tailTrace_6911215 : CollatzResearch.WordTrace tailWord_6911215 prefixEnd_6911215 3548775201563282573228407 := by
  unfold tailWord_6911215
  simp only [CollatzResearch.WordTrace]
  refine ⟨252072719656855871395319099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168048479771237247596879399 252072719656855871395319099)
  ·
    refine ⟨378109079485283807092978649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252072719656855871395319099 378109079485283807092978649)
    ·
      refine ⟨283581809613962855319733987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378109079485283807092978649 283581809613962855319733987)
      ·
        refine ⟨425372714420944282979600981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283581809613962855319733987 425372714420944282979600981)
        ·
          refine ⟨4984836497120440816167199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 425372714420944282979600981 4984836497120440816167199)
          ·
            refine ⟨7477254745680661224250799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984836497120440816167199 7477254745680661224250799)
            ·
              refine ⟨11215882118520991836376199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7477254745680661224250799 11215882118520991836376199)
              ·
                refine ⟨16823823177781487754564299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11215882118520991836376199 16823823177781487754564299)
                ·
                  refine ⟨25235734766672231631846449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16823823177781487754564299 25235734766672231631846449)
                  ·
                    refine ⟨18926801075004173723884837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25235734766672231631846449 18926801075004173723884837)
                    ·
                      refine ⟨3548775201563282573228407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18926801075004173723884837 3548775201563282573228407)
                      ·
                        rfl

theorem cell23_6911215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 2, 4].length) (baseStart_6911215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911215 prefixEnd_6911215 := by exact prefixLift 6911215
  have htrace : WordTrace (prefixWord ++ tailWord_6911215) baseStart_6911215 baseEnd_6911215 := by
    simpa [prefixWord, tailWord_6911215, baseEnd_6911215] using wordTrace_append hprefix tailTrace_6911215
  have hstable : (prefixWord ++ tailWord_6911215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911215).length < 2 ^ (prefixWord ++ tailWord_6911215).sum := by decide
  have hdescent : baseEnd_6911215 < baseStart_6911215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911321 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_6911321 : Nat := 118140960795 + 6911321 * 2 ^ 59
def prefixEnd_6911321 : Nat := 4983230072969 + 3 ^ 40 * 6911321 * 2
def baseEnd_6911321 : Nat := 3548829630512659158502919

theorem tailTrace_6911321 : CollatzResearch.WordTrace tailWord_6911321 prefixEnd_6911321 3548829630512659158502919 := by
  unfold tailWord_6911321
  simp only [CollatzResearch.WordTrace]
  refine ⟨252076585794471851498677817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168051057196314567665785211 252076585794471851498677817)
  ·
    refine ⟨189057439345853888624008363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252076585794471851498677817 189057439345853888624008363)
    ·
      refine ⟨283586159018780832936012545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189057439345853888624008363 283586159018780832936012545)
      ·
        refine ⟨212689619264085624702009409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283586159018780832936012545 212689619264085624702009409)
        ·
          refine ⟨159517214448064218526507057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212689619264085624702009409 159517214448064218526507057)
          ·
            refine ⟨119637910836048163894880293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159517214448064218526507057 119637910836048163894880293)
            ·
              refine ⟨22432108281759030730290055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119637910836048163894880293 22432108281759030730290055)
              ·
                refine ⟨33648162422638546095435083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22432108281759030730290055 33648162422638546095435083)
                ·
                  refine ⟨50472243633957819143152625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33648162422638546095435083 50472243633957819143152625)
                  ·
                    refine ⟨37854182725468364357364469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50472243633957819143152625 37854182725468364357364469)
                    ·
                      refine ⟨3548829630512659158502919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37854182725468364357364469 3548829630512659158502919)
                      ·
                        rfl

theorem cell23_6911321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_6911321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911321 prefixEnd_6911321 := by exact prefixLift 6911321
  have htrace : WordTrace (prefixWord ++ tailWord_6911321) baseStart_6911321 baseEnd_6911321 := by
    simpa [prefixWord, tailWord_6911321, baseEnd_6911321] using wordTrace_append hprefix tailTrace_6911321
  have hstable : (prefixWord ++ tailWord_6911321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911321).length < 2 ^ (prefixWord ++ tailWord_6911321).sum := by decide
  have hdescent : baseEnd_6911321 < baseStart_6911321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911371 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 8]
def baseStart_6911371 : Nat := 118140960795 + 6911371 * 2 ^ 59
def prefixEnd_6911371 : Nat := 4983230072969 + 3 ^ 40 * 6911371 * 2
def baseEnd_6911371 : Nat := 394317256060598218097521

theorem tailTrace_6911371 : CollatzResearch.WordTrace tailWord_6911371 prefixEnd_6911371 394317256060598218097521 := by
  unfold tailWord_6911371
  simp only [CollatzResearch.WordTrace]
  refine ⟨252078409444290710037997967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168052272962860473358665311 252078409444290710037997967)
  ·
    refine ⟨378117614166436065056996951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252078409444290710037997967 378117614166436065056996951)
    ·
      refine ⟨567176421249654097585495427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378117614166436065056996951 567176421249654097585495427)
      ·
        refine ⟨850764631874481146378243141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567176421249654097585495427 850764631874481146378243141)
        ·
          refine ⟨159518368476465214945920589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 850764631874481146378243141 159518368476465214945920589)
          ·
            refine ⟨59819388178674455604720221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159518368476465214945920589 59819388178674455604720221)
            ·
              refine ⟨22432270567002920851770083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59819388178674455604720221 22432270567002920851770083)
              ·
                refine ⟨33648405850504381277655125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22432270567002920851770083 33648405850504381277655125)
                ·
                  refine ⟨394317256060598218097521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33648405850504381277655125 394317256060598218097521)
                  ·
                    rfl

theorem cell23_6911371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 8].length) (baseStart_6911371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911371 prefixEnd_6911371 := by exact prefixLift 6911371
  have htrace : WordTrace (prefixWord ++ tailWord_6911371) baseStart_6911371 baseEnd_6911371 := by
    simpa [prefixWord, tailWord_6911371, baseEnd_6911371] using wordTrace_append hprefix tailTrace_6911371
  have hstable : (prefixWord ++ tailWord_6911371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911371).length < 2 ^ (prefixWord ++ tailWord_6911371).sum := by decide
  have hdescent : baseEnd_6911371 < baseStart_6911371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911469 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_6911469 : Nat := 118140960795 + 6911469 * 2 ^ 59
def prefixEnd_6911469 : Nat := 4983230072969 + 3 ^ 40 * 6911469 * 2
def baseEnd_6911469 : Nat := 1182968541883174859817413

theorem tailTrace_6911469 : CollatzResearch.WordTrace tailWord_6911469 prefixEnd_6911469 1182968541883174859817413 := by
  unfold tailWord_6911469
  simp only [CollatzResearch.WordTrace]
  refine ⟨252081983797935672775065461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168054655865290448516710307 252081983797935672775065461)
  ·
    refine ⟨23632685981056469322662387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252081983797935672775065461 23632685981056469322662387)
    ·
      refine ⟨35449028971584703983993581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23632685981056469322662387 35449028971584703983993581)
      ·
        refine ⟨13293385864344263993997593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35449028971584703983993581 13293385864344263993997593)
        ·
          refine ⟨9970039398258197995498195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13293385864344263993997593 9970039398258197995498195)
          ·
            refine ⟨14955059097387296993247293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970039398258197995498195 14955059097387296993247293)
            ·
              refine ⟨5608147161520236372467735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14955059097387296993247293 5608147161520236372467735)
              ·
                refine ⟨8412220742280354558701603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608147161520236372467735 8412220742280354558701603)
                ·
                  refine ⟨12618331113420531838052405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412220742280354558701603 12618331113420531838052405)
                  ·
                    refine ⟨1182968541883174859817413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12618331113420531838052405 1182968541883174859817413)
                    ·
                      rfl

theorem cell23_6911469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_6911469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911469 prefixEnd_6911469 := by exact prefixLift 6911469
  have htrace : WordTrace (prefixWord ++ tailWord_6911469) baseStart_6911469 baseEnd_6911469 := by
    simpa [prefixWord, tailWord_6911469, baseEnd_6911469] using wordTrace_append hprefix tailTrace_6911469
  have hstable : (prefixWord ++ tailWord_6911469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911469).length < 2 ^ (prefixWord ++ tailWord_6911469).sum := by decide
  have hdescent : baseEnd_6911469 < baseStart_6911469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911472 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 1, 1, 4]
def baseStart_6911472 : Nat := 118140960795 + 6911472 * 2 ^ 59
def prefixEnd_6911472 : Nat := 4983230072969 + 3 ^ 40 * 6911472 * 2
def baseEnd_6911472 : Nat := 3548907166091488067714725

theorem tailTrace_6911472 : CollatzResearch.WordTrace tailWord_6911472 prefixEnd_6911472 3548907166091488067714725 := by
  unfold tailWord_6911472
  simp only [CollatzResearch.WordTrace]
  refine ⟨126041046608462402143712335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168054728811283202858283113 126041046608462402143712335)
  ·
    refine ⟨189061569912693603215568503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126041046608462402143712335 189061569912693603215568503)
    ·
      refine ⟨283592354869040404823352755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189061569912693603215568503 283592354869040404823352755)
      ·
        refine ⟨425388532303560607235029133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283592354869040404823352755 425388532303560607235029133)
        ·
          refine ⟨159520699613835227713135925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425388532303560607235029133 159520699613835227713135925)
          ·
            refine ⟨14955065588797052598106493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159520699613835227713135925 14955065588797052598106493)
            ·
              refine ⟨5608149595798894724289935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14955065588797052598106493 5608149595798894724289935)
              ·
                refine ⟨8412224393698342086434903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608149595798894724289935 8412224393698342086434903)
                ·
                  refine ⟨12618336590547513129652355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412224393698342086434903 12618336590547513129652355)
                  ·
                    refine ⟨18927504885821269694478533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12618336590547513129652355 18927504885821269694478533)
                    ·
                      refine ⟨3548907166091488067714725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18927504885821269694478533 3548907166091488067714725)
                      ·
                        rfl

theorem cell23_6911472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 1, 4].length) (baseStart_6911472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911472 prefixEnd_6911472 := by exact prefixLift 6911472
  have htrace : WordTrace (prefixWord ++ tailWord_6911472) baseStart_6911472 baseEnd_6911472 := by
    simpa [prefixWord, tailWord_6911472, baseEnd_6911472] using wordTrace_append hprefix tailTrace_6911472
  have hstable : (prefixWord ++ tailWord_6911472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911472).length < 2 ^ (prefixWord ++ tailWord_6911472).sum := by decide
  have hdescent : baseEnd_6911472 < baseStart_6911472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911478 : List Nat := [5, 1, 1, 1, 2, 13]
def baseStart_6911478 : Nat := 118140960795 + 6911478 * 2 ^ 59
def prefixEnd_6911478 : Nat := 4983230072969 + 3 ^ 40 * 6911478 * 2
def baseEnd_6911478 : Nat := 14604568917594300593579

theorem tailTrace_6911478 : CollatzResearch.WordTrace tailWord_6911478 prefixEnd_6911478 14604568917594300593579 := by
  unfold tailWord_6911478
  simp only [CollatzResearch.WordTrace]
  refine ⟨15755144503431441707008943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168054874703268711541428725 15755144503431441707008943)
  ·
    refine ⟨23632716755147162560513415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15755144503431441707008943 23632716755147162560513415)
    ·
      refine ⟨35449075132720743840770123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23632716755147162560513415 35449075132720743840770123)
      ·
        refine ⟨53173612699081115761155185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35449075132720743840770123 53173612699081115761155185)
        ·
          refine ⟨39880209524310836820866389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53173612699081115761155185 39880209524310836820866389)
          ·
            refine ⟨14604568917594300593579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 39880209524310836820866389 14604568917594300593579)
            ·
              rfl

theorem cell23_6911478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 13].length) (baseStart_6911478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911478 prefixEnd_6911478 := by exact prefixLift 6911478
  have htrace : WordTrace (prefixWord ++ tailWord_6911478) baseStart_6911478 baseEnd_6911478 := by
    simpa [prefixWord, tailWord_6911478, baseEnd_6911478] using wordTrace_append hprefix tailTrace_6911478
  have hstable : (prefixWord ++ tailWord_6911478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911478).length < 2 ^ (prefixWord ++ tailWord_6911478).sum := by decide
  have hdescent : baseEnd_6911478 < baseStart_6911478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911495 : List Nat := [1, 1, 4, 3, 2, 3, 1, 8]
def baseStart_6911495 : Nat := 118140960795 + 6911495 * 2 ^ 59
def prefixEnd_6911495 : Nat := 4983230072969 + 3 ^ 40 * 6911495 * 2
def baseEnd_6911495 : Nat := 131441443560983017693597

theorem tailTrace_6911495 : CollatzResearch.WordTrace tailWord_6911495 prefixEnd_6911495 131441443560983017693597 := by
  unfold tailWord_6911495
  simp only [CollatzResearch.WordTrace]
  refine ⟨252082932095841479215511939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168055288063894319477007959 252082932095841479215511939)
  ·
    refine ⟨378124398143762218823267909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252082932095841479215511939 378124398143762218823267909)
    ·
      refine ⟨70898324651955416029362733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378124398143762218823267909 70898324651955416029362733)
      ·
        refine ⟨26586871744483281011011025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70898324651955416029362733 26586871744483281011011025)
        ·
          refine ⟨19940153808362460758258269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26586871744483281011011025 19940153808362460758258269)
          ·
            refine ⟨7477557678135922784346851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19940153808362460758258269 7477557678135922784346851)
            ·
              refine ⟨11216336517203884176520277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7477557678135922784346851 11216336517203884176520277)
              ·
                refine ⟨131441443560983017693597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11216336517203884176520277 131441443560983017693597)
                ·
                  rfl

theorem cell23_6911495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 8].length) (baseStart_6911495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911495 prefixEnd_6911495 := by exact prefixLift 6911495
  have htrace : WordTrace (prefixWord ++ tailWord_6911495) baseStart_6911495 baseEnd_6911495 := by
    simpa [prefixWord, tailWord_6911495, baseEnd_6911495] using wordTrace_append hprefix tailTrace_6911495
  have hstable : (prefixWord ++ tailWord_6911495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911495).length < 2 ^ (prefixWord ++ tailWord_6911495).sum := by decide
  have hdescent : baseEnd_6911495 < baseStart_6911495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911502 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_6911502 : Nat := 118140960795 + 6911502 * 2 ^ 59
def prefixEnd_6911502 : Nat := 4983230072969 + 3 ^ 40 * 6911502 * 2
def baseEnd_6911502 : Nat := 3548922570511122950339587

theorem tailTrace_6911502 : CollatzResearch.WordTrace tailWord_6911502 prefixEnd_6911502 3548922570511122950339587 := by
  unfold tailWord_6911502
  simp only [CollatzResearch.WordTrace]
  refine ⟨31510398425852014926377095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168055458271210746274011173 31510398425852014926377095)
  ·
    refine ⟨47265597638778022389565643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31510398425852014926377095 47265597638778022389565643)
    ·
      refine ⟨70898396458167033584348465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47265597638778022389565643 70898396458167033584348465)
      ·
        refine ⟨53173797343625275188261349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70898396458167033584348465 53173797343625275188261349)
        ·
          refine ⟨9970087001929739097799003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53173797343625275188261349 9970087001929739097799003)
          ·
            refine ⟨14955130502894608646698505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970087001929739097799003 14955130502894608646698505)
            ·
              refine ⟨11216347877170956485023879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14955130502894608646698505 11216347877170956485023879)
              ·
                refine ⟨16824521815756434727535819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11216347877170956485023879 16824521815756434727535819)
                ·
                  refine ⟨25236782723634652091303729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16824521815756434727535819 25236782723634652091303729)
                  ·
                    refine ⟨18927587042725989068477797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25236782723634652091303729 18927587042725989068477797)
                    ·
                      refine ⟨3548922570511122950339587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18927587042725989068477797 3548922570511122950339587)
                      ·
                        rfl

theorem cell23_6911502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_6911502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911502 prefixEnd_6911502 := by exact prefixLift 6911502
  have htrace : WordTrace (prefixWord ++ tailWord_6911502) baseStart_6911502 baseEnd_6911502 := by
    simpa [prefixWord, tailWord_6911502, baseEnd_6911502] using wordTrace_append hprefix tailTrace_6911502
  have hstable : (prefixWord ++ tailWord_6911502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911502).length < 2 ^ (prefixWord ++ tailWord_6911502).sum := by decide
  have hdescent : baseEnd_6911502 < baseStart_6911502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911505 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_6911505 : Nat := 118140960795 + 6911505 * 2 ^ 59
def prefixEnd_6911505 : Nat := 4983230072969 + 3 ^ 40 * 6911505 * 2
def baseEnd_6911505 : Nat := 3548924110953086438602073

theorem tailTrace_6911505 : CollatzResearch.WordTrace tailWord_6911505 prefixEnd_6911505 3548924110953086438602073 := by
  unfold tailWord_6911505
  simp only [CollatzResearch.WordTrace]
  refine ⟨252083296825805250923375969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168055531217203500615583979 252083296825805250923375969)
  ·
    refine ⟨189062472619353938192531977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252083296825805250923375969 189062472619353938192531977)
    ·
      refine ⟨141796854464515453644398983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189062472619353938192531977 141796854464515453644398983)
      ·
        refine ⟨212695281696773180466598475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141796854464515453644398983 212695281696773180466598475)
        ·
          refine ⟨319042922545159770699897713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212695281696773180466598475 319042922545159770699897713)
          ·
            refine ⟨239282191908869828024923285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319042922545159770699897713 239282191908869828024923285)
            ·
              refine ⟨11216352745728273188668279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 239282191908869828024923285 11216352745728273188668279)
              ·
                refine ⟨16824529118592409783002419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11216352745728273188668279 16824529118592409783002419)
                ·
                  refine ⟨25236793677888614674503629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16824529118592409783002419 25236793677888614674503629)
                  ·
                    refine ⟨9463797629208230502938861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25236793677888614674503629 9463797629208230502938861)
                    ·
                      refine ⟨3548924110953086438602073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9463797629208230502938861 3548924110953086438602073)
                      ·
                        rfl

theorem cell23_6911505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_6911505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911505 prefixEnd_6911505 := by exact prefixLift 6911505
  have htrace : WordTrace (prefixWord ++ tailWord_6911505) baseStart_6911505 baseEnd_6911505 := by
    simpa [prefixWord, tailWord_6911505, baseEnd_6911505] using wordTrace_append hprefix tailTrace_6911505
  have hstable : (prefixWord ++ tailWord_6911505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911505).length < 2 ^ (prefixWord ++ tailWord_6911505).sum := by decide
  have hdescent : baseEnd_6911505 < baseStart_6911505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911539 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 3]
def baseStart_6911539 : Nat := 118140960795 + 6911539 * 2 ^ 59
def prefixEnd_6911539 : Nat := 4983230072969 + 3 ^ 40 * 6911539 * 2
def baseEnd_6911539 : Nat := 3548941569295339305576917

theorem tailTrace_6911539 : CollatzResearch.WordTrace tailWord_6911539 prefixEnd_6911539 3548941569295339305576917 := by
  unfold tailWord_6911539
  simp only [CollatzResearch.WordTrace]
  refine ⟨252084536907682074730113671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168056357938454716486742447 252084536907682074730113671)
  ·
    refine ⟨378126805361523112095170507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252084536907682074730113671 378126805361523112095170507)
    ·
      refine ⟨567190208042284668142755761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378126805361523112095170507 567190208042284668142755761)
      ·
        refine ⟨425392656031713501107066821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567190208042284668142755761 425392656031713501107066821)
        ·
          refine ⟨79761123005946281457575029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425392656031713501107066821 79761123005946281457575029)
          ·
            refine ⟨7477605281807463886647659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79761123005946281457575029 7477605281807463886647659)
            ·
              refine ⟨11216407922711195829971489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7477605281807463886647659 11216407922711195829971489)
              ·
                refine ⟨8412305942033396872478617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11216407922711195829971489 8412305942033396872478617)
                ·
                  refine ⟨6309229456525047654358963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412305942033396872478617 6309229456525047654358963)
                  ·
                    refine ⟨9463844184787571481538445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6309229456525047654358963 9463844184787571481538445)
                    ·
                      refine ⟨3548941569295339305576917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9463844184787571481538445 3548941569295339305576917)
                      ·
                        rfl

theorem cell23_6911539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 3].length) (baseStart_6911539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911539 prefixEnd_6911539 := by exact prefixLift 6911539
  have htrace : WordTrace (prefixWord ++ tailWord_6911539) baseStart_6911539 baseEnd_6911539 := by
    simpa [prefixWord, tailWord_6911539, baseEnd_6911539] using wordTrace_append hprefix tailTrace_6911539
  have hstable : (prefixWord ++ tailWord_6911539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911539).length < 2 ^ (prefixWord ++ tailWord_6911539).sum := by decide
  have hdescent : baseEnd_6911539 < baseStart_6911539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911568 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 7]
def baseStart_6911568 : Nat := 118140960795 + 6911568 * 2 ^ 59
def prefixEnd_6911568 : Nat := 4983230072969 + 3 ^ 40 * 6911568 * 2
def baseEnd_6911568 : Nat := 394328495581591076901587

theorem tailTrace_6911568 : CollatzResearch.WordTrace tailWord_6911568 prefixEnd_6911568 394328495581591076901587 := by
  unfold tailWord_6911568
  simp only [CollatzResearch.WordTrace]
  refine ⟨126042797312288506341459679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168057063083051341788612905 126042797312288506341459679)
  ·
    refine ⟨189064195968432759512189519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126042797312288506341459679 189064195968432759512189519)
    ·
      refine ⟨283596293952649139268284279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189064195968432759512189519 283596293952649139268284279)
      ·
        refine ⟨425394440928973708902426419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283596293952649139268284279 425394440928973708902426419)
        ·
          refine ⟨638091661393460563353639629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425394440928973708902426419 638091661393460563353639629)
          ·
            refine ⟨239284373022547711257614861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 638091661393460563353639629 239284373022547711257614861)
            ·
              refine ⟨89731639883455391721605573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239284373022547711257614861 89731639883455391721605573)
              ·
                refine ⟨16824682478147885947801045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89731639883455391721605573 16824682478147885947801045)
                ·
                  refine ⟨394328495581591076901587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16824682478147885947801045 394328495581591076901587)
                  ·
                    rfl

theorem cell23_6911568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_6911568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911568 prefixEnd_6911568 := by exact prefixLift 6911568
  have htrace : WordTrace (prefixWord ++ tailWord_6911568) baseStart_6911568 baseEnd_6911568 := by
    simpa [prefixWord, tailWord_6911568, baseEnd_6911568] using wordTrace_append hprefix tailTrace_6911568
  have hstable : (prefixWord ++ tailWord_6911568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911568).length < 2 ^ (prefixWord ++ tailWord_6911568).sum := by decide
  have hdescent : baseEnd_6911568 < baseStart_6911568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911574 : List Nat := [5, 2, 2, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6911574 : Nat := 118140960795 + 6911574 * 2 ^ 59
def prefixEnd_6911574 : Nat := 4983230072969 + 3 ^ 40 * 6911574 * 2
def baseEnd_6911574 : Nat := 3548959541118246668639257

theorem tailTrace_6911574 : CollatzResearch.WordTrace tailWord_6911574 prefixEnd_6911574 3548959541118246668639257 := by
  unfold tailWord_6911574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15755363341409704731727361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168057208975036850471758517 15755363341409704731727361)
  ·
    refine ⟨11816522506057278548795521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15755363341409704731727361 11816522506057278548795521)
    ·
      refine ⟨8862391879542958911596641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11816522506057278548795521 8862391879542958911596641)
      ·
        refine ⟨6646793909657219183697481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8862391879542958911596641 6646793909657219183697481)
        ·
          refine ⟨4985095432242914387773111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6646793909657219183697481 4985095432242914387773111)
          ·
            refine ⟨7477643148364371581659667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985095432242914387773111 7477643148364371581659667)
            ·
              refine ⟨11216464722546557372489501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7477643148364371581659667 11216464722546557372489501)
              ·
                refine ⟨4206174270954959014683563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11216464722546557372489501 4206174270954959014683563)
                ·
                  refine ⟨6309261406432438522025345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206174270954959014683563 6309261406432438522025345)
                  ·
                    refine ⟨4731946054824328891519009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6309261406432438522025345 4731946054824328891519009)
                    ·
                      refine ⟨3548959541118246668639257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731946054824328891519009 3548959541118246668639257)
                      ·
                        rfl

theorem cell23_6911574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6911574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911574 prefixEnd_6911574 := by exact prefixLift 6911574
  have htrace : WordTrace (prefixWord ++ tailWord_6911574) baseStart_6911574 baseEnd_6911574 := by
    simpa [prefixWord, tailWord_6911574, baseEnd_6911574] using wordTrace_append hprefix tailTrace_6911574
  have hstable : (prefixWord ++ tailWord_6911574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911574).length < 2 ^ (prefixWord ++ tailWord_6911574).sum := by decide
  have hdescent : baseEnd_6911574 < baseStart_6911574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911602 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 7]
def baseStart_6911602 : Nat := 118140960795 + 6911602 * 2 ^ 59
def prefixEnd_6911602 : Nat := 4983230072969 + 3 ^ 40 * 6911602 * 2
def baseEnd_6911602 : Nat := 394330435397396951009903

theorem tailTrace_6911602 : CollatzResearch.WordTrace tailWord_6911602 prefixEnd_6911602 394330435397396951009903 := by
  unfold tailWord_6911602
  simp only [CollatzResearch.WordTrace]
  refine ⟨63021708676613459122414265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168057889804302557659771373 63021708676613459122414265)
  ·
    refine ⟨47266281507460094341810699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63021708676613459122414265 47266281507460094341810699)
    ·
      refine ⟨70899422261190141512716049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47266281507460094341810699 70899422261190141512716049)
      ·
        refine ⟨53174566695892606134537037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70899422261190141512716049 53174566695892606134537037)
        ·
          refine ⟨19940462510959727300451389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53174566695892606134537037 19940462510959727300451389)
          ·
            refine ⟨7477673441609897737669271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19940462510959727300451389 7477673441609897737669271)
            ·
              refine ⟨11216510162414846606503907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7477673441609897737669271 11216510162414846606503907)
              ·
                refine ⟨16824765243622269909755861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11216510162414846606503907 16824765243622269909755861)
                ·
                  refine ⟨394330435397396951009903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16824765243622269909755861 394330435397396951009903)
                  ·
                    rfl

theorem cell23_6911602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_6911602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911602 prefixEnd_6911602 := by exact prefixLift 6911602
  have htrace : WordTrace (prefixWord ++ tailWord_6911602) baseStart_6911602 baseEnd_6911602 := by
    simpa [prefixWord, tailWord_6911602, baseEnd_6911602] using wordTrace_append hprefix tailTrace_6911602
  have hstable : (prefixWord ++ tailWord_6911602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911602).length < 2 ^ (prefixWord ++ tailWord_6911602).sum := by decide
  have hdescent : baseEnd_6911602 < baseStart_6911602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911613 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_6911613 : Nat := 118140960795 + 6911613 * 2 ^ 59
def prefixEnd_6911613 : Nat := 4983230072969 + 3 ^ 40 * 6911613 * 2
def baseEnd_6911613 : Nat := 3548979566863772016051577

theorem tailTrace_6911613 : CollatzResearch.WordTrace tailWord_6911613 prefixEnd_6911613 3548979566863772016051577 := by
  unfold tailWord_6911613
  simp only [CollatzResearch.WordTrace]
  refine ⟨252087235909413985368307493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168058157272942656912204995 252087235909413985368307493)
  ·
    refine ⟨47266356733015122256557655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252087235909413985368307493 47266356733015122256557655)
    ·
      refine ⟨70899535099522683384836483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47266356733015122256557655 70899535099522683384836483)
      ·
        refine ⟨106349302649284025077254725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70899535099522683384836483 106349302649284025077254725)
        ·
          refine ⟨19940494246740754701985261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106349302649284025077254725 19940494246740754701985261)
          ·
            refine ⟨7477685342527783013244473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19940494246740754701985261 7477685342527783013244473)
            ·
              refine ⟨5608264006895837259933355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7477685342527783013244473 5608264006895837259933355)
              ·
                refine ⟨8412396010343755889900033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608264006895837259933355 8412396010343755889900033)
                ·
                  refine ⟨6309297007757816917425025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412396010343755889900033 6309297007757816917425025)
                  ·
                    refine ⟨4731972755818362688068769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6309297007757816917425025 4731972755818362688068769)
                    ·
                      refine ⟨3548979566863772016051577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4731972755818362688068769 3548979566863772016051577)
                      ·
                        rfl

theorem cell23_6911613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_6911613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911613 prefixEnd_6911613 := by exact prefixLift 6911613
  have htrace : WordTrace (prefixWord ++ tailWord_6911613) baseStart_6911613 baseEnd_6911613 := by
    simpa [prefixWord, tailWord_6911613, baseEnd_6911613] using wordTrace_append hprefix tailTrace_6911613
  have hstable : (prefixWord ++ tailWord_6911613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911613).length < 2 ^ (prefixWord ++ tailWord_6911613).sum := by decide
  have hdescent : baseEnd_6911613 < baseStart_6911613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911652 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_6911652 : Nat := 118140960795 + 6911652 * 2 ^ 59
def prefixEnd_6911652 : Nat := 4983230072969 + 3 ^ 40 * 6911652 * 2
def baseEnd_6911652 : Nat := 3548999592609297363463897

theorem tailTrace_6911652 : CollatzResearch.WordTrace tailWord_6911652 prefixEnd_6911652 3548999592609297363463897 := by
  unfold tailWord_6911652
  simp only [CollatzResearch.WordTrace]
  refine ⟨126044329178136347514488605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168059105570848463352651473 126044329178136347514488605)
  ·
    refine ⟨47266623441801130317933227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126044329178136347514488605 47266623441801130317933227)
    ·
      refine ⟨70899935162701695476899841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47266623441801130317933227 70899935162701695476899841)
      ·
        refine ⟨53174951372026271607674881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70899935162701695476899841 53174951372026271607674881)
        ·
          refine ⟨39881213529019703705756161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53174951372026271607674881 39881213529019703705756161)
          ·
            refine ⟨29910910146764777779317121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39881213529019703705756161 29910910146764777779317121)
            ·
              refine ⟨22433182610073583334487841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29910910146764777779317121 22433182610073583334487841)
              ·
                refine ⟨16824886957555187500865881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22433182610073583334487841 16824886957555187500865881)
                ·
                  refine ⟨12618665218166390625649411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16824886957555187500865881 12618665218166390625649411)
                  ·
                    refine ⟨18927997827249585938474117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12618665218166390625649411 18927997827249585938474117)
                    ·
                      refine ⟨3548999592609297363463897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18927997827249585938474117 3548999592609297363463897)
                      ·
                        rfl

theorem cell23_6911652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_6911652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911652 prefixEnd_6911652 := by exact prefixLift 6911652
  have htrace : WordTrace (prefixWord ++ tailWord_6911652) baseStart_6911652 baseEnd_6911652 := by
    simpa [prefixWord, tailWord_6911652, baseEnd_6911652] using wordTrace_append hprefix tailTrace_6911652
  have hstable : (prefixWord ++ tailWord_6911652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911652).length < 2 ^ (prefixWord ++ tailWord_6911652).sum := by decide
  have hdescent : baseEnd_6911652 < baseStart_6911652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911685 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_6911685 : Nat := 118140960795 + 6911685 * 2 ^ 59
def prefixEnd_6911685 : Nat := 4983230072969 + 3 ^ 40 * 6911685 * 2
def baseEnd_6911685 : Nat := 3549016537470895734351245

theorem tailTrace_6911685 : CollatzResearch.WordTrace tailWord_6911685 prefixEnd_6911685 3549016537470895734351245 := by
  unfold tailWord_6911685
  simp only [CollatzResearch.WordTrace]
  refine ⟨252089861965153141664928509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168059907976768761109952339 252089861965153141664928509)
  ·
    refine ⟨94533698236932428124348191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252089861965153141664928509 94533698236932428124348191)
    ·
      refine ⟨141800547355398642186522287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94533698236932428124348191 141800547355398642186522287)
      ·
        refine ⟨212700821033097963279783431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141800547355398642186522287 212700821033097963279783431)
        ·
          refine ⟨319051231549646944919675147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212700821033097963279783431 319051231549646944919675147)
          ·
            refine ⟨478576847324470417379512721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319051231549646944919675147 478576847324470417379512721)
            ·
              refine ⟨358932635493352813034634541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478576847324470417379512721 358932635493352813034634541)
              ·
                refine ⟨134599738310007304887987953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358932635493352813034634541 134599738310007304887987953)
                ·
                  refine ⟨100949803732505478665990965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134599738310007304887987953 100949803732505478665990965)
                  ·
                    refine ⟨9464044099922388624936653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100949803732505478665990965 9464044099922388624936653)
                    ·
                      refine ⟨3549016537470895734351245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464044099922388624936653 3549016537470895734351245)
                      ·
                        rfl

theorem cell23_6911685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_6911685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911685 prefixEnd_6911685 := by exact prefixLift 6911685
  have htrace : WordTrace (prefixWord ++ tailWord_6911685) baseStart_6911685 baseEnd_6911685 := by
    simpa [prefixWord, tailWord_6911685, baseEnd_6911685] using wordTrace_append hprefix tailTrace_6911685
  have hstable : (prefixWord ++ tailWord_6911685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911685).length < 2 ^ (prefixWord ++ tailWord_6911685).sum := by decide
  have hdescent : baseEnd_6911685 < baseStart_6911685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911686 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6911686 : Nat := 118140960795 + 6911686 * 2 ^ 59
def prefixEnd_6911686 : Nat := 4983230072969 + 3 ^ 40 * 6911686 * 2
def baseEnd_6911686 : Nat := 3549017050951550230438741

theorem tailTrace_6911686 : CollatzResearch.WordTrace tailWord_6911686 prefixEnd_6911686 3549017050951550230438741 := by
  unfold tailWord_6911686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877809326192172463616091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168059932292099679223809941 7877809326192172463616091)
  ·
    refine ⟨11816713989288258695424137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7877809326192172463616091 11816713989288258695424137)
    ·
      refine ⟨8862535491966194021568103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11816713989288258695424137 8862535491966194021568103)
      ·
        refine ⟨13293803237949291032352155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8862535491966194021568103 13293803237949291032352155)
        ·
          refine ⟨19940704856923936548528233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13293803237949291032352155 19940704856923936548528233)
          ·
            refine ⟨14955528642692952411396175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19940704856923936548528233 14955528642692952411396175)
            ·
              refine ⟨22433292964039428617094263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14955528642692952411396175 22433292964039428617094263)
              ·
                refine ⟨33649939446059142925641395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22433292964039428617094263 33649939446059142925641395)
                ·
                  refine ⟨50474909169088714388462093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33649939446059142925641395 50474909169088714388462093)
                  ·
                    refine ⟨18928090938408267895673285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50474909169088714388462093 18928090938408267895673285)
                    ·
                      refine ⟨3549017050951550230438741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18928090938408267895673285 3549017050951550230438741)
                      ·
                        rfl

theorem cell23_6911686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6911686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911686 prefixEnd_6911686 := by exact prefixLift 6911686
  have htrace : WordTrace (prefixWord ++ tailWord_6911686) baseStart_6911686 baseEnd_6911686 := by
    simpa [prefixWord, tailWord_6911686, baseEnd_6911686] using wordTrace_append hprefix tailTrace_6911686
  have hstable : (prefixWord ++ tailWord_6911686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911686).length < 2 ^ (prefixWord ++ tailWord_6911686).sum := by decide
  have hdescent : baseEnd_6911686 < baseStart_6911686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911709 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 8]
def baseStart_6911709 : Nat := 118140960795 + 6911709 * 2 ^ 59
def prefixEnd_6911709 : Nat := 4983230072969 + 3 ^ 40 * 6911709 * 2
def baseEnd_6911709 : Nat := 394336540111844848939015

theorem tailTrace_6911709 : CollatzResearch.WordTrace tailWord_6911709 prefixEnd_6911709 394336540111844848939015 := by
  unfold tailWord_6911709
  simp only [CollatzResearch.WordTrace]
  refine ⟨252090737317066193763802181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168060491544710795842534787 252090737317066193763802181)
  ·
    refine ⟨47267013246949911330712909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252090737317066193763802181 47267013246949911330712909)
    ·
      refine ⟨17725129967606216749017341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47267013246949911330712909 17725129967606216749017341)
      ·
        refine ⟨6646923737852331280881503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17725129967606216749017341 6646923737852331280881503)
        ·
          refine ⟨9970385606778496921322255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6646923737852331280881503 9970385606778496921322255)
          ·
            refine ⟨14955578410167745381983383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970385606778496921322255 14955578410167745381983383)
            ·
              refine ⟨22433367615251618072975075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14955578410167745381983383 22433367615251618072975075)
              ·
                refine ⟨33650051422877427109462613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22433367615251618072975075 33650051422877427109462613)
                ·
                  refine ⟨394336540111844848939015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33650051422877427109462613 394336540111844848939015)
                  ·
                    rfl

theorem cell23_6911709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_6911709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911709 prefixEnd_6911709 := by exact prefixLift 6911709
  have htrace : WordTrace (prefixWord ++ tailWord_6911709) baseStart_6911709 baseEnd_6911709 := by
    simpa [prefixWord, tailWord_6911709, baseEnd_6911709] using wordTrace_append hprefix tailTrace_6911709
  have hstable : (prefixWord ++ tailWord_6911709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911709).length < 2 ^ (prefixWord ++ tailWord_6911709).sum := by decide
  have hdescent : baseEnd_6911709 < baseStart_6911709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911746 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_6911746 : Nat := 118140960795 + 6911746 * 2 ^ 59
def prefixEnd_6911746 : Nat := 4983230072969 + 3 ^ 40 * 6911746 * 2
def baseEnd_6911746 : Nat := 3549047859790819995688465

theorem tailTrace_6911746 : CollatzResearch.WordTrace tailWord_6911746 prefixEnd_6911746 3549047859790819995688465 := by
  unfold tailWord_6911746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63023021704483037270724773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168061391211954766055266061 63023021704483037270724773)
  ·
    refine ⟨11816816569590569488260895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63023021704483037270724773 11816816569590569488260895)
    ·
      refine ⟨17725224854385854232391343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11816816569590569488260895 17725224854385854232391343)
      ·
        refine ⟨26587837281578781348587015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17725224854385854232391343 26587837281578781348587015)
        ·
          refine ⟨39881755922368172022880523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26587837281578781348587015 39881755922368172022880523)
          ·
            refine ⟨59822633883552258034320785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39881755922368172022880523 59822633883552258034320785)
            ·
              refine ⟨44866975412664193525740589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59822633883552258034320785 44866975412664193525740589)
              ·
                refine ⟨16825115779749072572152721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44866975412664193525740589 16825115779749072572152721)
                ·
                  refine ⟨12618836834811804429114541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16825115779749072572152721 12618836834811804429114541)
                  ·
                    refine ⟨4732063813054426660917953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12618836834811804429114541 4732063813054426660917953)
                    ·
                      refine ⟨3549047859790819995688465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732063813054426660917953 3549047859790819995688465)
                      ·
                        rfl

theorem cell23_6911746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_6911746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911746 prefixEnd_6911746 := by exact prefixLift 6911746
  have htrace : WordTrace (prefixWord ++ tailWord_6911746) baseStart_6911746 baseEnd_6911746 := by
    simpa [prefixWord, tailWord_6911746, baseEnd_6911746] using wordTrace_append hprefix tailTrace_6911746
  have hstable : (prefixWord ++ tailWord_6911746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911746).length < 2 ^ (prefixWord ++ tailWord_6911746).sum := by decide
  have hdescent : baseEnd_6911746 < baseStart_6911746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911752 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 6, 4]
def baseStart_6911752 : Nat := 118140960795 + 6911752 * 2 ^ 59
def prefixEnd_6911752 : Nat := 4983230072969 + 3 ^ 40 * 6911752 * 2
def baseEnd_6911752 : Nat := 1183016980224915657404479

theorem tailTrace_6911752 : CollatzResearch.WordTrace tailWord_6911752 prefixEnd_6911752 1183016980224915657404479 := by
  unfold tailWord_6911752
  simp only [CollatzResearch.WordTrace]
  refine ⟨126046152827955206053808755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168061537103940274738411673 126046152827955206053808755)
  ·
    refine ⟨189069229241932809080713133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126046152827955206053808755 189069229241932809080713133)
    ·
      refine ⟨70900960965724803405267425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189069229241932809080713133 70900960965724803405267425)
      ·
        refine ⟨53175720724293602553950569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70900960965724803405267425 53175720724293602553950569)
        ·
          refine ⟨39881790543220201915462927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53175720724293602553950569 39881790543220201915462927)
          ·
            refine ⟨59822685814830302873194391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39881790543220201915462927 59822685814830302873194391)
            ·
              refine ⟨89734028722245454309791587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59822685814830302873194391 89734028722245454309791587)
              ·
                refine ⟨134601043083368181464687381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89734028722245454309791587 134601043083368181464687381)
                ·
                  refine ⟨6309423894532883506157221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134601043083368181464687381 6309423894532883506157221)
                  ·
                    refine ⟨1183016980224915657404479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6309423894532883506157221 1183016980224915657404479)
                    ·
                      rfl

theorem cell23_6911752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_6911752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911752 prefixEnd_6911752 := by exact prefixLift 6911752
  have htrace : WordTrace (prefixWord ++ tailWord_6911752) baseStart_6911752 baseEnd_6911752 := by
    simpa [prefixWord, tailWord_6911752, baseEnd_6911752] using wordTrace_append hprefix tailTrace_6911752
  have hstable : (prefixWord ++ tailWord_6911752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911752).length < 2 ^ (prefixWord ++ tailWord_6911752).sum := by decide
  have hdescent : baseEnd_6911752 < baseStart_6911752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911765 : List Nat := [1, 3, 2, 1, 2, 3, 11]
def baseStart_6911765 : Nat := 118140960795 + 6911765 * 2 ^ 59
def prefixEnd_6911765 : Nat := 4983230072969 + 3 ^ 40 * 6911765 * 2
def baseEnd_6911765 : Nat := 43815526122509326189517

theorem tailTrace_6911765 : CollatzResearch.WordTrace tailWord_6911765 prefixEnd_6911765 43815526122509326189517 := by
  unfold tailWord_6911765
  simp only [CollatzResearch.WordTrace]
  refine ⟨252092779804863315327840749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168061853203242210218560499 252092779804863315327840749)
  ·
    refine ⟨94534792426823743247940281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252092779804863315327840749 94534792426823743247940281)
    ·
      refine ⟨70901094320117807435955211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94534792426823743247940281 70901094320117807435955211)
      ·
        refine ⟨106351641480176711153932817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70901094320117807435955211 106351641480176711153932817)
        ·
          refine ⟨79763731110132533365449613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106351641480176711153932817 79763731110132533365449613)
          ·
            refine ⟨29911399166299700012043605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79763731110132533365449613 29911399166299700012043605)
            ·
              refine ⟨43815526122509326189517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29911399166299700012043605 43815526122509326189517)
              ·
                rfl

theorem cell23_6911765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 11].length) (baseStart_6911765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911765 prefixEnd_6911765 := by exact prefixLift 6911765
  have htrace : WordTrace (prefixWord ++ tailWord_6911765) baseStart_6911765 baseEnd_6911765 := by
    simpa [prefixWord, tailWord_6911765, baseEnd_6911765] using wordTrace_append hprefix tailTrace_6911765
  have hstable : (prefixWord ++ tailWord_6911765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911765).length < 2 ^ (prefixWord ++ tailWord_6911765).sum := by decide
  have hdescent : baseEnd_6911765 < baseStart_6911765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911796 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_6911796 : Nat := 118140960795 + 6911796 * 2 ^ 59
def prefixEnd_6911796 : Nat := 4983230072969 + 3 ^ 40 * 6911796 * 2
def baseEnd_6911796 : Nat := 3549073533823544800063235

theorem tailTrace_6911796 : CollatzResearch.WordTrace tailWord_6911796 prefixEnd_6911796 3549073533823544800063235 := by
  unfold tailWord_6911796
  simp only [CollatzResearch.WordTrace]
  refine ⟨126046955233875503811109621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168062606978500671748146161 126046955233875503811109621)
  ·
    refine ⟨11816902053175828482291527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126046955233875503811109621 11816902053175828482291527)
    ·
      refine ⟨17725353079763742723437291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11816902053175828482291527 17725353079763742723437291)
      ·
        refine ⟨26588029619645614085155937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17725353079763742723437291 26588029619645614085155937)
        ·
          refine ⟨19941022214734210563866953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26588029619645614085155937 19941022214734210563866953)
          ·
            refine ⟨14955766661050657922900215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19941022214734210563866953 14955766661050657922900215)
            ·
              refine ⟨22433649991575986884350323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14955766661050657922900215 22433649991575986884350323)
              ·
                refine ⟨33650474987363980326525485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22433649991575986884350323 33650474987363980326525485)
                ·
                  refine ⟨12618928120261492622447057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33650474987363980326525485 12618928120261492622447057)
                  ·
                    refine ⟨9464196090196119466835293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12618928120261492622447057 9464196090196119466835293)
                    ·
                      refine ⟨3549073533823544800063235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464196090196119466835293 3549073533823544800063235)
                      ·
                        rfl

theorem cell23_6911796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_6911796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911796 prefixEnd_6911796 := by exact prefixLift 6911796
  have htrace : WordTrace (prefixWord ++ tailWord_6911796) baseStart_6911796 baseEnd_6911796 := by
    simpa [prefixWord, tailWord_6911796, baseEnd_6911796] using wordTrace_append hprefix tailTrace_6911796
  have hstable : (prefixWord ++ tailWord_6911796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911796).length < 2 ^ (prefixWord ++ tailWord_6911796).sum := by decide
  have hdescent : baseEnd_6911796 < baseStart_6911796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911826 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_6911826 : Nat := 118140960795 + 6911826 * 2 ^ 59
def prefixEnd_6911826 : Nat := 4983230072969 + 3 ^ 40 * 6911826 * 2
def baseEnd_6911826 : Nat := 3549088938243179682688097

theorem tailTrace_6911826 : CollatzResearch.WordTrace tailWord_6911826 prefixEnd_6911826 3549088938243179682688097 := by
  unfold tailWord_6911826
  simp only [CollatzResearch.WordTrace]
  refine ⟨63023751164410580686452833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168063336438428215163874221 63023751164410580686452833)
  ·
    refine ⟨47267813373307935514839625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63023751164410580686452833 47267813373307935514839625)
    ·
      refine ⟨35450860029980951636129719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47267813373307935514839625 35450860029980951636129719)
      ·
        refine ⟨53176290044971427454194579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35450860029980951636129719 53176290044971427454194579)
        ·
          refine ⟨79764435067457141181291869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53176290044971427454194579 79764435067457141181291869)
          ·
            refine ⟨29911663150296427942984451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79764435067457141181291869 29911663150296427942984451)
            ·
              refine ⟨44867494725444641914476677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29911663150296427942984451 44867494725444641914476677)
              ·
                refine ⟨8412655261020870358964377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44867494725444641914476677 8412655261020870358964377)
                ·
                  refine ⟨6309491445765652769223283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412655261020870358964377 6309491445765652769223283)
                  ·
                    refine ⟨9464237168648479153834925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6309491445765652769223283 9464237168648479153834925)
                    ·
                      refine ⟨3549088938243179682688097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464237168648479153834925 3549088938243179682688097)
                      ·
                        rfl

theorem cell23_6911826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_6911826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911826 prefixEnd_6911826 := by exact prefixLift 6911826
  have htrace : WordTrace (prefixWord ++ tailWord_6911826) baseStart_6911826 baseEnd_6911826 := by
    simpa [prefixWord, tailWord_6911826, baseEnd_6911826] using wordTrace_append hprefix tailTrace_6911826
  have hstable : (prefixWord ++ tailWord_6911826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911826).length < 2 ^ (prefixWord ++ tailWord_6911826).sum := by decide
  have hdescent : baseEnd_6911826 < baseStart_6911826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911870 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6911870 : Nat := 118140960795 + 6911870 * 2 ^ 59
def prefixEnd_6911870 : Nat := 4983230072969 + 3 ^ 40 * 6911870 * 2
def baseEnd_6911870 : Nat := 3549111531391977510537895

theorem tailTrace_6911870 : CollatzResearch.WordTrace tailWord_6911870 prefixEnd_6911870 3549111531391977510537895 := by
  unfold tailWord_6911870
  simp only [CollatzResearch.WordTrace]
  refine ⟨31512076183685364782551633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168064406312988612173608709 31512076183685364782551633)
  ·
    refine ⟨23634057137764023586913725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31512076183685364782551633 23634057137764023586913725)
    ·
      refine ⟨8862771426661508845092647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23634057137764023586913725 8862771426661508845092647)
      ·
        refine ⟨13294157139992263267638971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8862771426661508845092647 13294157139992263267638971)
        ·
          refine ⟨19941235709988394901458457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13294157139992263267638971 19941235709988394901458457)
          ·
            refine ⟨14955926782491296176093843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19941235709988394901458457 14955926782491296176093843)
            ·
              refine ⟨22433890173736944264140765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14955926782491296176093843 22433890173736944264140765)
              ·
                refine ⟨8412708815151354099052787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22433890173736944264140765 8412708815151354099052787)
                ·
                  refine ⟨12619063222727031148579181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412708815151354099052787 12619063222727031148579181)
                  ·
                    refine ⟨4732148708522636680717193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12619063222727031148579181 4732148708522636680717193)
                    ·
                      refine ⟨3549111531391977510537895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732148708522636680717193 3549111531391977510537895)
                      ·
                        rfl

theorem cell23_6911870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6911870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911870 prefixEnd_6911870 := by exact prefixLift 6911870
  have htrace : WordTrace (prefixWord ++ tailWord_6911870) baseStart_6911870 baseEnd_6911870 := by
    simpa [prefixWord, tailWord_6911870, baseEnd_6911870] using wordTrace_append hprefix tailTrace_6911870
  have hstable : (prefixWord ++ tailWord_6911870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911870).length < 2 ^ (prefixWord ++ tailWord_6911870).sum := by decide
  have hdescent : baseEnd_6911870 < baseStart_6911870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911889 : List Nat := [1, 2, 2, 1, 1, 1, 6, 4, 5]
def baseStart_6911889 : Nat := 118140960795 + 6911889 * 2 ^ 59
def prefixEnd_6911889 : Nat := 4983230072969 + 3 ^ 40 * 6911889 * 2
def baseEnd_6911889 : Nat := 394346809724934770688923

theorem tailTrace_6911889 : CollatzResearch.WordTrace tailWord_6911889 prefixEnd_6911889 394346809724934770688923 := by
  unfold tailWord_6911889
  simp only [CollatzResearch.WordTrace]
  refine ⟨252097302456414084505354721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168064868304276056336903147 252097302456414084505354721)
  ·
    refine ⟨189072976842310563379016041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252097302456414084505354721 189072976842310563379016041)
    ·
      refine ⟨141804732631732922534262031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189072976842310563379016041 141804732631732922534262031)
      ·
        refine ⟨212707098947599383801393047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141804732631732922534262031 212707098947599383801393047)
        ·
          refine ⟨319060648421399075702089571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212707098947599383801393047 319060648421399075702089571)
          ·
            refine ⟨478590972632098613553134357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319060648421399075702089571 478590972632098613553134357)
            ·
              refine ⟨22433951842129622510303173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 478590972632098613553134357 22433951842129622510303173)
              ·
                refine ⟨4206365970399304220681845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22433951842129622510303173 4206365970399304220681845)
                ·
                  refine ⟨394346809724934770688923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4206365970399304220681845 394346809724934770688923)
                  ·
                    rfl

theorem cell23_6911889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 5].length) (baseStart_6911889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911889 prefixEnd_6911889 := by exact prefixLift 6911889
  have htrace : WordTrace (prefixWord ++ tailWord_6911889) baseStart_6911889 baseEnd_6911889 := by
    simpa [prefixWord, tailWord_6911889, baseEnd_6911889] using wordTrace_append hprefix tailTrace_6911889
  have hstable : (prefixWord ++ tailWord_6911889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911889).length < 2 ^ (prefixWord ++ tailWord_6911889).sum := by decide
  have hdescent : baseEnd_6911889 < baseStart_6911889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911894 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6911894 : Nat := 118140960795 + 6911894 * 2 ^ 59
def prefixEnd_6911894 : Nat := 4983230072969 + 3 ^ 40 * 6911894 * 2
def baseEnd_6911894 : Nat := 3549123854927685416637785

theorem tailTrace_6911894 : CollatzResearch.WordTrace tailWord_6911894 prefixEnd_6911894 3549123854927685416637785 := by
  unfold tailWord_6911894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15756092801337248147455421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168064989880930646906191157 15756092801337248147455421)
  ·
    refine ⟨5908534800501468055295783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15756092801337248147455421 5908534800501468055295783)
    ·
      refine ⟨8862802200752202082943675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908534800501468055295783 8862802200752202082943675)
      ·
        refine ⟨13294203301128303124415513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8862802200752202082943675 13294203301128303124415513)
        ·
          refine ⟨9970652475846227343311635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13294203301128303124415513 9970652475846227343311635)
          ·
            refine ⟨14955978713769341014967453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970652475846227343311635 14955978713769341014967453)
            ·
              refine ⟨5608492017663502880612795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14955978713769341014967453 5608492017663502880612795)
              ·
                refine ⟨8412738026495254320919193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608492017663502880612795 8412738026495254320919193)
                ·
                  refine ⟨6309553519871440740689395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412738026495254320919193 6309553519871440740689395)
                  ·
                    refine ⟨9464330279807161111034093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6309553519871440740689395 9464330279807161111034093)
                    ·
                      refine ⟨3549123854927685416637785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464330279807161111034093 3549123854927685416637785)
                      ·
                        rfl

theorem cell23_6911894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6911894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911894 prefixEnd_6911894 := by exact prefixLift 6911894
  have htrace : WordTrace (prefixWord ++ tailWord_6911894) baseStart_6911894 baseEnd_6911894 := by
    simpa [prefixWord, tailWord_6911894, baseEnd_6911894] using wordTrace_append hprefix tailTrace_6911894
  have hstable : (prefixWord ++ tailWord_6911894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911894).length < 2 ^ (prefixWord ++ tailWord_6911894).sum := by decide
  have hdescent : baseEnd_6911894 < baseStart_6911894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911909 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 2, 5, 2]
def baseStart_6911909 : Nat := 118140960795 + 6911909 * 2 ^ 59
def prefixEnd_6911909 : Nat := 4983230072969 + 3 ^ 40 * 6911909 * 2
def baseEnd_6911909 : Nat := 3549131557137502857950215

theorem tailTrace_6911909 : CollatzResearch.WordTrace tailWord_6911909 prefixEnd_6911909 3549131557137502857950215 := by
  unfold tailWord_6911909
  simp only [CollatzResearch.WordTrace]
  refine ⟨252098031916341627921082781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168065354610894418614055187 252098031916341627921082781)
  ·
    refine ⟨94536761968628110470406043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252098031916341627921082781 94536761968628110470406043)
    ·
      refine ⟨141805142952942165705609065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94536761968628110470406043 141805142952942165705609065)
      ·
        refine ⟨106353857214706624279206799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141805142952942165705609065 106353857214706624279206799)
        ·
          refine ⟨159530785822059936418810199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106353857214706624279206799 159530785822059936418810199)
          ·
            refine ⟨239296178733089904628215299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159530785822059936418810199 239296178733089904628215299)
            ·
              refine ⟨358944268099634856942322949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239296178733089904628215299 358944268099634856942322949)
              ·
                refine ⟨67302050268681535676685553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358944268099634856942322949 67302050268681535676685553)
                ·
                  refine ⟨50476537701511151757514165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67302050268681535676685553 50476537701511151757514165)
                  ·
                    refine ⟨4732175409516670477266953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50476537701511151757514165 4732175409516670477266953)
                    ·
                      refine ⟨3549131557137502857950215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732175409516670477266953 3549131557137502857950215)
                      ·
                        rfl

theorem cell23_6911909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_6911909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911909 prefixEnd_6911909 := by exact prefixLift 6911909
  have htrace : WordTrace (prefixWord ++ tailWord_6911909) baseStart_6911909 baseEnd_6911909 := by
    simpa [prefixWord, tailWord_6911909, baseEnd_6911909] using wordTrace_append hprefix tailTrace_6911909
  have hstable : (prefixWord ++ tailWord_6911909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911909).length < 2 ^ (prefixWord ++ tailWord_6911909).sum := by decide
  have hdescent : baseEnd_6911909 < baseStart_6911909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911952 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_6911952 : Nat := 118140960795 + 6911952 * 2 ^ 59
def prefixEnd_6911952 : Nat := 4983230072969 + 3 ^ 40 * 6911952 * 2
def baseEnd_6911952 : Nat := 3549153636805646189712517

theorem tailTrace_6911952 : CollatzResearch.WordTrace tailWord_6911952 prefixEnd_6911952 3549153636805646189712517 := by
  unfold tailWord_6911952
  simp only [CollatzResearch.WordTrace]
  refine ⟨126049800127592923132449055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168066400170123897509932073 126049800127592923132449055)
  ·
    refine ⟨189074700191389384698673583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126049800127592923132449055 189074700191389384698673583)
    ·
      refine ⟨283612050287084077048010375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189074700191389384698673583 283612050287084077048010375)
      ·
        refine ⟨425418075430626115572015563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283612050287084077048010375 425418075430626115572015563)
        ·
          refine ⟨638127113145939173358023345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425418075430626115572015563 638127113145939173358023345)
          ·
            refine ⟨478595334859454380018517509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638127113145939173358023345 478595334859454380018517509)
            ·
              refine ⟨89736625286147696253472033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 478595334859454380018517509 89736625286147696253472033)
              ·
                refine ⟨67302468964610772190104025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89736625286147696253472033 67302468964610772190104025)
                ·
                  refine ⟨50476851723458079142578019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67302468964610772190104025 50476851723458079142578019)
                  ·
                    refine ⟨75715277585187118713867029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50476851723458079142578019 75715277585187118713867029)
                    ·
                      refine ⟨3549153636805646189712517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75715277585187118713867029 3549153636805646189712517)
                      ·
                        rfl

theorem cell23_6911952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_6911952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911952 prefixEnd_6911952 := by exact prefixLift 6911952
  have htrace : WordTrace (prefixWord ++ tailWord_6911952) baseStart_6911952 baseEnd_6911952 := by
    simpa [prefixWord, tailWord_6911952, baseEnd_6911952] using wordTrace_append hprefix tailTrace_6911952
  have hstable : (prefixWord ++ tailWord_6911952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911952).length < 2 ^ (prefixWord ++ tailWord_6911952).sum := by decide
  have hdescent : baseEnd_6911952 < baseStart_6911952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911956 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_6911956 : Nat := 118140960795 + 6911956 * 2 ^ 59
def prefixEnd_6911956 : Nat := 4983230072969 + 3 ^ 40 * 6911956 * 2
def baseEnd_6911956 : Nat := 3549155690728264174062499

theorem tailTrace_6911956 : CollatzResearch.WordTrace tailWord_6911956 prefixEnd_6911956 3549155690728264174062499 := by
  unfold tailWord_6911956
  simp only [CollatzResearch.WordTrace]
  refine ⟨126049873073585677474021861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168066497431447569965362481 126049873073585677474021861)
  ·
    refine ⟨23634351201297314526379099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126049873073585677474021861 23634351201297314526379099)
    ·
      refine ⟨35451526801945971789568649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23634351201297314526379099 35451526801945971789568649)
      ·
        refine ⟨26588645101459478842176487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35451526801945971789568649 26588645101459478842176487)
        ·
          refine ⟨39882967652189218263264731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26588645101459478842176487 39882967652189218263264731)
          ·
            refine ⟨59824451478283827394897097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39882967652189218263264731 59824451478283827394897097)
            ·
              refine ⟨44868338608712870546172823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59824451478283827394897097 44868338608712870546172823)
              ·
                refine ⟨67302507913069305819259235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44868338608712870546172823 67302507913069305819259235)
                ·
                  refine ⟨100953761869603958728888853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67302507913069305819259235 100953761869603958728888853)
                  ·
                    refine ⟨4732207587637685565416665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100953761869603958728888853 4732207587637685565416665)
                    ·
                      refine ⟨3549155690728264174062499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732207587637685565416665 3549155690728264174062499)
                      ·
                        rfl

theorem cell23_6911956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_6911956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911956 prefixEnd_6911956 := by exact prefixLift 6911956
  have htrace : WordTrace (prefixWord ++ tailWord_6911956) baseStart_6911956 baseEnd_6911956 := by
    simpa [prefixWord, tailWord_6911956, baseEnd_6911956] using wordTrace_append hprefix tailTrace_6911956
  have hstable : (prefixWord ++ tailWord_6911956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911956).length < 2 ^ (prefixWord ++ tailWord_6911956).sum := by decide
  have hdescent : baseEnd_6911956 < baseStart_6911956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6911959 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_6911959 : Nat := 118140960795 + 6911959 * 2 ^ 59
def prefixEnd_6911959 : Nat := 4983230072969 + 3 ^ 40 * 6911959 * 2
def baseEnd_6911959 : Nat := 3549157231170227662324985

theorem tailTrace_6911959 : CollatzResearch.WordTrace tailWord_6911959 prefixEnd_6911959 3549157231170227662324985 := by
  unfold tailWord_6911959
  simp only [CollatzResearch.WordTrace]
  refine ⟨252099855566160486460402931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168066570377440324306935287 252099855566160486460402931)
  ·
    refine ⟨378149783349240729690604397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252099855566160486460402931 378149783349240729690604397)
    ·
      refine ⟨141806168755965273633976649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378149783349240729690604397 141806168755965273633976649)
      ·
        refine ⟨106354626566973955225482487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141806168755965273633976649 106354626566973955225482487)
        ·
          refine ⟨159531939850460932838223731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106354626566973955225482487 159531939850460932838223731)
          ·
            refine ⟨239297909775691399257335597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159531939850460932838223731 239297909775691399257335597)
            ·
              refine ⟨89736716165884274721500849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239297909775691399257335597 89736716165884274721500849)
              ·
                refine ⟨67302537124413206041125637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89736716165884274721500849 67302537124413206041125637)
                ·
                  refine ⟨12619225710827476132711057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67302537124413206041125637 12619225710827476132711057)
                  ·
                    refine ⟨9464419283120607099533293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12619225710827476132711057 9464419283120607099533293)
                    ·
                      refine ⟨3549157231170227662324985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464419283120607099533293 3549157231170227662324985)
                      ·
                        rfl

theorem cell23_6911959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_6911959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6911959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6911959 prefixEnd_6911959 := by exact prefixLift 6911959
  have htrace : WordTrace (prefixWord ++ tailWord_6911959) baseStart_6911959 baseEnd_6911959 := by
    simpa [prefixWord, tailWord_6911959, baseEnd_6911959] using wordTrace_append hprefix tailTrace_6911959
  have hstable : (prefixWord ++ tailWord_6911959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6911959).length < 2 ^ (prefixWord ++ tailWord_6911959).sum := by decide
  have hdescent : baseEnd_6911959 < baseStart_6911959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6911959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912033 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_6912033 : Nat := 118140960795 + 6912033 * 2 ^ 59
def prefixEnd_6912033 : Nat := 4983230072969 + 3 ^ 40 * 6912033 * 2
def baseEnd_6912033 : Nat := 3549195228738660372799645

theorem tailTrace_6912033 : CollatzResearch.WordTrace tailWord_6912033 prefixEnd_6912033 3549195228738660372799645 := by
  unfold tailWord_6912033
  simp only [CollatzResearch.WordTrace]
  refine ⟨252102554567892397098596753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168068369711928264732397835 252102554567892397098596753)
  ·
    refine ⟨189076915925919297823947565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252102554567892397098596753 189076915925919297823947565)
    ·
      refine ⟨70903843472219736683980337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189076915925919297823947565 70903843472219736683980337)
      ·
        refine ⟨53177882604164802512985253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70903843472219736683980337 53177882604164802512985253)
        ·
          refine ⟨9970852988280900471184735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53177882604164802512985253 9970852988280900471184735)
          ·
            refine ⟨14956279482421350706777103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970852988280900471184735 14956279482421350706777103)
            ·
              refine ⟨22434419223632026060165655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14956279482421350706777103 22434419223632026060165655)
              ·
                refine ⟨33651628835448039090248483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22434419223632026060165655 33651628835448039090248483)
                ·
                  refine ⟨50477443253172058635372725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33651628835448039090248483 50477443253172058635372725)
                  ·
                    refine ⟨4732260304984880497066193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50477443253172058635372725 4732260304984880497066193)
                    ·
                      refine ⟨3549195228738660372799645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732260304984880497066193 3549195228738660372799645)
                      ·
                        rfl

theorem cell23_6912033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_6912033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912033 prefixEnd_6912033 := by exact prefixLift 6912033
  have htrace : WordTrace (prefixWord ++ tailWord_6912033) baseStart_6912033 baseEnd_6912033 := by
    simpa [prefixWord, tailWord_6912033, baseEnd_6912033] using wordTrace_append hprefix tailTrace_6912033
  have hstable : (prefixWord ++ tailWord_6912033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912033).length < 2 ^ (prefixWord ++ tailWord_6912033).sum := by decide
  have hdescent : baseEnd_6912033 < baseStart_6912033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912063 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 3, 2, 2]
def baseStart_6912063 : Nat := 118140960795 + 6912063 * 2 ^ 59
def prefixEnd_6912063 : Nat := 4983230072969 + 3 ^ 40 * 6912063 * 2
def baseEnd_6912063 : Nat := 3549210633158295255424507

theorem tailTrace_6912063 : CollatzResearch.WordTrace tailWord_6912063 prefixEnd_6912063 3549210633158295255424507 := by
  unfold tailWord_6912063
  simp only [CollatzResearch.WordTrace]
  refine ⟨252103648757783712222188843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168069099171855808148125895 252103648757783712222188843)
  ·
    refine ⟨378155473136675568333283265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252103648757783712222188843 378155473136675568333283265)
    ·
      refine ⟨283616604852506676249962449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378155473136675568333283265 283616604852506676249962449)
      ·
        refine ⟨212712453639380007187471837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283616604852506676249962449 212712453639380007187471837)
        ·
          refine ⟨79767170114767502695301939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212712453639380007187471837 79767170114767502695301939)
          ·
            refine ⟨119650755172151254042952909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79767170114767502695301939 119650755172151254042952909)
            ·
              refine ⟨44869033189556720266107341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119650755172151254042952909 44869033189556720266107341)
              ·
                refine ⟨16825887446083770099790253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44869033189556720266107341 16825887446083770099790253)
                ·
                  refine ⟨6309707792281413787421345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16825887446083770099790253 6309707792281413787421345)
                  ·
                    refine ⟨4732280844211060340566009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6309707792281413787421345 4732280844211060340566009)
                    ·
                      refine ⟨3549210633158295255424507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732280844211060340566009 3549210633158295255424507)
                      ·
                        rfl

theorem cell23_6912063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_6912063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912063 prefixEnd_6912063 := by exact prefixLift 6912063
  have htrace : WordTrace (prefixWord ++ tailWord_6912063) baseStart_6912063 baseEnd_6912063 := by
    simpa [prefixWord, tailWord_6912063, baseEnd_6912063] using wordTrace_append hprefix tailTrace_6912063
  have hstable : (prefixWord ++ tailWord_6912063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912063).length < 2 ^ (prefixWord ++ tailWord_6912063).sum := by decide
  have hdescent : baseEnd_6912063 < baseStart_6912063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912073 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 2, 4]
def baseStart_6912073 : Nat := 118140960795 + 6912073 * 2 ^ 59
def prefixEnd_6912073 : Nat := 4983230072969 + 3 ^ 40 * 6912073 * 2
def baseEnd_6912073 : Nat := 1183071922654946738766487

theorem tailTrace_6912073 : CollatzResearch.WordTrace tailWord_6912073 prefixEnd_6912073 1183071922654946738766487 := by
  unfold tailWord_6912073
  simp only [CollatzResearch.WordTrace]
  refine ⟨252104013487747483930052873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168069342325164989286701915 252104013487747483930052873)
  ·
    refine ⟨189078010115810612947539655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252104013487747483930052873 189078010115810612947539655)
    ·
      refine ⟨283617015173715919421309483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189078010115810612947539655 283617015173715919421309483)
      ·
        refine ⟨425425522760573879131964225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283617015173715919421309483 425425522760573879131964225)
        ·
          refine ⟨319069142070430409348973169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425425522760573879131964225 319069142070430409348973169)
          ·
            refine ⟨239301856552822807011729877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319069142070430409348973169 239301856552822807011729877)
            ·
              refine ⟨5608637262956784539337419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239301856552822807011729877 5608637262956784539337419)
              ·
                refine ⟨8412955894435176809006129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608637262956784539337419 8412955894435176809006129)
                ·
                  refine ⟨6309716920826382606754597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412955894435176809006129 6309716920826382606754597)
                  ·
                    refine ⟨1183071922654946738766487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6309716920826382606754597 1183071922654946738766487)
                    ·
                      rfl

theorem cell23_6912073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 4].length) (baseStart_6912073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912073 prefixEnd_6912073 := by exact prefixLift 6912073
  have htrace : WordTrace (prefixWord ++ tailWord_6912073) baseStart_6912073 baseEnd_6912073 := by
    simpa [prefixWord, tailWord_6912073, baseEnd_6912073] using wordTrace_append hprefix tailTrace_6912073
  have hstable : (prefixWord ++ tailWord_6912073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912073).length < 2 ^ (prefixWord ++ tailWord_6912073).sum := by decide
  have hdescent : baseEnd_6912073 < baseStart_6912073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912076 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_6912076 : Nat := 118140960795 + 6912076 * 2 ^ 59
def prefixEnd_6912076 : Nat := 4983230072969 + 3 ^ 40 * 6912076 * 2
def baseEnd_6912076 : Nat := 3549217308406803704561947

theorem tailTrace_6912076 : CollatzResearch.WordTrace tailWord_6912076 prefixEnd_6912076 3549217308406803704561947 := by
  unfold tailWord_6912076
  simp only [CollatzResearch.WordTrace]
  refine ⟨126052061453368307721206041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168069415271157743628274721 126052061453368307721206041)
  ·
    refine ⟨94539046090026230790904531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126052061453368307721206041 94539046090026230790904531)
    ·
      refine ⟨141808569135039346186356797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94539046090026230790904531 141808569135039346186356797)
      ·
        refine ⟨53178213425639754819883799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141808569135039346186356797 53178213425639754819883799)
        ·
          refine ⟨79767320138459632229825699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53178213425639754819883799 79767320138459632229825699)
          ·
            refine ⟨119650980207689448344738549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79767320138459632229825699 119650980207689448344738549)
            ·
              refine ⟨11217279394470885782319239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119650980207689448344738549 11217279394470885782319239)
              ·
                refine ⟨16825919091706328673478859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11217279394470885782319239 16825919091706328673478859)
                ·
                  refine ⟨25238878637559493010218289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16825919091706328673478859 25238878637559493010218289)
                  ·
                    refine ⟨18929158978169619757663717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25238878637559493010218289 18929158978169619757663717)
                    ·
                      refine ⟨3549217308406803704561947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18929158978169619757663717 3549217308406803704561947)
                      ·
                        rfl

theorem cell23_6912076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_6912076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912076 prefixEnd_6912076 := by exact prefixLift 6912076
  have htrace : WordTrace (prefixWord ++ tailWord_6912076) baseStart_6912076 baseEnd_6912076 := by
    simpa [prefixWord, tailWord_6912076, baseEnd_6912076] using wordTrace_append hprefix tailTrace_6912076
  have hstable : (prefixWord ++ tailWord_6912076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912076).length < 2 ^ (prefixWord ++ tailWord_6912076).sum := by decide
  have hdescent : baseEnd_6912076 < baseStart_6912076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912113 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_6912113 : Nat := 118140960795 + 6912113 * 2 ^ 59
def prefixEnd_6912113 : Nat := 4983230072969 + 3 ^ 40 * 6912113 * 2
def baseEnd_6912113 : Nat := 3549236307191020059799277

theorem tailTrace_6912113 : CollatzResearch.WordTrace tailWord_6912113 prefixEnd_6912113 3549236307191020059799277 := by
  unfold tailWord_6912113
  simp only [CollatzResearch.WordTrace]
  refine ⟨252105472407602570761508993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168070314938401713841005995 252105472407602570761508993)
  ·
    refine ⟨189079104305701928071131745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252105472407602570761508993 189079104305701928071131745)
    ·
      refine ⟨141809328229276446053348809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189079104305701928071131745 141809328229276446053348809)
      ·
        refine ⟨106356996171957334540011607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141809328229276446053348809 106356996171957334540011607)
        ·
          refine ⟨159535494257936001810017411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106356996171957334540011607 159535494257936001810017411)
          ·
            refine ⟨239303241386904002715026117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159535494257936001810017411 239303241386904002715026117)
            ·
              refine ⟨44869357760044500509067397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239303241386904002715026117 44869357760044500509067397)
              ·
                refine ⟨8413004580008343845450137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44869357760044500509067397 8413004580008343845450137)
                ·
                  refine ⟨6309753435006257884087603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8413004580008343845450137 6309753435006257884087603)
                  ·
                    refine ⟨9464630152509386826131405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6309753435006257884087603 9464630152509386826131405)
                    ·
                      refine ⟨3549236307191020059799277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464630152509386826131405 3549236307191020059799277)
                      ·
                        rfl

theorem cell23_6912113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_6912113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912113 prefixEnd_6912113 := by exact prefixLift 6912113
  have htrace : WordTrace (prefixWord ++ tailWord_6912113) baseStart_6912113 baseEnd_6912113 := by
    simpa [prefixWord, tailWord_6912113, baseEnd_6912113] using wordTrace_append hprefix tailTrace_6912113
  have hstable : (prefixWord ++ tailWord_6912113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912113).length < 2 ^ (prefixWord ++ tailWord_6912113).sum := by decide
  have hdescent : baseEnd_6912113 < baseStart_6912113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912114 : List Nat := [3, 2, 1, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_6912114 : Nat := 118140960795 + 6912114 * 2 ^ 59
def prefixEnd_6912114 : Nat := 4983230072969 + 3 ^ 40 * 6912114 * 2
def baseEnd_6912114 : Nat := 3549236820671674555886773

theorem tailTrace_6912114 : CollatzResearch.WordTrace tailWord_6912114 prefixEnd_6912114 3549236820671674555886773 := by
  unfold tailWord_6912114
  simp only [CollatzResearch.WordTrace]
  refine ⟨63026377220149736983073849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168070339253732631954863597 63026377220149736983073849)
  ·
    refine ⟨47269782915112302737305387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63026377220149736983073849 47269782915112302737305387)
    ·
      refine ⟨70904674372668454105958081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47269782915112302737305387 70904674372668454105958081)
      ·
        refine ⟨53178505779501340579468561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70904674372668454105958081 53178505779501340579468561)
        ·
          refine ⟨39883879334626005434601421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53178505779501340579468561 39883879334626005434601421)
          ·
            refine ⟨14956454750484752037975533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39883879334626005434601421 14956454750484752037975533)
            ·
              refine ⟨5608670531431782014240825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14956454750484752037975533 5608670531431782014240825)
              ·
                refine ⟨4206502898573836510680619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608670531431782014240825 4206502898573836510680619)
                ·
                  refine ⟨6309754347860754766020929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206502898573836510680619 6309754347860754766020929)
                  ·
                    refine ⟨4732315760895566074515697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6309754347860754766020929 4732315760895566074515697)
                    ·
                      refine ⟨3549236820671674555886773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732315760895566074515697 3549236820671674555886773)
                      ·
                        rfl

theorem cell23_6912114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_6912114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912114 prefixEnd_6912114 := by exact prefixLift 6912114
  have htrace : WordTrace (prefixWord ++ tailWord_6912114) baseStart_6912114 baseEnd_6912114 := by
    simpa [prefixWord, tailWord_6912114, baseEnd_6912114] using wordTrace_append hprefix tailTrace_6912114
  have hstable : (prefixWord ++ tailWord_6912114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912114).length < 2 ^ (prefixWord ++ tailWord_6912114).sum := by decide
  have hdescent : baseEnd_6912114 < baseStart_6912114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912153 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 6, 2, 2]
def baseStart_6912153 : Nat := 118140960795 + 6912153 * 2 ^ 59
def prefixEnd_6912153 : Nat := 4983230072969 + 3 ^ 40 * 6912153 * 2
def baseEnd_6912153 : Nat := 3549256846417199903299093

theorem tailTrace_6912153 : CollatzResearch.WordTrace tailWord_6912153 prefixEnd_6912153 3549256846417199903299093 := by
  unfold tailWord_6912153
  simp only [CollatzResearch.WordTrace]
  refine ⟨252106931327457657592965113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168071287551638438395310075 252106931327457657592965113)
  ·
    refine ⟨189080198495593243194723835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252106931327457657592965113 189080198495593243194723835)
    ·
      refine ⟨283620297743389864792085753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189080198495593243194723835 283620297743389864792085753)
      ·
        refine ⟨212715223307542398594064315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283620297743389864792085753 212715223307542398594064315)
        ·
          refine ⟨319072834961313597891096473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212715223307542398594064315 319072834961313597891096473)
          ·
            refine ⟨239304626220985198418322355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319072834961313597891096473 239304626220985198418322355)
            ·
              refine ⟨358956939331477797627483533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239304626220985198418322355 358956939331477797627483533)
              ·
                refine ⟨134608852249304174110306325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358956939331477797627483533 134608852249304174110306325)
                ·
                  refine ⟨6309789949186133161420609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134608852249304174110306325 6309789949186133161420609)
                  ·
                    refine ⟨4732342461889599871065457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6309789949186133161420609 4732342461889599871065457)
                    ·
                      refine ⟨3549256846417199903299093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732342461889599871065457 3549256846417199903299093)
                      ·
                        rfl

theorem cell23_6912153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_6912153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912153 prefixEnd_6912153 := by exact prefixLift 6912153
  have htrace : WordTrace (prefixWord ++ tailWord_6912153) baseStart_6912153 baseEnd_6912153 := by
    simpa [prefixWord, tailWord_6912153, baseEnd_6912153] using wordTrace_append hprefix tailTrace_6912153
  have hstable : (prefixWord ++ tailWord_6912153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912153).length < 2 ^ (prefixWord ++ tailWord_6912153).sum := by decide
  have hdescent : baseEnd_6912153 < baseStart_6912153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912156 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6912156 : Nat := 118140960795 + 6912156 * 2 ^ 59
def prefixEnd_6912156 : Nat := 4983230072969 + 3 ^ 40 * 6912156 * 2
def baseEnd_6912156 : Nat := 3549258386859163391561579

theorem tailTrace_6912156 : CollatzResearch.WordTrace tailWord_6912156 prefixEnd_6912156 3549258386859163391561579 := by
  unfold tailWord_6912156
  simp only [CollatzResearch.WordTrace]
  refine ⟨126053520373223394552662161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168071360497631192736882881 126053520373223394552662161)
  ·
    refine ⟨94540140279917545914496621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126053520373223394552662161 94540140279917545914496621)
    ·
      refine ⟨35452552604969079717936233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94540140279917545914496621 35452552604969079717936233)
      ·
        refine ⟨26589414453726809788452175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35452552604969079717936233 26589414453726809788452175)
        ·
          refine ⟨39884121680590214682678263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26589414453726809788452175 39884121680590214682678263)
          ·
            refine ⟨59826182520885322024017395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39884121680590214682678263 59826182520885322024017395)
            ·
              refine ⟨89739273781327983036026093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59826182520885322024017395 89739273781327983036026093)
              ·
                refine ⟨33652227667997993638509785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89739273781327983036026093 33652227667997993638509785)
                ·
                  refine ⟨25239170750998495228882339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33652227667997993638509785 25239170750998495228882339)
                  ·
                    refine ⟨37858756126497742843323509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25239170750998495228882339 37858756126497742843323509)
                    ·
                      refine ⟨3549258386859163391561579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37858756126497742843323509 3549258386859163391561579)
                      ·
                        rfl

theorem cell23_6912156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6912156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912156 prefixEnd_6912156 := by exact prefixLift 6912156
  have htrace : WordTrace (prefixWord ++ tailWord_6912156) baseStart_6912156 baseEnd_6912156 := by
    simpa [prefixWord, tailWord_6912156, baseEnd_6912156] using wordTrace_append hprefix tailTrace_6912156
  have hstable : (prefixWord ++ tailWord_6912156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912156).length < 2 ^ (prefixWord ++ tailWord_6912156).sum := by decide
  have hdescent : baseEnd_6912156 < baseStart_6912156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912157 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_6912157 : Nat := 118140960795 + 6912157 * 2 ^ 59
def prefixEnd_6912157 : Nat := 4983230072969 + 3 ^ 40 * 6912157 * 2
def baseEnd_6912157 : Nat := 3549258900339817887649075

theorem tailTrace_6912157 : CollatzResearch.WordTrace tailWord_6912157 prefixEnd_6912157 3549258900339817887649075 := by
  unfold tailWord_6912157
  simp only [CollatzResearch.WordTrace]
  refine ⟨252107077219443166276110725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168071384812962110850740483 252107077219443166276110725)
  ·
    refine ⟨47270076978645593676770761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252107077219443166276110725 47270076978645593676770761)
    ·
      refine ⟨35452557733984195257578071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47270076978645593676770761 35452557733984195257578071)
      ·
        refine ⟨53178836600976292886367107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35452557733984195257578071 53178836600976292886367107)
        ·
          refine ⟨79768254901464439329550661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53178836600976292886367107 79768254901464439329550661)
          ·
            refine ⟨14956547794024582374290749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79768254901464439329550661 14956547794024582374290749)
            ·
              refine ⟨5608705422759218390359031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14956547794024582374290749 5608705422759218390359031)
              ·
                refine ⟨8413058134138827585538547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608705422759218390359031 8413058134138827585538547)
                ·
                  refine ⟨12619587201208241378307821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8413058134138827585538547 12619587201208241378307821)
                  ·
                    refine ⟨4732345200453090516865433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12619587201208241378307821 4732345200453090516865433)
                    ·
                      refine ⟨3549258900339817887649075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732345200453090516865433 3549258900339817887649075)
                      ·
                        rfl

theorem cell23_6912157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_6912157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912157 prefixEnd_6912157 := by exact prefixLift 6912157
  have htrace : WordTrace (prefixWord ++ tailWord_6912157) baseStart_6912157 baseEnd_6912157 := by
    simpa [prefixWord, tailWord_6912157, baseEnd_6912157] using wordTrace_append hprefix tailTrace_6912157
  have hstable : (prefixWord ++ tailWord_6912157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912157).length < 2 ^ (prefixWord ++ tailWord_6912157).sum := by decide
  have hdescent : baseEnd_6912157 < baseStart_6912157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912173 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_6912173 : Nat := 118140960795 + 6912173 * 2 ^ 59
def prefixEnd_6912173 : Nat := 4983230072969 + 3 ^ 40 * 6912173 * 2
def baseEnd_6912173 : Nat := 3549267116030289825049001

theorem tailTrace_6912173 : CollatzResearch.WordTrace tailWord_6912173 prefixEnd_6912173 3549267116030289825049001 := by
  unfold tailWord_6912173
  simp only [CollatzResearch.WordTrace]
  refine ⟨252107660787385201008693173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168071773858256800672462115 252107660787385201008693173)
  ·
    refine ⟨23635093198817362594564985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252107660787385201008693173 23635093198817362594564985)
    ·
      refine ⟨17726319899113021945923739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23635093198817362594564985 17726319899113021945923739)
      ·
        refine ⟨26589479848669532918885609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17726319899113021945923739 26589479848669532918885609)
        ·
          refine ⟨19942109886502149689164207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26589479848669532918885609 19942109886502149689164207)
          ·
            refine ⟨29913164829753224533746311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19942109886502149689164207 29913164829753224533746311)
            ·
              refine ⟨44869747244629836800619467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29913164829753224533746311 44869747244629836800619467)
              ·
                refine ⟨67304620866944755200929201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44869747244629836800619467 67304620866944755200929201)
                ·
                  refine ⟨50478465650208566400696901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67304620866944755200929201 50478465650208566400696901)
                  ·
                    refine ⟨9464712309414106200130669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50478465650208566400696901 9464712309414106200130669)
                    ·
                      refine ⟨3549267116030289825049001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464712309414106200130669 3549267116030289825049001)
                      ·
                        rfl

theorem cell23_6912173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_6912173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912173 prefixEnd_6912173 := by exact prefixLift 6912173
  have htrace : WordTrace (prefixWord ++ tailWord_6912173) baseStart_6912173 baseEnd_6912173 := by
    simpa [prefixWord, tailWord_6912173, baseEnd_6912173] using wordTrace_append hprefix tailTrace_6912173
  have hstable : (prefixWord ++ tailWord_6912173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912173).length < 2 ^ (prefixWord ++ tailWord_6912173).sum := by decide
  have hdescent : baseEnd_6912173 < baseStart_6912173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912179 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8]
def baseStart_6912179 : Nat := 118140960795 + 6912179 * 2 ^ 59
def prefixEnd_6912179 : Nat := 4983230072969 + 3 ^ 40 * 6912179 * 2
def baseEnd_6912179 : Nat := 3549270196914216801573973

theorem tailTrace_6912179 : CollatzResearch.WordTrace tailWord_6912179 prefixEnd_6912179 3549270196914216801573973 := by
  unfold tailWord_6912179
  simp only [CollatzResearch.WordTrace]
  refine ⟨252107879625363464033411591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168071919750242309355607727 252107879625363464033411591)
  ·
    refine ⟨378161819438045196050117387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252107879625363464033411591 378161819438045196050117387)
    ·
      refine ⟨567242729157067794075176081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378161819438045196050117387 567242729157067794075176081)
      ·
        refine ⟨425432046867800845556382061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567242729157067794075176081 425432046867800845556382061)
        ·
          refine ⟨159537017575425317083643273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425432046867800845556382061 159537017575425317083643273)
          ·
            refine ⟨119652763181568987812732455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159537017575425317083643273 119652763181568987812732455)
            ·
              refine ⟨179479144772353481719098683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119652763181568987812732455 179479144772353481719098683)
              ·
                refine ⟨269218717158530222578648025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179479144772353481719098683 269218717158530222578648025)
                ·
                  refine ⟨201914037868897666933986019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269218717158530222578648025 201914037868897666933986019)
                  ·
                    refine ⟨302871056803346500400979029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 201914037868897666933986019 302871056803346500400979029)
                    ·
                      refine ⟨3549270196914216801573973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 302871056803346500400979029 3549270196914216801573973)
                      ·
                        rfl

theorem cell23_6912179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_6912179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912179 prefixEnd_6912179 := by exact prefixLift 6912179
  have htrace : WordTrace (prefixWord ++ tailWord_6912179) baseStart_6912179 baseEnd_6912179 := by
    simpa [prefixWord, tailWord_6912179, baseEnd_6912179] using wordTrace_append hprefix tailTrace_6912179
  have hstable : (prefixWord ++ tailWord_6912179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912179).length < 2 ^ (prefixWord ++ tailWord_6912179).sum := by decide
  have hdescent : baseEnd_6912179 < baseStart_6912179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912186 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_6912186 : Nat := 118140960795 + 6912186 * 2 ^ 59
def prefixEnd_6912186 : Nat := 4983230072969 + 3 ^ 40 * 6912186 * 2
def baseEnd_6912186 : Nat := 3549273791278798274186441

theorem tailTrace_6912186 : CollatzResearch.WordTrace tailWord_6912186 prefixEnd_6912186 3549273791278798274186441 := by
  unfold tailWord_6912186
  simp only [CollatzResearch.WordTrace]
  refine ⟨63027033734084526057229103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168072089957558736152610941 63027033734084526057229103)
  ·
    refine ⟨94540550601126789085843655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63027033734084526057229103 94540550601126789085843655)
    ·
      refine ⟨141810825901690183628765483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94540550601126789085843655 141810825901690183628765483)
      ·
        refine ⟨212716238852535275443148225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141810825901690183628765483 212716238852535275443148225)
        ·
          refine ⟨159537179139401456582361169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212716238852535275443148225 159537179139401456582361169)
          ·
            refine ⟨119652884354551092436770877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159537179139401456582361169 119652884354551092436770877)
            ·
              refine ⟨44869831632956659663789079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119652884354551092436770877 44869831632956659663789079)
              ·
                refine ⟨67304747449434989495683619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44869831632956659663789079 67304747449434989495683619)
                ·
                  refine ⟨100957121174152484243525429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67304747449434989495683619 100957121174152484243525429)
                  ·
                    refine ⟨9464730110076795397830509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100957121174152484243525429 9464730110076795397830509)
                    ·
                      refine ⟨3549273791278798274186441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464730110076795397830509 3549273791278798274186441)
                      ·
                        rfl

theorem cell23_6912186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_6912186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912186 prefixEnd_6912186 := by exact prefixLift 6912186
  have htrace : WordTrace (prefixWord ++ tailWord_6912186) baseStart_6912186 baseEnd_6912186 := by
    simpa [prefixWord, tailWord_6912186, baseEnd_6912186] using wordTrace_append hprefix tailTrace_6912186
  have hstable : (prefixWord ++ tailWord_6912186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912186).length < 2 ^ (prefixWord ++ tailWord_6912186).sum := by decide
  have hdescent : baseEnd_6912186 < baseStart_6912186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912210 : List Nat := [3, 2, 2, 2, 1, 3, 2, 3, 5]
def baseStart_6912210 : Nat := 118140960795 + 6912210 * 2 ^ 59
def prefixEnd_6912210 : Nat := 4983230072969 + 3 ^ 40 * 6912210 * 2
def baseEnd_6912210 : Nat := 394365123868278464476259

theorem tailTrace_6912210 : CollatzResearch.WordTrace tailWord_6912210 prefixEnd_6912210 394365123868278464476259 := by
  unfold tailWord_6912210
  simp only [CollatzResearch.WordTrace]
  refine ⟨63027252572062789081947521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168072673525500770885193389 63027252572062789081947521)
  ·
    refine ⟨47270439429047091811460641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63027252572062789081947521 47270439429047091811460641)
    ·
      refine ⟨35452829571785318858595481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47270439429047091811460641 35452829571785318858595481)
      ·
        refine ⟨26589622178838989143946611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35452829571785318858595481 26589622178838989143946611)
        ·
          refine ⟨39884433268258483715919917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26589622178838989143946611 39884433268258483715919917)
          ·
            refine ⟨14956662475596931393469969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39884433268258483715919917 14956662475596931393469969)
            ·
              refine ⟨11217496856697698545102477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14956662475596931393469969 11217496856697698545102477)
              ·
                refine ⟨4206561321261636954413429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11217496856697698545102477 4206561321261636954413429)
                ·
                  refine ⟨394365123868278464476259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4206561321261636954413429 394365123868278464476259)
                  ·
                    rfl

theorem cell23_6912210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_6912210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912210 prefixEnd_6912210 := by exact prefixLift 6912210
  have htrace : WordTrace (prefixWord ++ tailWord_6912210) baseStart_6912210 baseEnd_6912210 := by
    simpa [prefixWord, tailWord_6912210, baseEnd_6912210] using wordTrace_append hprefix tailTrace_6912210
  have hstable : (prefixWord ++ tailWord_6912210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912210).length < 2 ^ (prefixWord ++ tailWord_6912210).sum := by decide
  have hdescent : baseEnd_6912210 < baseStart_6912210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912243 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 2, 4, 2]
def baseStart_6912243 : Nat := 118140960795 + 6912243 * 2 ^ 59
def prefixEnd_6912243 : Nat := 4983230072969 + 3 ^ 40 * 6912243 * 2
def baseEnd_6912243 : Nat := 3549303059676104551173679

theorem tailTrace_6912243 : CollatzResearch.WordTrace tailWord_6912243 prefixEnd_6912243 3549303059676104551173679 := by
  unfold tailWord_6912243
  simp only [CollatzResearch.WordTrace]
  refine ⟨252110213897131602963741383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168073475931421068642494255 252110213897131602963741383)
  ·
    refine ⟨378165320845697404445612075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252110213897131602963741383 378165320845697404445612075)
    ·
      refine ⟨567247981268546106668418113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378165320845697404445612075 567247981268546106668418113)
      ·
        refine ⟨425435985951409580001313585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567247981268546106668418113 425435985951409580001313585)
        ·
          refine ⟨319076989463557185000985189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425435985951409580001313585 319076989463557185000985189)
          ·
            refine ⟨59826935524416972187684723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319076989463557185000985189 59826935524416972187684723)
            ·
              refine ⟨89740403286625458281527085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59826935524416972187684723 89740403286625458281527085)
              ·
                refine ⟨33652651232484546855572657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89740403286625458281527085 33652651232484546855572657)
                ·
                  refine ⟨25239488424363410141679493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33652651232484546855572657 25239488424363410141679493)
                  ·
                    refine ⟨4732404079568139401564905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25239488424363410141679493 4732404079568139401564905)
                    ·
                      refine ⟨3549303059676104551173679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732404079568139401564905 3549303059676104551173679)
                      ·
                        rfl

theorem cell23_6912243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4, 2].length) (baseStart_6912243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912243 prefixEnd_6912243 := by exact prefixLift 6912243
  have htrace : WordTrace (prefixWord ++ tailWord_6912243) baseStart_6912243 baseEnd_6912243 := by
    simpa [prefixWord, tailWord_6912243, baseEnd_6912243] using wordTrace_append hprefix tailTrace_6912243
  have hstable : (prefixWord ++ tailWord_6912243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912243).length < 2 ^ (prefixWord ++ tailWord_6912243).sum := by decide
  have hdescent : baseEnd_6912243 < baseStart_6912243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912266 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 8]
def baseStart_6912266 : Nat := 118140960795 + 6912266 * 2 ^ 59
def prefixEnd_6912266 : Nat := 4983230072969 + 3 ^ 40 * 6912266 * 2
def baseEnd_6912266 : Nat := 394368318859017551242897

theorem tailTrace_6912266 : CollatzResearch.WordTrace tailWord_6912266 prefixEnd_6912266 394368318859017551242897 := by
  unfold tailWord_6912266
  simp only [CollatzResearch.WordTrace]
  refine ⟨63027763194012069472957163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168074035184032185261219101 63027763194012069472957163)
  ·
    refine ⟨94541644791018104209435745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63027763194012069472957163 94541644791018104209435745)
    ·
      refine ⟨70906233593263578157076809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94541644791018104209435745 70906233593263578157076809)
      ·
        refine ⟨53179675194947683617807607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70906233593263578157076809 53179675194947683617807607)
        ·
          refine ⟨79769512792421525426711411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53179675194947683617807607 79769512792421525426711411)
          ·
            refine ⟨119654269188632288140067117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79769512792421525426711411 119654269188632288140067117)
            ·
              refine ⟨44870350945737108052525169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119654269188632288140067117 44870350945737108052525169)
              ·
                refine ⟨33652763209302831039393877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44870350945737108052525169 33652763209302831039393877)
                ·
                  refine ⟨394368318859017551242897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33652763209302831039393877 394368318859017551242897)
                  ·
                    rfl

theorem cell23_6912266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_6912266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912266 prefixEnd_6912266 := by exact prefixLift 6912266
  have htrace : WordTrace (prefixWord ++ tailWord_6912266) baseStart_6912266 baseEnd_6912266 := by
    simpa [prefixWord, tailWord_6912266, baseEnd_6912266] using wordTrace_append hprefix tailTrace_6912266
  have hstable : (prefixWord ++ tailWord_6912266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912266).length < 2 ^ (prefixWord ++ tailWord_6912266).sum := by decide
  have hdescent : baseEnd_6912266 < baseStart_6912266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912303 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 3, 5, 2]
def baseStart_6912303 : Nat := 118140960795 + 6912303 * 2 ^ 59
def prefixEnd_6912303 : Nat := 4983230072969 + 3 ^ 40 * 6912303 * 2
def baseEnd_6912303 : Nat := 3549333868515374316423403

theorem tailTrace_6912303 : CollatzResearch.WordTrace tailWord_6912303 prefixEnd_6912303 3549333868515374316423403 := by
  unfold tailWord_6912303
  simp only [CollatzResearch.WordTrace]
  refine ⟨252112402276914233210925563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168074934851276155473950375 252112402276914233210925563)
  ·
    refine ⟨378168603415371349816388345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252112402276914233210925563 378168603415371349816388345)
    ·
      refine ⟨283626452561528512362291259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378168603415371349816388345 283626452561528512362291259)
      ·
        refine ⟨425439678842292768543436889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283626452561528512362291259 425439678842292768543436889)
        ·
          refine ⟨319079759131719576407577667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425439678842292768543436889 319079759131719576407577667)
          ·
            refine ⟨478619638697579364611366501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319079759131719576407577667 478619638697579364611366501)
            ·
              refine ⟨89741182255796130864631219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 478619638697579364611366501 89741182255796130864631219)
              ·
                refine ⟨134611773383694196296946829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89741182255796130864631219 134611773383694196296946829)
                ·
                  refine ⟨50479415018885323611355061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134611773383694196296946829 50479415018885323611355061)
                  ·
                    refine ⟨4732445158020499088564537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50479415018885323611355061 4732445158020499088564537)
                    ·
                      refine ⟨3549333868515374316423403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732445158020499088564537 3549333868515374316423403)
                      ·
                        rfl

theorem cell23_6912303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5, 2].length) (baseStart_6912303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912303 prefixEnd_6912303 := by exact prefixLift 6912303
  have htrace : WordTrace (prefixWord ++ tailWord_6912303) baseStart_6912303 baseEnd_6912303 := by
    simpa [prefixWord, tailWord_6912303, baseEnd_6912303] using wordTrace_append hprefix tailTrace_6912303
  have hstable : (prefixWord ++ tailWord_6912303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912303).length < 2 ^ (prefixWord ++ tailWord_6912303).sum := by decide
  have hdescent : baseEnd_6912303 < baseStart_6912303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912327 : List Nat := [1, 1, 4, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_6912327 : Nat := 118140960795 + 6912327 * 2 ^ 59
def prefixEnd_6912327 : Nat := 4983230072969 + 3 ^ 40 * 6912327 * 2
def baseEnd_6912327 : Nat := 3549346192051082222523293

theorem tailTrace_6912327 : CollatzResearch.WordTrace tailWord_6912327 prefixEnd_6912327 3549346192051082222523293 := by
  unfold tailWord_6912327
  simp only [CollatzResearch.WordTrace]
  refine ⟨252113277628827285309799235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168075518419218190206532823 252113277628827285309799235)
  ·
    refine ⟨378169916443240927964698853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252113277628827285309799235 378169916443240927964698853)
    ·
      refine ⟨70906859333107673993381035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378169916443240927964698853 70906859333107673993381035)
      ·
        refine ⟨106360288999661510990071553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70906859333107673993381035 106360288999661510990071553)
        ·
          refine ⟨79770216749746133242553665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106360288999661510990071553 79770216749746133242553665)
          ·
            refine ⟨59827662562309599931915249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79770216749746133242553665 59827662562309599931915249)
            ·
              refine ⟨44870746921732199948936437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59827662562309599931915249 44870746921732199948936437)
              ·
                refine ⟨4206632523912393745212791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44870746921732199948936437 4206632523912393745212791)
                ·
                  refine ⟨6309948785868590617819187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206632523912393745212791 6309948785868590617819187)
                  ·
                    refine ⟨9464923178802885926728781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6309948785868590617819187 9464923178802885926728781)
                    ·
                      refine ⟨3549346192051082222523293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464923178802885926728781 3549346192051082222523293)
                      ·
                        rfl

theorem cell23_6912327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_6912327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912327 prefixEnd_6912327 := by exact prefixLift 6912327
  have htrace : WordTrace (prefixWord ++ tailWord_6912327) baseStart_6912327 baseEnd_6912327 := by
    simpa [prefixWord, tailWord_6912327, baseEnd_6912327] using wordTrace_append hprefix tailTrace_6912327
  have hstable : (prefixWord ++ tailWord_6912327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912327).length < 2 ^ (prefixWord ++ tailWord_6912327).sum := by decide
  have hdescent : baseEnd_6912327 < baseStart_6912327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912360 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 1, 6]
def baseStart_6912360 : Nat := 118140960795 + 6912360 * 2 ^ 59
def prefixEnd_6912360 : Nat := 4983230072969 + 3 ^ 40 * 6912360 * 2
def baseEnd_6912360 : Nat := 1183121045637560197803547

theorem tailTrace_6912360 : CollatzResearch.WordTrace tailWord_6912360 prefixEnd_6912360 1183121045637560197803547 := by
  unfold tailWord_6912360
  simp only [CollatzResearch.WordTrace]
  refine ⟨126057240618853865972875267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168076320825138487963833689 126057240618853865972875267)
  ·
    refine ⟨189085860928280798959312901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126057240618853865972875267 189085860928280798959312901)
    ·
      refine ⟨35453598924052649804871169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189085860928280798959312901 35453598924052649804871169)
      ·
        refine ⟨26590199193039487353653377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35453598924052649804871169 26590199193039487353653377)
        ·
          refine ⟨19942649394779615515240033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26590199193039487353653377 19942649394779615515240033)
          ·
            refine ⟨14956987046084711636430025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19942649394779615515240033 14956987046084711636430025)
            ·
              refine ⟨11217740284563533727322519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14956987046084711636430025 11217740284563533727322519)
              ·
                refine ⟨16826610426845300590983779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11217740284563533727322519 16826610426845300590983779)
                ·
                  refine ⟨25239915640267950886475669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16826610426845300590983779 25239915640267950886475669)
                  ·
                    refine ⟨1183121045637560197803547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25239915640267950886475669 1183121045637560197803547)
                    ·
                      rfl

theorem cell23_6912360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_6912360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912360 prefixEnd_6912360 := by exact prefixLift 6912360
  have htrace : WordTrace (prefixWord ++ tailWord_6912360) baseStart_6912360 baseEnd_6912360 := by
    simpa [prefixWord, tailWord_6912360, baseEnd_6912360] using wordTrace_append hprefix tailTrace_6912360
  have hstable : (prefixWord ++ tailWord_6912360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912360).length < 2 ^ (prefixWord ++ tailWord_6912360).sum := by decide
  have hdescent : baseEnd_6912360 < baseStart_6912360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912370 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_6912370 : Nat := 118140960795 + 6912370 * 2 ^ 59
def prefixEnd_6912370 : Nat := 4983230072969 + 3 ^ 40 * 6912370 * 2
def baseEnd_6912370 : Nat := 3549368271719225554285595

theorem tailTrace_6912370 : CollatzResearch.WordTrace tailWord_6912370 prefixEnd_6912370 3549368271719225554285595 := by
  unfold tailWord_6912370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63028711491917875913403641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168076563978447669102409709 63028711491917875913403641)
  ·
    refine ⟨47271533618938406935052731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63028711491917875913403641 47271533618938406935052731)
    ·
      refine ⟨70907300428407610402579097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47271533618938406935052731 70907300428407610402579097)
      ·
        refine ⟨53180475321305707801934323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70907300428407610402579097 53180475321305707801934323)
        ·
          refine ⟨79770712981958561702901485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53180475321305707801934323 79770712981958561702901485)
          ·
            refine ⟨29914017368234460638588057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79770712981958561702901485 29914017368234460638588057)
            ·
              refine ⟨22435513026175845478941043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29914017368234460638588057 22435513026175845478941043)
              ·
                refine ⟨33653269539263768218411565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22435513026175845478941043 33653269539263768218411565)
                ·
                  refine ⟨12619976077223913081904337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33653269539263768218411565 12619976077223913081904337)
                  ·
                    refine ⟨9464982057917934811428253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12619976077223913081904337 9464982057917934811428253)
                    ·
                      refine ⟨3549368271719225554285595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9464982057917934811428253 3549368271719225554285595)
                      ·
                        rfl

theorem cell23_6912370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_6912370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912370 prefixEnd_6912370 := by exact prefixLift 6912370
  have htrace : WordTrace (prefixWord ++ tailWord_6912370) baseStart_6912370 baseEnd_6912370 := by
    simpa [prefixWord, tailWord_6912370, baseEnd_6912370] using wordTrace_append hprefix tailTrace_6912370
  have hstable : (prefixWord ++ tailWord_6912370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912370).length < 2 ^ (prefixWord ++ tailWord_6912370).sum := by decide
  have hdescent : baseEnd_6912370 < baseStart_6912370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912387 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 3]
def baseStart_6912387 : Nat := 118140960795 + 6912387 * 2 ^ 59
def prefixEnd_6912387 : Nat := 4983230072969 + 3 ^ 40 * 6912387 * 2
def baseEnd_6912387 : Nat := 3549377000890351987773017

theorem tailTrace_6912387 : CollatzResearch.WordTrace tailWord_6912387 prefixEnd_6912387 3549377000890351987773017 := by
  unfold tailWord_6912387
  simp only [CollatzResearch.WordTrace]
  refine ⟨252115466008609915556983415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168076977339073277037988943 252115466008609915556983415)
  ·
    refine ⟨378173199012914873335475123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252115466008609915556983415 378173199012914873335475123)
    ·
      refine ⟨567259798519372310003212685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378173199012914873335475123 567259798519372310003212685)
      ·
        refine ⟨212722424444764616251204757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567259798519372310003212685 212722424444764616251204757)
        ·
          refine ⟨9971363645848341386775223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 212722424444764616251204757 9971363645848341386775223)
          ·
            refine ⟨14957045468772512080162835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9971363645848341386775223 14957045468772512080162835)
            ·
              refine ⟨22435568203158768120244253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14957045468772512080162835 22435568203158768120244253)
              ·
                refine ⟨8413338076184538045091595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22435568203158768120244253 8413338076184538045091595)
                ·
                  refine ⟨12620007114276807067637393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8413338076184538045091595 12620007114276807067637393)
                  ·
                    refine ⟨9465005335707605300728045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12620007114276807067637393 9465005335707605300728045)
                    ·
                      refine ⟨3549377000890351987773017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9465005335707605300728045 3549377000890351987773017)
                      ·
                        rfl

theorem cell23_6912387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_6912387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912387 prefixEnd_6912387 := by exact prefixLift 6912387
  have htrace : WordTrace (prefixWord ++ tailWord_6912387) baseStart_6912387 baseEnd_6912387 := by
    simpa [prefixWord, tailWord_6912387, baseEnd_6912387] using wordTrace_append hprefix tailTrace_6912387
  have hstable : (prefixWord ++ tailWord_6912387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912387).length < 2 ^ (prefixWord ++ tailWord_6912387).sum := by decide
  have hdescent : baseEnd_6912387 < baseStart_6912387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912414 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6912414 : Nat := 118140960795 + 6912414 * 2 ^ 59
def prefixEnd_6912414 : Nat := 4983230072969 + 3 ^ 40 * 6912414 * 2
def baseEnd_6912414 : Nat := 3549390864868023382135393

theorem tailTrace_6912414 : CollatzResearch.WordTrace tailWord_6912414 prefixEnd_6912414 3549390864868023382135393 := by
  unfold tailWord_6912414
  simp only [CollatzResearch.WordTrace]
  refine ⟨31514556347439012396027037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168077633853008066112144197 31514556347439012396027037)
  ·
    refine ⟨11817958630289629648510139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31514556347439012396027037 11817958630289629648510139)
    ·
      refine ⟨17726937945434444472765209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11817958630289629648510139 17726937945434444472765209)
      ·
        refine ⟨13295203459075833354573907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17726937945434444472765209 13295203459075833354573907)
        ·
          refine ⟨19942805188613750031860861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295203459075833354573907 19942805188613750031860861)
          ·
            refine ⟨7478551945730156261947823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19942805188613750031860861 7478551945730156261947823)
            ·
              refine ⟨11217827918595234392921735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7478551945730156261947823 11217827918595234392921735)
              ·
                refine ⟨16826741877892851589382603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11217827918595234392921735 16826741877892851589382603)
                ·
                  refine ⟨25240112816839277384073905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16826741877892851589382603 25240112816839277384073905)
                  ·
                    refine ⟨18930084612629458038055429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25240112816839277384073905 18930084612629458038055429)
                    ·
                      refine ⟨3549390864868023382135393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18930084612629458038055429 3549390864868023382135393)
                      ·
                        rfl

theorem cell23_6912414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6912414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912414 prefixEnd_6912414 := by exact prefixLift 6912414
  have htrace : WordTrace (prefixWord ++ tailWord_6912414) baseStart_6912414 baseEnd_6912414 := by
    simpa [prefixWord, tailWord_6912414, baseEnd_6912414] using wordTrace_append hprefix tailTrace_6912414
  have hstable : (prefixWord ++ tailWord_6912414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912414).length < 2 ^ (prefixWord ++ tailWord_6912414).sum := by decide
  have hdescent : baseEnd_6912414 < baseStart_6912414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912440 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 3, 4, 2]
def baseStart_6912440 : Nat := 118140960795 + 6912440 * 2 ^ 59
def prefixEnd_6912440 : Nat := 4983230072969 + 3 ^ 40 * 6912440 * 2
def baseEnd_6912440 : Nat := 3549404215365040280410273

theorem tailTrace_6912440 : CollatzResearch.WordTrace tailWord_6912440 prefixEnd_6912440 3549404215365040280410273 := by
  unfold tailWord_6912440
  simp only [CollatzResearch.WordTrace]
  refine ⟨126058699538708952804331387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168078266051611937072441849 126058699538708952804331387)
  ·
    refine ⟨189088049308063429206497081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126058699538708952804331387 189088049308063429206497081)
    ·
      refine ⟨141816036981047571904872811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189088049308063429206497081 141816036981047571904872811)
      ·
        refine ⟨212724055471571357857309217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141816036981047571904872811 212724055471571357857309217)
        ·
          refine ⟨159543041603678518392981913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212724055471571357857309217 159543041603678518392981913)
          ·
            refine ⟨119657281202758888794736435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159543041603678518392981913 119657281202758888794736435)
            ·
              refine ⟨179485921804138333192104653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119657281202758888794736435 179485921804138333192104653)
              ·
                refine ⟨67307220676551874947039245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179485921804138333192104653 67307220676551874947039245)
                ·
                  refine ⟨25240207753706953105139717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67307220676551874947039245 25240207753706953105139717)
                  ·
                    refine ⟨4732538953820053707213697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25240207753706953105139717 4732538953820053707213697)
                    ·
                      refine ⟨3549404215365040280410273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732538953820053707213697 3549404215365040280410273)
                      ·
                        rfl

theorem cell23_6912440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_6912440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912440 prefixEnd_6912440 := by exact prefixLift 6912440
  have htrace : WordTrace (prefixWord ++ tailWord_6912440) baseStart_6912440 baseEnd_6912440 := by
    simpa [prefixWord, tailWord_6912440, baseEnd_6912440] using wordTrace_append hprefix tailTrace_6912440
  have hstable : (prefixWord ++ tailWord_6912440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912440).length < 2 ^ (prefixWord ++ tailWord_6912440).sum := by decide
  have hdescent : baseEnd_6912440 < baseStart_6912440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912443 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 3]
def baseStart_6912443 : Nat := 118140960795 + 6912443 * 2 ^ 59
def prefixEnd_6912443 : Nat := 4983230072969 + 3 ^ 40 * 6912443 * 2
def baseEnd_6912443 : Nat := 3549405755807003768672759

theorem tailTrace_6912443 : CollatzResearch.WordTrace tailWord_6912443 prefixEnd_6912443 3549405755807003768672759 := by
  unfold tailWord_6912443
  simp only [CollatzResearch.WordTrace]
  refine ⟨252117508496407037121021983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168078338997604691414014655 252117508496407037121021983)
  ·
    refine ⟨378176262744610555681532975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252117508496407037121021983 378176262744610555681532975)
    ·
      refine ⟨567264394116915833522299463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378176262744610555681532975 567264394116915833522299463)
      ·
        refine ⟨850896591175373750283449195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567264394116915833522299463 850896591175373750283449195)
        ·
          refine ⟨1276344886763060625425173793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850896591175373750283449195 1276344886763060625425173793)
          ·
            refine ⟨957258665072295469068880345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276344886763060625425173793 957258665072295469068880345)
            ·
              refine ⟨717943998804221601801660259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957258665072295469068880345 717943998804221601801660259)
              ·
                refine ⟨1076915998206332402702490389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717943998804221601801660259 1076915998206332402702490389)
                ·
                  refine ⟨50480437415921831376679237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1076915998206332402702490389 50480437415921831376679237)
                  ·
                    refine ⟨9465082015485343383127357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50480437415921831376679237 9465082015485343383127357)
                    ·
                      refine ⟨3549405755807003768672759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9465082015485343383127357 3549405755807003768672759)
                      ·
                        rfl

theorem cell23_6912443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 3].length) (baseStart_6912443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912443 prefixEnd_6912443 := by exact prefixLift 6912443
  have htrace : WordTrace (prefixWord ++ tailWord_6912443) baseStart_6912443 baseEnd_6912443 := by
    simpa [prefixWord, tailWord_6912443, baseEnd_6912443] using wordTrace_append hprefix tailTrace_6912443
  have hstable : (prefixWord ++ tailWord_6912443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912443).length < 2 ^ (prefixWord ++ tailWord_6912443).sum := by decide
  have hdescent : baseEnd_6912443 < baseStart_6912443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912444 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6912444 : Nat := 118140960795 + 6912444 * 2 ^ 59
def prefixEnd_6912444 : Nat := 4983230072969 + 3 ^ 40 * 6912444 * 2
def baseEnd_6912444 : Nat := 3549406269287658264760255

theorem tailTrace_6912444 : CollatzResearch.WordTrace tailWord_6912444 prefixEnd_6912444 3549406269287658264760255 := by
  unfold tailWord_6912444
  simp only [CollatzResearch.WordTrace]
  refine ⟨126058772484701707145904193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168078363312935609527872257 126058772484701707145904193)
  ·
    refine ⟨94544079363526280359428145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126058772484701707145904193 94544079363526280359428145)
    ·
      refine ⟨70908059522644710269571109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94544079363526280359428145 70908059522644710269571109)
      ·
        refine ⟨13295261160495883175544583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70908059522644710269571109 13295261160495883175544583)
        ·
          refine ⟨19942891740743824763316875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295261160495883175544583 19942891740743824763316875)
          ·
            refine ⟨29914337611115737144975313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19942891740743824763316875 29914337611115737144975313)
            ·
              refine ⟨22435753208336802858731485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29914337611115737144975313 22435753208336802858731485)
              ·
                refine ⟨8413407453126301072024307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22435753208336802858731485 8413407453126301072024307)
                ·
                  refine ⟨12620111179689451608036461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8413407453126301072024307 12620111179689451608036461)
                  ·
                    refine ⟨4732541692383544353013673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12620111179689451608036461 4732541692383544353013673)
                    ·
                      refine ⟨3549406269287658264760255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732541692383544353013673 3549406269287658264760255)
                      ·
                        rfl

theorem cell23_6912444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6912444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912444 prefixEnd_6912444 := by exact prefixLift 6912444
  have htrace : WordTrace (prefixWord ++ tailWord_6912444) baseStart_6912444 baseEnd_6912444 := by
    simpa [prefixWord, tailWord_6912444, baseEnd_6912444] using wordTrace_append hprefix tailTrace_6912444
  have hstable : (prefixWord ++ tailWord_6912444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912444).length < 2 ^ (prefixWord ++ tailWord_6912444).sum := by decide
  have hdescent : baseEnd_6912444 < baseStart_6912444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912457 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 4, 2, 2]
def baseStart_6912457 : Nat := 118140960795 + 6912457 * 2 ^ 59
def prefixEnd_6912457 : Nat := 4983230072969 + 3 ^ 40 * 6912457 * 2
def baseEnd_6912457 : Nat := 3549412944536166713897695

theorem tailTrace_6912457 : CollatzResearch.WordTrace tailWord_6912457 prefixEnd_6912457 3549412944536166713897695 := by
  unfold tailWord_6912457
  simp only [CollatzResearch.WordTrace]
  refine ⟨252118019118356317512031625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168078679412237545008021083 252118019118356317512031625)
  ·
    refine ⟨189088514338767238134023719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252118019118356317512031625 189088514338767238134023719)
    ·
      refine ⟨283632771508150857201035579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189088514338767238134023719 283632771508150857201035579)
      ·
        refine ⟨425449157262226285801553369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283632771508150857201035579 425449157262226285801553369)
        ·
          refine ⟨319086867946669714351165027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425449157262226285801553369 319086867946669714351165027)
          ·
            refine ⟨478630301920004571526747541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319086867946669714351165027 478630301920004571526747541)
            ·
              refine ⟨22435795402500214290316291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 478630301920004571526747541 22435795402500214290316291)
              ·
                refine ⟨33653693103750321435474437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22435795402500214290316291 33653693103750321435474437)
                ·
                  refine ⟨6310067456953185269151457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33653693103750321435474437 6310067456953185269151457)
                  ·
                    refine ⟨4732550592714888951863593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6310067456953185269151457 4732550592714888951863593)
                    ·
                      refine ⟨3549412944536166713897695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732550592714888951863593 3549412944536166713897695)
                      ·
                        rfl

theorem cell23_6912457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 2, 2].length) (baseStart_6912457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912457 prefixEnd_6912457 := by exact prefixLift 6912457
  have htrace : WordTrace (prefixWord ++ tailWord_6912457) baseStart_6912457 baseEnd_6912457 := by
    simpa [prefixWord, tailWord_6912457, baseEnd_6912457] using wordTrace_append hprefix tailTrace_6912457
  have hstable : (prefixWord ++ tailWord_6912457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912457).length < 2 ^ (prefixWord ++ tailWord_6912457).sum := by decide
  have hdescent : baseEnd_6912457 < baseStart_6912457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912474 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2]
def baseStart_6912474 : Nat := 118140960795 + 6912474 * 2 ^ 59
def prefixEnd_6912474 : Nat := 4983230072969 + 3 ^ 40 * 6912474 * 2
def baseEnd_6912474 : Nat := 3549421673707293147385117

theorem tailTrace_6912474 : CollatzResearch.WordTrace tailWord_6912474 prefixEnd_6912474 3549421673707293147385117 := by
  unfold tailWord_6912474
  simp only [CollatzResearch.WordTrace]
  refine ⟨63029659789823682353850119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168079092772863152943600317 63029659789823682353850119)
  ·
    refine ⟨94544489684735523530775179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63029659789823682353850119 94544489684735523530775179)
    ·
      refine ⟨141816734527103285296162769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94544489684735523530775179 141816734527103285296162769)
      ·
        refine ⟨106362550895327463972122077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141816734527103285296162769 106362550895327463972122077)
        ·
          refine ⟨39885956585747798989545779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106362550895327463972122077 39885956585747798989545779)
          ·
            refine ⟨59828934878621698484318669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39885956585747798989545779 59828934878621698484318669)
            ·
              refine ⟨22435850579483136931619501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59828934878621698484318669 22435850579483136931619501)
              ·
                refine ⟨8413443967306176349357313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22435850579483136931619501 8413443967306176349357313)
                ·
                  refine ⟨6310082975479632262017985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8413443967306176349357313 6310082975479632262017985)
                  ·
                    refine ⟨4732562231609724196513489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6310082975479632262017985 4732562231609724196513489)
                    ·
                      refine ⟨3549421673707293147385117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732562231609724196513489 3549421673707293147385117)
                      ·
                        rfl

theorem cell23_6912474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_6912474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912474 prefixEnd_6912474 := by exact prefixLift 6912474
  have htrace : WordTrace (prefixWord ++ tailWord_6912474) baseStart_6912474 baseEnd_6912474 := by
    simpa [prefixWord, tailWord_6912474, baseEnd_6912474] using wordTrace_append hprefix tailTrace_6912474
  have hstable : (prefixWord ++ tailWord_6912474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912474).length < 2 ^ (prefixWord ++ tailWord_6912474).sum := by decide
  have hdescent : baseEnd_6912474 < baseStart_6912474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912544 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 2, 5]
def baseStart_6912544 : Nat := 118140960795 + 6912544 * 2 ^ 59
def prefixEnd_6912544 : Nat := 4983230072969 + 3 ^ 40 * 6912544 * 2
def baseEnd_6912544 : Nat := 1183152539117702624503265

theorem tailTrace_6912544 : CollatzResearch.WordTrace tailWord_6912544 prefixEnd_6912544 1183152539117702624503265 := by
  unfold tailWord_6912544
  simp only [CollatzResearch.WordTrace]
  refine ⟨126060596134520565685224343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168080794846027420913632457 126060596134520565685224343)
  ·
    refine ⟨189090894201780848527836515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126060596134520565685224343 189090894201780848527836515)
    ·
      refine ⟨283636341302671272791754773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189090894201780848527836515 283636341302671272791754773)
      ·
        refine ⟨13295453498562715912113505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 283636341302671272791754773 13295453498562715912113505)
        ·
          refine ⟨9971590123922036934085129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13295453498562715912113505 9971590123922036934085129)
          ·
            refine ⟨7478692592941527700563847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9971590123922036934085129 7478692592941527700563847)
            ·
              refine ⟨11218038889412291550845771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7478692592941527700563847 11218038889412291550845771)
              ·
                refine ⟨16827058334118437326268657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11218038889412291550845771 16827058334118437326268657)
                ·
                  refine ⟨12620293750588827994701493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16827058334118437326268657 12620293750588827994701493)
                  ·
                    refine ⟨1183152539117702624503265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12620293750588827994701493 1183152539117702624503265)
                    ·
                      rfl

theorem cell23_6912544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_6912544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912544 prefixEnd_6912544 := by exact prefixLift 6912544
  have htrace : WordTrace (prefixWord ++ tailWord_6912544) baseStart_6912544 baseEnd_6912544 := by
    simpa [prefixWord, tailWord_6912544, baseEnd_6912544] using wordTrace_append hprefix tailTrace_6912544
  have hstable : (prefixWord ++ tailWord_6912544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912544).length < 2 ^ (prefixWord ++ tailWord_6912544).sum := by decide
  have hdescent : baseEnd_6912544 < baseStart_6912544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912547 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 4]
def baseStart_6912547 : Nat := 118140960795 + 6912547 * 2 ^ 59
def prefixEnd_6912547 : Nat := 4983230072969 + 3 ^ 40 * 6912547 * 2
def baseEnd_6912547 : Nat := 3549459157795071361772281

theorem tailTrace_6912547 : CollatzResearch.WordTrace tailWord_6912547 prefixEnd_6912547 3549459157795071361772281 := by
  unfold tailWord_6912547
  simp only [CollatzResearch.WordTrace]
  refine ⟨252121301688030262882807895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168080867792020175255205263 252121301688030262882807895)
  ·
    refine ⟨378181952532045394324211843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252121301688030262882807895 378181952532045394324211843)
    ·
      refine ⟨567272928798068091486317765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378181952532045394324211843 567272928798068091486317765)
      ·
        refine ⟨106363674149637767153684581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 567272928798068091486317765 106363674149637767153684581)
        ·
          refine ⟨19943188903057081341315859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106363674149637767153684581 19943188903057081341315859)
          ·
            refine ⟨29914783354585622011973789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19943188903057081341315859 29914783354585622011973789)
            ·
              refine ⟨11218043757969608254490171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29914783354585622011973789 11218043757969608254490171)
              ·
                refine ⟨16827065636954412381735257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11218043757969608254490171 16827065636954412381735257)
                ·
                  refine ⟨12620299227715809286301443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16827065636954412381735257 12620299227715809286301443)
                  ·
                    refine ⟨18930448841573713929452165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12620299227715809286301443 18930448841573713929452165)
                    ·
                      refine ⟨3549459157795071361772281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18930448841573713929452165 3549459157795071361772281)
                      ·
                        rfl

theorem cell23_6912547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_6912547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912547 prefixEnd_6912547 := by exact prefixLift 6912547
  have htrace : WordTrace (prefixWord ++ tailWord_6912547) baseStart_6912547 baseEnd_6912547 := by
    simpa [prefixWord, tailWord_6912547, baseEnd_6912547] using wordTrace_append hprefix tailTrace_6912547
  have hstable : (prefixWord ++ tailWord_6912547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912547).length < 2 ^ (prefixWord ++ tailWord_6912547).sum := by decide
  have hdescent : baseEnd_6912547 < baseStart_6912547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912570 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 8]
def baseStart_6912570 : Nat := 118140960795 + 6912570 * 2 ^ 59
def prefixEnd_6912570 : Nat := 4983230072969 + 3 ^ 40 * 6912570 * 2
def baseEnd_6912570 : Nat := 394385663094458307976075

theorem tailTrace_6912570 : CollatzResearch.WordTrace tailWord_6912570 prefixEnd_6912570 394385663094458307976075 := by
  unfold tailWord_6912570
  simp only [CollatzResearch.WordTrace]
  refine ⟨63030535141736734452723791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168081427044631291873930109 63030535141736734452723791)
  ·
    refine ⟨94545802712605101679085687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63030535141736734452723791 94545802712605101679085687)
    ·
      refine ⟨141818704068907652518628531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94545802712605101679085687 141818704068907652518628531)
      ·
        refine ⟨212728056103361478777942797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141818704068907652518628531 212728056103361478777942797)
        ·
          refine ⟨79773021038760554541728549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212728056103361478777942797 79773021038760554541728549)
          ·
            refine ⟨14957441444767603976574103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79773021038760554541728549 14957441444767603976574103)
            ·
              refine ⟨22436162167151405964861155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14957441444767603976574103 22436162167151405964861155)
              ·
                refine ⟨33654243250727108947291733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22436162167151405964861155 33654243250727108947291733)
                ·
                  refine ⟨394385663094458307976075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33654243250727108947291733 394385663094458307976075)
                  ·
                    rfl

theorem cell23_6912570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_6912570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912570 prefixEnd_6912570 := by exact prefixLift 6912570
  have htrace : WordTrace (prefixWord ++ tailWord_6912570) baseStart_6912570 baseEnd_6912570 := by
    simpa [prefixWord, tailWord_6912570, baseEnd_6912570] using wordTrace_append hprefix tailTrace_6912570
  have hstable : (prefixWord ++ tailWord_6912570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912570).length < 2 ^ (prefixWord ++ tailWord_6912570).sum := by decide
  have hdescent : baseEnd_6912570 < baseStart_6912570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912600 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 3, 5]
def baseStart_6912600 : Nat := 118140960795 + 6912600 * 2 ^ 59
def prefixEnd_6912600 : Nat := 4983230072969 + 3 ^ 40 * 6912600 * 2
def baseEnd_6912600 : Nat := 1183162124089919884803179

theorem tailTrace_6912600 : CollatzResearch.WordTrace tailWord_6912600 prefixEnd_6912600 1183162124089919884803179 := by
  unfold tailWord_6912600
  simp only [CollatzResearch.WordTrace]
  refine ⟨126061617378419126467243627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168082156504558835289658169 126061617378419126467243627)
  ·
    refine ⟨189092426067628689700865441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126061617378419126467243627 189092426067628689700865441)
    ·
      refine ⟨141819319550721517275649081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189092426067628689700865441 141819319550721517275649081)
      ·
        refine ⟨106364489663041137956736811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141819319550721517275649081 106364489663041137956736811)
        ·
          refine ⟨159546734494561706935105217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106364489663041137956736811 159546734494561706935105217)
          ·
            refine ⟨119660050870921280201328913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159546734494561706935105217 119660050870921280201328913)
            ·
              refine ⟨89745038153190960150996685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119660050870921280201328913 89745038153190960150996685)
              ·
                refine ⟨33654389307446610056623757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89745038153190960150996685 33654389307446610056623757)
                ·
                  refine ⟨12620395990292478771233909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33654389307446610056623757 12620395990292478771233909)
                  ·
                    refine ⟨1183162124089919884803179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12620395990292478771233909 1183162124089919884803179)
                    ·
                      rfl

theorem cell23_6912600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_6912600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912600 prefixEnd_6912600 := by exact prefixLift 6912600
  have htrace : WordTrace (prefixWord ++ tailWord_6912600) baseStart_6912600 baseEnd_6912600 := by
    simpa [prefixWord, tailWord_6912600, baseEnd_6912600] using wordTrace_append hprefix tailTrace_6912600
  have hstable : (prefixWord ++ tailWord_6912600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912600).length < 2 ^ (prefixWord ++ tailWord_6912600).sum := by decide
  have hdescent : baseEnd_6912600 < baseStart_6912600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912607 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 6, 3, 2]
def baseStart_6912607 : Nat := 118140960795 + 6912607 * 2 ^ 59
def prefixEnd_6912607 : Nat := 4983230072969 + 3 ^ 40 * 6912607 * 2
def baseEnd_6912607 : Nat := 3549489966634341127022005

theorem tailTrace_6912607 : CollatzResearch.WordTrace tailWord_6912607 prefixEnd_6912607 3549489966634341127022005 := by
  unfold tailWord_6912607
  simp only [CollatzResearch.WordTrace]
  refine ⟨252123490067812893129992075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168082326711875262086661383 252123490067812893129992075)
  ·
    refine ⟨378185235101719339694988113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252123490067812893129992075 378185235101719339694988113)
    ·
      refine ⟨283638926326289504771241085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378185235101719339694988113 283638926326289504771241085)
      ·
        refine ⟨106364597372358564289215407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283638926326289504771241085 106364597372358564289215407)
        ·
          refine ⟨159546896058537846433823111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106364597372358564289215407 159546896058537846433823111)
          ·
            refine ⟨239320344087806769650734667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159546896058537846433823111 239320344087806769650734667)
            ·
              refine ⟨358980516131710154476102001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239320344087806769650734667 358980516131710154476102001)
              ·
                refine ⟨269235387098782615857076501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358980516131710154476102001 269235387098782615857076501)
                ·
                  refine ⟨12620408770255435118300461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269235387098782615857076501 12620408770255435118300461)
                  ·
                    refine ⟨4732653288845788169362673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12620408770255435118300461 4732653288845788169362673)
                    ·
                      refine ⟨3549489966634341127022005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732653288845788169362673 3549489966634341127022005)
                      ·
                        rfl

theorem cell23_6912607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_6912607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912607 prefixEnd_6912607 := by exact prefixLift 6912607
  have htrace : WordTrace (prefixWord ++ tailWord_6912607) baseStart_6912607 baseEnd_6912607 := by
    simpa [prefixWord, tailWord_6912607, baseEnd_6912607] using wordTrace_append hprefix tailTrace_6912607
  have hstable : (prefixWord ++ tailWord_6912607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912607).length < 2 ^ (prefixWord ++ tailWord_6912607).sum := by decide
  have hdescent : baseEnd_6912607 < baseStart_6912607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912704 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3]
def baseStart_6912704 : Nat := 118140960795 + 6912704 * 2 ^ 59
def prefixEnd_6912704 : Nat := 4983230072969 + 3 ^ 40 * 6912704 * 2
def baseEnd_6912704 : Nat := 3549539774257827247509059

theorem tailTrace_6912704 : CollatzResearch.WordTrace tailWord_6912704 prefixEnd_6912704 3549539774257827247509059 := by
  unfold tailWord_6912704
  simp only [CollatzResearch.WordTrace]
  refine ⟨126063513974230739348136583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168084685298974319130848777 126063513974230739348136583)
  ·
    refine ⟨189095270961346109022204875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126063513974230739348136583 189095270961346109022204875)
    ·
      refine ⟨283642906442019163533307313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189095270961346109022204875 283642906442019163533307313)
      ·
        refine ⟨212732179831514372649980485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283642906442019163533307313 212732179831514372649980485)
        ·
          refine ⟨39887283718408944871871341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212732179831514372649980485 39887283718408944871871341)
          ·
            refine ⟨14957731394403354326951753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39887283718408944871871341 14957731394403354326951753)
            ·
              refine ⟨11218298545802515745213815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14957731394403354326951753 11218298545802515745213815)
              ·
                refine ⟨16827447818703773617820723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11218298545802515745213815 16827447818703773617820723)
                ·
                  refine ⟨25241171728055660426731085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16827447818703773617820723 25241171728055660426731085)
                  ·
                    refine ⟨9465439398020872660024157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25241171728055660426731085 9465439398020872660024157)
                    ·
                      refine ⟨3549539774257827247509059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9465439398020872660024157 3549539774257827247509059)
                      ·
                        rfl

theorem cell23_6912704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_6912704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912704 prefixEnd_6912704 := by exact prefixLift 6912704
  have htrace : WordTrace (prefixWord ++ tailWord_6912704) baseStart_6912704 baseEnd_6912704 := by
    simpa [prefixWord, tailWord_6912704, baseEnd_6912704] using wordTrace_append hprefix tailTrace_6912704
  have hstable : (prefixWord ++ tailWord_6912704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912704).length < 2 ^ (prefixWord ++ tailWord_6912704).sum := by decide
  have hdescent : baseEnd_6912704 < baseStart_6912704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912705 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6912705 : Nat := 118140960795 + 6912705 * 2 ^ 59
def prefixEnd_6912705 : Nat := 4983230072969 + 3 ^ 40 * 6912705 * 2
def baseEnd_6912705 : Nat := 3549540287738481743596555

theorem tailTrace_6912705 : CollatzResearch.WordTrace tailWord_6912705 prefixEnd_6912705 3549540287738481743596555 := by
  unfold tailWord_6912705
  simp only [CollatzResearch.WordTrace]
  refine ⟨252127064421457855867059569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168084709614305237244706379 252127064421457855867059569)
  ·
    refine ⟨189095298316093391900294677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252127064421457855867059569 189095298316093391900294677)
    ·
      refine ⟨8863842108566877745326313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189095298316093391900294677 8863842108566877745326313)
      ·
        refine ⟨6647881581425158308994735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8863842108566877745326313 6647881581425158308994735)
        ·
          refine ⟨9971822372137737463492103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647881581425158308994735 9971822372137737463492103)
          ·
            refine ⟨14957733558206606195238155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9971822372137737463492103 14957733558206606195238155)
            ·
              refine ⟨22436600337309909292857233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14957733558206606195238155 22436600337309909292857233)
              ·
                refine ⟨16827450252982431969642925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22436600337309909292857233 16827450252982431969642925)
                ·
                  refine ⟨6310293844868411988616097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16827450252982431969642925 6310293844868411988616097)
                  ·
                    refine ⟨4732720383651308991462073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6310293844868411988616097 4732720383651308991462073)
                    ·
                      refine ⟨3549540287738481743596555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732720383651308991462073 3549540287738481743596555)
                      ·
                        rfl

theorem cell23_6912705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6912705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912705 prefixEnd_6912705 := by exact prefixLift 6912705
  have htrace : WordTrace (prefixWord ++ tailWord_6912705) baseStart_6912705 baseEnd_6912705 := by
    simpa [prefixWord, tailWord_6912705, baseEnd_6912705] using wordTrace_append hprefix tailTrace_6912705
  have hstable : (prefixWord ++ tailWord_6912705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912705).length < 2 ^ (prefixWord ++ tailWord_6912705).sum := by decide
  have hdescent : baseEnd_6912705 < baseStart_6912705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912725 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6912725 : Nat := 118140960795 + 6912725 * 2 ^ 59
def prefixEnd_6912725 : Nat := 4983230072969 + 3 ^ 40 * 6912725 * 2
def baseEnd_6912725 : Nat := 3549550557351571665346463

theorem tailTrace_6912725 : CollatzResearch.WordTrace tailWord_6912725 prefixEnd_6912725 3549550557351571665346463 := by
  unfold tailWord_6912725
  simp only [CollatzResearch.WordTrace]
  refine ⟨252127793881385399282787629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168085195920923599521858419 252127793881385399282787629)
  ·
    refine ⟨94547922705519524731045361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252127793881385399282787629 94547922705519524731045361)
    ·
      refine ⟨70910942029139643548284021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94547922705519524731045361 70910942029139643548284021)
      ·
        refine ⟨6647900815231841582651627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70910942029139643548284021 6647900815231841582651627)
        ·
          refine ⟨9971851222847762373977441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647900815231841582651627 9971851222847762373977441)
          ·
            refine ⟨7478888417135821780483081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9971851222847762373977441 7478888417135821780483081)
            ·
              refine ⟨5609166312851866335362311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7478888417135821780483081 5609166312851866335362311)
              ·
                refine ⟨8413749469277799503043467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609166312851866335362311 8413749469277799503043467)
                ·
                  refine ⟨12620624203916699254565201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8413749469277799503043467 12620624203916699254565201)
                  ·
                    refine ⟨9465468152937524440923901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12620624203916699254565201 9465468152937524440923901)
                    ·
                      refine ⟨3549550557351571665346463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9465468152937524440923901 3549550557351571665346463)
                      ·
                        rfl

theorem cell23_6912725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6912725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912725 prefixEnd_6912725 := by exact prefixLift 6912725
  have htrace : WordTrace (prefixWord ++ tailWord_6912725) baseStart_6912725 baseEnd_6912725 := by
    simpa [prefixWord, tailWord_6912725, baseEnd_6912725] using wordTrace_append hprefix tailTrace_6912725
  have hstable : (prefixWord ++ tailWord_6912725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912725).length < 2 ^ (prefixWord ++ tailWord_6912725).sum := by decide
  have hdescent : baseEnd_6912725 < baseStart_6912725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912737 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 2, 6]
def baseStart_6912737 : Nat := 118140960795 + 6912737 * 2 ^ 59
def prefixEnd_6912737 : Nat := 4983230072969 + 3 ^ 40 * 6912737 * 2
def baseEnd_6912737 : Nat := 1183185573039808539465469

theorem tailTrace_6912737 : CollatzResearch.WordTrace tailWord_6912737 prefixEnd_6912737 1183185573039808539465469 := by
  unfold tailWord_6912737
  simp only [CollatzResearch.WordTrace]
  refine ⟨252128231557341925332224465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168085487704894616888149643 252128231557341925332224465)
  ·
    refine ⟨189096173668006443999168349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252128231557341925332224465 189096173668006443999168349)
    ·
      refine ⟨70911065125502416499688131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189096173668006443999168349 70911065125502416499688131)
      ·
        refine ⟨106366597688253624749532197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70911065125502416499688131 106366597688253624749532197)
        ·
          refine ⟨19943737066547554640537287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106366597688253624749532197 19943737066547554640537287)
          ·
            refine ⟨29915605599821331960805931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19943737066547554640537287 29915605599821331960805931)
            ·
              refine ⟨44873408399731997941208897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29915605599821331960805931 44873408399731997941208897)
              ·
                refine ⟨33655056299798998455906673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44873408399731997941208897 33655056299798998455906673)
                ·
                  refine ⟨25241292224849248841930005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33655056299798998455906673 25241292224849248841930005)
                  ·
                    refine ⟨1183185573039808539465469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25241292224849248841930005 1183185573039808539465469)
                    ·
                      rfl

theorem cell23_6912737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_6912737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912737 prefixEnd_6912737 := by exact prefixLift 6912737
  have htrace : WordTrace (prefixWord ++ tailWord_6912737) baseStart_6912737 baseEnd_6912737 := by
    simpa [prefixWord, tailWord_6912737, baseEnd_6912737] using wordTrace_append hprefix tailTrace_6912737
  have hstable : (prefixWord ++ tailWord_6912737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912737).length < 2 ^ (prefixWord ++ tailWord_6912737).sum := by decide
  have hdescent : baseEnd_6912737 < baseStart_6912737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912761 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 2, 2, 2]
def baseStart_6912761 : Nat := 118140960795 + 6912761 * 2 ^ 59
def prefixEnd_6912761 : Nat := 4983230072969 + 3 ^ 40 * 6912761 * 2
def baseEnd_6912761 : Nat := 3549569042655133524496297

theorem tailTrace_6912761 : CollatzResearch.WordTrace tailWord_6912761 prefixEnd_6912761 3549569042655133524496297 := by
  unfold tailWord_6912761
  simp only [CollatzResearch.WordTrace]
  refine ⟨252129106909254977431098137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168086071272836651620732091 252129106909254977431098137)
  ·
    refine ⟨189096830181941233073323603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252129106909254977431098137 189096830181941233073323603)
    ·
      refine ⟨283645245272911849609985405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189096830181941233073323603 283645245272911849609985405)
      ·
        refine ⟨106366966977341943603744527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283645245272911849609985405 106366966977341943603744527)
        ·
          refine ⟨159550450466012915405616791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106366966977341943603744527 159550450466012915405616791)
          ·
            refine ⟨239325675699019373108425187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159550450466012915405616791 239325675699019373108425187)
            ·
              refine ⟨358988513548529059662637781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239325675699019373108425187 358988513548529059662637781)
              ·
                refine ⟨8413793286293649835843073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 358988513548529059662637781 8413793286293649835843073)
                ·
                  refine ⟨6310344964720237376882305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8413793286293649835843073 6310344964720237376882305)
                  ·
                    refine ⟨4732758723540178032661729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6310344964720237376882305 4732758723540178032661729)
                    ·
                      refine ⟨3549569042655133524496297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732758723540178032661729 3549569042655133524496297)
                      ·
                        rfl

theorem cell23_6912761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_6912761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912761 prefixEnd_6912761 := by exact prefixLift 6912761
  have htrace : WordTrace (prefixWord ++ tailWord_6912761) baseStart_6912761 baseEnd_6912761 := by
    simpa [prefixWord, tailWord_6912761, baseEnd_6912761] using wordTrace_append hprefix tailTrace_6912761
  have hstable : (prefixWord ++ tailWord_6912761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912761).length < 2 ^ (prefixWord ++ tailWord_6912761).sum := by decide
  have hdescent : baseEnd_6912761 < baseStart_6912761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912777 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 3]
def baseStart_6912777 : Nat := 118140960795 + 6912777 * 2 ^ 59
def prefixEnd_6912777 : Nat := 4983230072969 + 3 ^ 40 * 6912777 * 2
def baseEnd_6912777 : Nat := 3549577258345605461896223

theorem tailTrace_6912777 : CollatzResearch.WordTrace tailWord_6912777 prefixEnd_6912777 3549577258345605461896223 := by
  unfold tailWord_6912777
  simp only [CollatzResearch.WordTrace]
  refine ⟨252129690477197012163680585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168086460318131341442453723 252129690477197012163680585)
  ·
    refine ⟨189097267857897759122760439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252129690477197012163680585 189097267857897759122760439)
    ·
      refine ⟨283645901786846638684140659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189097267857897759122760439 283645901786846638684140659)
      ·
        refine ⟨425468852680269958026210989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283645901786846638684140659 425468852680269958026210989)
        ·
          refine ⟨159550819755101234259829121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425468852680269958026210989 159550819755101234259829121)
          ·
            refine ⟨119663114816325925694871841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159550819755101234259829121 119663114816325925694871841)
            ·
              refine ⟨89747336112244444271153881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119663114816325925694871841 89747336112244444271153881)
              ·
                refine ⟨67310502084183333203365411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89747336112244444271153881 67310502084183333203365411)
                ·
                  refine ⟨100965753126274999805048117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67310502084183333203365411 100965753126274999805048117)
                  ·
                    refine ⟨9465539355588281231723261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100965753126274999805048117 9465539355588281231723261)
                    ·
                      refine ⟨3549577258345605461896223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9465539355588281231723261 3549577258345605461896223)
                      ·
                        rfl

theorem cell23_6912777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_6912777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912777 prefixEnd_6912777 := by exact prefixLift 6912777
  have htrace : WordTrace (prefixWord ++ tailWord_6912777) baseStart_6912777 baseEnd_6912777 := by
    simpa [prefixWord, tailWord_6912777, baseEnd_6912777] using wordTrace_append hprefix tailTrace_6912777
  have hstable : (prefixWord ++ tailWord_6912777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912777).length < 2 ^ (prefixWord ++ tailWord_6912777).sum := by decide
  have hdescent : baseEnd_6912777 < baseStart_6912777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912801 : List Nat := [1, 2, 3, 2, 1, 2, 5, 2, 5]
def baseStart_6912801 : Nat := 118140960795 + 6912801 * 2 ^ 59
def prefixEnd_6912801 : Nat := 4983230072969 + 3 ^ 40 * 6912801 * 2
def baseEnd_6912801 : Nat := 394398842431257040888457

theorem tailTrace_6912801 : CollatzResearch.WordTrace tailWord_6912801 prefixEnd_6912801 394398842431257040888457 := by
  unfold tailWord_6912801
  simp only [CollatzResearch.WordTrace]
  refine ⟨252130565829110064262554257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168087043886073376175036171 252130565829110064262554257)
  ·
    refine ⟨189097924371832548196915693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252130565829110064262554257 189097924371832548196915693)
    ·
      refine ⟨70911721639437205573843385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189097924371832548196915693 70911721639437205573843385)
      ·
        refine ⟨53183791229577904180382539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70911721639437205573843385 53183791229577904180382539)
        ·
          refine ⟨79775686844366856270573809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53183791229577904180382539 79775686844366856270573809)
          ·
            refine ⟨59831765133275142202930357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79775686844366856270573809 59831765133275142202930357)
            ·
              refine ⟨5609227981244544581524721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59831765133275142202930357 5609227981244544581524721)
              ·
                refine ⟨4206920985933408436143541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5609227981244544581524721 4206920985933408436143541)
                ·
                  refine ⟨394398842431257040888457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4206920985933408436143541 394398842431257040888457)
                  ·
                    rfl

theorem cell23_6912801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 5].length) (baseStart_6912801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912801 prefixEnd_6912801 := by exact prefixLift 6912801
  have htrace : WordTrace (prefixWord ++ tailWord_6912801) baseStart_6912801 baseEnd_6912801 := by
    simpa [prefixWord, tailWord_6912801, baseEnd_6912801] using wordTrace_append hprefix tailTrace_6912801
  have hstable : (prefixWord ++ tailWord_6912801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912801).length < 2 ^ (prefixWord ++ tailWord_6912801).sum := by decide
  have hdescent : baseEnd_6912801 < baseStart_6912801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912878 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_6912878 : Nat := 118140960795 + 6912878 * 2 ^ 59
def prefixEnd_6912878 : Nat := 4983230072969 + 3 ^ 40 * 6912878 * 2
def baseEnd_6912878 : Nat := 1183209706630569855577753

theorem tailTrace_6912878 : CollatzResearch.WordTrace tailWord_6912878 prefixEnd_6912878 1183209706630569855577753 := by
  unfold tailWord_6912878
  simp only [CollatzResearch.WordTrace]
  refine ⟨31516671781228888301638411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168088916166554070942071525 31516671781228888301638411)
  ·
    refine ⟨47275007671843332452457617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31516671781228888301638411 47275007671843332452457617)
    ·
      refine ⟨35456255753882499339343213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47275007671843332452457617 35456255753882499339343213)
      ·
        refine ⟨13296095907705937252253705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35456255753882499339343213 13296095907705937252253705)
        ·
          refine ⟨9972071930779452939190279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13296095907705937252253705 9972071930779452939190279)
          ·
            refine ⟨14958107896169179408785419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972071930779452939190279 14958107896169179408785419)
            ·
              refine ⟨22437161844253769113178129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14958107896169179408785419 22437161844253769113178129)
              ·
                refine ⟨16827871383190326834883597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22437161844253769113178129 16827871383190326834883597)
                ·
                  refine ⟨6310451768696372563081349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16827871383190326834883597 6310451768696372563081349)
                  ·
                    refine ⟨1183209706630569855577753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6310451768696372563081349 1183209706630569855577753)
                    ·
                      rfl

theorem cell23_6912878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_6912878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912878 prefixEnd_6912878 := by exact prefixLift 6912878
  have htrace : WordTrace (prefixWord ++ tailWord_6912878) baseStart_6912878 baseEnd_6912878 := by
    simpa [prefixWord, tailWord_6912878, baseEnd_6912878] using wordTrace_append hprefix tailTrace_6912878
  have hstable : (prefixWord ++ tailWord_6912878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912878).length < 2 ^ (prefixWord ++ tailWord_6912878).sum := by decide
  have hdescent : baseEnd_6912878 < baseStart_6912878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912954 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_6912954 : Nat := 118140960795 + 6912954 * 2 ^ 59
def prefixEnd_6912954 : Nat := 4983230072969 + 3 ^ 40 * 6912954 * 2
def baseEnd_6912954 : Nat := 3549668144421451269382909

theorem tailTrace_6912954 : CollatzResearch.WordTrace tailWord_6912954 prefixEnd_6912954 3549668144421451269382909 := by
  unfold tailWord_6912954
  simp only [CollatzResearch.WordTrace]
  refine ⟨63034036549388942848218479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168090764131703847595249277 63034036549388942848218479)
  ·
    refine ⟨94551054824083414272327719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63034036549388942848218479 94551054824083414272327719)
    ·
      refine ⟨141826582236125121408491579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94551054824083414272327719 141826582236125121408491579)
      ·
        refine ⟨212739873354187682112737369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141826582236125121408491579 212739873354187682112737369)
        ·
          refine ⟨159554905015640761584553027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212739873354187682112737369 159554905015640761584553027)
          ·
            refine ⟨239332357523461142376829541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159554905015640761584553027 239332357523461142376829541)
            ·
              refine ⟨44874817035648964195655539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239332357523461142376829541 44874817035648964195655539)
              ·
                refine ⟨67312225553473446293483309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44874817035648964195655539 67312225553473446293483309)
                ·
                  refine ⟨25242084582552542360056241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67312225553473446293483309 25242084582552542360056241)
                  ·
                    refine ⟨18931563436914406770042181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25242084582552542360056241 18931563436914406770042181)
                    ·
                      refine ⟨3549668144421451269382909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18931563436914406770042181 3549668144421451269382909)
                      ·
                        rfl

theorem cell23_6912954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_6912954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912954 prefixEnd_6912954 := by exact prefixLift 6912954
  have htrace : WordTrace (prefixWord ++ tailWord_6912954) baseStart_6912954 baseEnd_6912954 := by
    simpa [prefixWord, tailWord_6912954, baseEnd_6912954] using wordTrace_append hprefix tailTrace_6912954
  have hstable : (prefixWord ++ tailWord_6912954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912954).length < 2 ^ (prefixWord ++ tailWord_6912954).sum := by decide
  have hdescent : baseEnd_6912954 < baseStart_6912954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912975 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 3, 2, 2]
def baseStart_6912975 : Nat := 118140960795 + 6912975 * 2 ^ 59
def prefixEnd_6912975 : Nat := 4983230072969 + 3 ^ 40 * 6912975 * 2
def baseEnd_6912975 : Nat := 3549678927515195687220313

theorem tailTrace_6912975 : CollatzResearch.WordTrace tailWord_6912975 prefixEnd_6912975 3549678927515195687220313 := by
  unfold tailWord_6912975
  simp only [CollatzResearch.WordTrace]
  refine ⟨252136912130479691979388379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168091274753653127986258919 252136912130479691979388379)
  ·
    refine ⟨378205368195719537969082569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252136912130479691979388379 378205368195719537969082569)
    ·
      refine ⟨283654026146789653476811927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378205368195719537969082569 283654026146789653476811927)
      ·
        refine ⟨425481039220184480215217891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283654026146789653476811927 425481039220184480215217891)
        ·
          refine ⟨638221558830276720322826837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425481039220184480215217891 638221558830276720322826837)
          ·
            refine ⟨7479158892542305316283127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 638221558830276720322826837 7479158892542305316283127)
            ·
              refine ⟨11218738338813457974424691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7479158892542305316283127 11218738338813457974424691)
              ·
                refine ⟨16828107508220186961637037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11218738338813457974424691 16828107508220186961637037)
                ·
                  refine ⟨6310540315582570110613889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16828107508220186961637037 6310540315582570110613889)
                  ·
                    refine ⟨4732905236686927582960417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6310540315582570110613889 4732905236686927582960417)
                    ·
                      refine ⟨3549678927515195687220313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732905236686927582960417 3549678927515195687220313)
                      ·
                        rfl

theorem cell23_6912975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 2, 2].length) (baseStart_6912975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912975 prefixEnd_6912975 := by exact prefixLift 6912975
  have htrace : WordTrace (prefixWord ++ tailWord_6912975) baseStart_6912975 baseEnd_6912975 := by
    simpa [prefixWord, tailWord_6912975, baseEnd_6912975] using wordTrace_append hprefix tailTrace_6912975
  have hstable : (prefixWord ++ tailWord_6912975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912975).length < 2 ^ (prefixWord ++ tailWord_6912975).sum := by decide
  have hdescent : baseEnd_6912975 < baseStart_6912975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912981 : List Nat := [1, 3, 2, 3, 3, 1, 2, 8]
def baseStart_6912981 : Nat := 118140960795 + 6912981 * 2 ^ 59
def prefixEnd_6912981 : Nat := 4983230072969 + 3 ^ 40 * 6912981 * 2
def baseEnd_6912981 : Nat := 131469704014782320879455

theorem tailTrace_6912981 : CollatzResearch.WordTrace tailWord_6912981 prefixEnd_6912981 131469704014782320879455 := by
  unfold tailWord_6912981
  simp only [CollatzResearch.WordTrace]
  refine ⟨252137130968457955004106797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168091420645638636669404531 252137130968457955004106797)
  ·
    refine ⟨94551424113171733126540049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252137130968457955004106797 94551424113171733126540049)
    ·
      refine ⟨70913568084878799844905037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94551424113171733126540049 70913568084878799844905037)
      ·
        refine ⟨26592588031829549941839389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70913568084878799844905037 26592588031829549941839389)
        ·
          refine ⟨9972220511936081228189771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26592588031829549941839389 9972220511936081228189771)
          ·
            refine ⟨14958330767904121842284657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972220511936081228189771 14958330767904121842284657)
            ·
              refine ⟨11218748075928091381713493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14958330767904121842284657 11218748075928091381713493)
              ·
                refine ⟨131469704014782320879455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11218748075928091381713493 131469704014782320879455)
                ·
                  rfl

theorem cell23_6912981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 8].length) (baseStart_6912981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912981 prefixEnd_6912981 := by exact prefixLift 6912981
  have htrace : WordTrace (prefixWord ++ tailWord_6912981) baseStart_6912981 baseEnd_6912981 := by
    simpa [prefixWord, tailWord_6912981, baseEnd_6912981] using wordTrace_append hprefix tailTrace_6912981
  have hstable : (prefixWord ++ tailWord_6912981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912981).length < 2 ^ (prefixWord ++ tailWord_6912981).sum := by decide
  have hdescent : baseEnd_6912981 < baseStart_6912981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6912985 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 2, 4]
def baseStart_6912985 : Nat := 118140960795 + 6912985 * 2 ^ 59
def prefixEnd_6912985 : Nat := 4983230072969 + 3 ^ 40 * 6912985 * 2
def baseEnd_6912985 : Nat := 1183228020773913549365089

theorem tailTrace_6912985 : CollatzResearch.WordTrace tailWord_6912985 prefixEnd_6912985 1183228020773913549365089 := by
  unfold tailWord_6912985
  simp only [CollatzResearch.WordTrace]
  refine ⟨252137276860443463687252409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168091517906962309124834939 252137276860443463687252409)
  ·
    refine ⟨189102957645332597765439307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252137276860443463687252409 189102957645332597765439307)
    ·
      refine ⟨283654436467998896648158961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189102957645332597765439307 283654436467998896648158961)
      ·
        refine ⟨212740827350999172486119221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283654436467998896648158961 212740827350999172486119221)
        ·
          refine ⟨19944452564156172420573677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212740827350999172486119221 19944452564156172420573677)
          ·
            refine ⟨7479169711558564657715129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19944452564156172420573677 7479169711558564657715129)
            ·
              refine ⟨5609377283668923493286347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7479169711558564657715129 5609377283668923493286347)
              ·
                refine ⟨8414065925503385239929521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609377283668923493286347 8414065925503385239929521)
                ·
                  refine ⟨6310549444127538929947141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8414065925503385239929521 6310549444127538929947141)
                  ·
                    refine ⟨1183228020773913549365089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6310549444127538929947141 1183228020773913549365089)
                    ·
                      rfl

theorem cell23_6912985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 4].length) (baseStart_6912985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6912985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6912985 prefixEnd_6912985 := by exact prefixLift 6912985
  have htrace : WordTrace (prefixWord ++ tailWord_6912985) baseStart_6912985 baseEnd_6912985 := by
    simpa [prefixWord, tailWord_6912985, baseEnd_6912985] using wordTrace_append hprefix tailTrace_6912985
  have hstable : (prefixWord ++ tailWord_6912985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6912985).length < 2 ^ (prefixWord ++ tailWord_6912985).sum := by decide
  have hdescent : baseEnd_6912985 < baseStart_6912985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6912985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913018 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2]
def baseStart_6913018 : Nat := 118140960795 + 6913018 * 2 ^ 59
def prefixEnd_6913018 : Nat := 4983230072969 + 3 ^ 40 * 6913018 * 2
def baseEnd_6913018 : Nat := 3549701007183339018982615

theorem tailTrace_6913018 : CollatzResearch.WordTrace tailWord_6913018 prefixEnd_6913018 3549701007183339018982615 := by
  unfold tailWord_6913018
  simp only [CollatzResearch.WordTrace]
  refine ⟨63034620117330977580800927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168092320312882606882135805 63034620117330977580800927)
  ·
    refine ⟨94551930175996466371201391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63034620117330977580800927 94551930175996466371201391)
    ·
      refine ⟨141827895263994699556802087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94551930175996466371201391 141827895263994699556802087)
      ·
        refine ⟨212741842895992049335203131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141827895263994699556802087 212741842895992049335203131)
        ·
          refine ⟨319112764343988074002804697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212741842895992049335203131 319112764343988074002804697)
          ·
            refine ⟨239334573257991055502103523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319112764343988074002804697 239334573257991055502103523)
            ·
              refine ⟨359001859886986583253155285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239334573257991055502103523 359001859886986583253155285)
              ·
                refine ⟨8414106091101248044995827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 359001859886986583253155285 8414106091101248044995827)
                ·
                  refine ⟨12621159136651872067493741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8414106091101248044995827 12621159136651872067493741)
                  ·
                    refine ⟨4732934676244452025310153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12621159136651872067493741 4732934676244452025310153)
                    ·
                      refine ⟨3549701007183339018982615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732934676244452025310153 3549701007183339018982615)
                      ·
                        rfl

theorem cell23_6913018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_6913018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913018 prefixEnd_6913018 := by exact prefixLift 6913018
  have htrace : WordTrace (prefixWord ++ tailWord_6913018) baseStart_6913018 baseEnd_6913018 := by
    simpa [prefixWord, tailWord_6913018, baseEnd_6913018] using wordTrace_append hprefix tailTrace_6913018
  have hstable : (prefixWord ++ tailWord_6913018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913018).length < 2 ^ (prefixWord ++ tailWord_6913018).sum := by decide
  have hdescent : baseEnd_6913018 < baseStart_6913018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913025 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_6913025 : Nat := 118140960795 + 6913025 * 2 ^ 59
def prefixEnd_6913025 : Nat := 4983230072969 + 3 ^ 40 * 6913025 * 2
def baseEnd_6913025 : Nat := 3549704601547920491595083

theorem tailTrace_6913025 : CollatzResearch.WordTrace tailWord_6913025 prefixEnd_6913025 3549704601547920491595083 := by
  unfold tailWord_6913025
  simp only [CollatzResearch.WordTrace]
  refine ⟨252138735780298550518708529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168092490520199033679139019 252138735780298550518708529)
  ·
    refine ⟨189104051835223912889031397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252138735780298550518708529 189104051835223912889031397)
    ·
      refine ⟨35457009719104483666693387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189104051835223912889031397 35457009719104483666693387)
      ·
        refine ⟨53185514578656725500040081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35457009719104483666693387 53185514578656725500040081)
        ·
          refine ⟨39889135933992544125030061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53185514578656725500040081 39889135933992544125030061)
          ·
            refine ⟨14958425975247204046886273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39889135933992544125030061 14958425975247204046886273)
            ·
              refine ⟨11218819481435403035164705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14958425975247204046886273 11218819481435403035164705)
              ·
                refine ⟨8414114611076552276373529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11218819481435403035164705 8414114611076552276373529)
                ·
                  refine ⟨6310585958307414207280147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8414114611076552276373529 6310585958307414207280147)
                  ·
                    refine ⟨9465878937461121310920221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6310585958307414207280147 9465878937461121310920221)
                    ·
                      refine ⟨3549704601547920491595083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9465878937461121310920221 3549704601547920491595083)
                      ·
                        rfl

theorem cell23_6913025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_6913025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913025 prefixEnd_6913025 := by exact prefixLift 6913025
  have htrace : WordTrace (prefixWord ++ tailWord_6913025) baseStart_6913025 baseEnd_6913025 := by
    simpa [prefixWord, tailWord_6913025, baseEnd_6913025] using wordTrace_append hprefix tailTrace_6913025
  have hstable : (prefixWord ++ tailWord_6913025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913025).length < 2 ^ (prefixWord ++ tailWord_6913025).sum := by decide
  have hdescent : baseEnd_6913025 < baseStart_6913025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913026 : List Nat := [3, 4, 1, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6913026 : Nat := 118140960795 + 6913026 * 2 ^ 59
def prefixEnd_6913026 : Nat := 4983230072969 + 3 ^ 40 * 6913026 * 2
def baseEnd_6913026 : Nat := 3549705115028574987682579

theorem tailTrace_6913026 : CollatzResearch.WordTrace tailWord_6913026 prefixEnd_6913026 3549705115028574987682579 := by
  unfold tailWord_6913026
  simp only [CollatzResearch.WordTrace]
  refine ⟨63034693063323731922373733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168092514835529951792996621 63034693063323731922373733)
  ·
    refine ⟨11819004949373199735445075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63034693063323731922373733 11819004949373199735445075)
    ·
      refine ⟨17728507424059799603167613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11819004949373199735445075 17728507424059799603167613)
      ·
        refine ⟨6648190284022424851187855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17728507424059799603167613 6648190284022424851187855)
        ·
          refine ⟨9972285426033637276781783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6648190284022424851187855 9972285426033637276781783)
          ·
            refine ⟨14958428139050455915172675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972285426033637276781783 14958428139050455915172675)
            ·
              refine ⟨22437642208575683872759013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14958428139050455915172675 22437642208575683872759013)
              ·
                refine ⟨4207057914107940726142315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22437642208575683872759013 4207057914107940726142315)
                ·
                  refine ⟨6310586871161911089213473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207057914107940726142315 6310586871161911089213473)
                  ·
                    refine ⟨4732940153371433316910105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6310586871161911089213473 4732940153371433316910105)
                    ·
                      refine ⟨3549705115028574987682579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732940153371433316910105 3549705115028574987682579)
                      ·
                        rfl

theorem cell23_6913026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6913026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913026 prefixEnd_6913026 := by exact prefixLift 6913026
  have htrace : WordTrace (prefixWord ++ tailWord_6913026) baseStart_6913026 baseEnd_6913026 := by
    simpa [prefixWord, tailWord_6913026, baseEnd_6913026] using wordTrace_append hprefix tailTrace_6913026
  have hstable : (prefixWord ++ tailWord_6913026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913026).length < 2 ^ (prefixWord ++ tailWord_6913026).sum := by decide
  have hdescent : baseEnd_6913026 < baseStart_6913026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913048 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 1, 4, 2]
def baseStart_6913048 : Nat := 118140960795 + 6913048 * 2 ^ 59
def prefixEnd_6913048 : Nat := 4983230072969 + 3 ^ 40 * 6913048 * 2
def baseEnd_6913048 : Nat := 3549716411602973901607477

theorem tailTrace_6913048 : CollatzResearch.WordTrace tailWord_6913048 prefixEnd_6913048 3549716411602973901607477 := by
  unfold tailWord_6913048
  simp only [CollatzResearch.WordTrace]
  refine ⟨126069787329607612723397899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168093049772810150297863865 126069787329607612723397899)
  ·
    refine ⟨189104680994411419085096849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126069787329607612723397899 189104680994411419085096849)
    ·
      refine ⟨141828510745808564313822637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189104680994411419085096849 141828510745808564313822637)
      ·
        refine ⟨53185691529678211617683489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141828510745808564313822637 53185691529678211617683489)
        ·
          refine ⟨39889268647258658713262617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53185691529678211617683489 39889268647258658713262617)
          ·
            refine ⟨29916951485443994034946963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39889268647258658713262617 29916951485443994034946963)
            ·
              refine ⟨44875427228165991052420445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29916951485443994034946963 44875427228165991052420445)
              ·
                refine ⟨16828285210562246644657667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44875427228165991052420445 16828285210562246644657667)
                ·
                  refine ⟨25242427815843369966986501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16828285210562246644657667 25242427815843369966986501)
                  ·
                    refine ⟨4732955215470631868809969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25242427815843369966986501 4732955215470631868809969)
                    ·
                      refine ⟨3549716411602973901607477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732955215470631868809969 3549716411602973901607477)
                      ·
                        rfl

theorem cell23_6913048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_6913048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913048 prefixEnd_6913048 := by exact prefixLift 6913048
  have htrace : WordTrace (prefixWord ++ tailWord_6913048) baseStart_6913048 baseEnd_6913048 := by
    simpa [prefixWord, tailWord_6913048, baseEnd_6913048] using wordTrace_append hprefix tailTrace_6913048
  have hstable : (prefixWord ++ tailWord_6913048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913048).length < 2 ^ (prefixWord ++ tailWord_6913048).sum := by decide
  have hdescent : baseEnd_6913048 < baseStart_6913048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913078 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_6913078 : Nat := 118140960795 + 6913078 * 2 ^ 59
def prefixEnd_6913078 : Nat := 4983230072969 + 3 ^ 40 * 6913078 * 2
def baseEnd_6913078 : Nat := 3549731816022608784232339

theorem tailTrace_6913078 : CollatzResearch.WordTrace tailWord_6913078 prefixEnd_6913078 3549731816022608784232339 := by
  unfold tailWord_6913078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758791803069158785649243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168093779232737693713591925 15758791803069158785649243)
  ·
    refine ⟨23638187704603738178473865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15758791803069158785649243 23638187704603738178473865)
    ·
      refine ⟨17728640778452803633855399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23638187704603738178473865 17728640778452803633855399)
      ·
        refine ⟨26592961167679205450783099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17728640778452803633855399 26592961167679205450783099)
        ·
          refine ⟨39889441751518808176174649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26592961167679205450783099 39889441751518808176174649)
          ·
            refine ⟨29917081313639106132130987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39889441751518808176174649 29917081313639106132130987)
            ·
              refine ⟨44875621970458659198196481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29917081313639106132130987 44875621970458659198196481)
              ·
                refine ⟨33656716477843994398647361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44875621970458659198196481 33656716477843994398647361)
                ·
                  refine ⟨25242537358382995798985521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33656716477843994398647361 25242537358382995798985521)
                  ·
                    refine ⟨18931903018787246849239141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25242537358382995798985521 18931903018787246849239141)
                    ·
                      refine ⟨3549731816022608784232339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18931903018787246849239141 3549731816022608784232339)
                      ·
                        rfl

theorem cell23_6913078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_6913078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913078 prefixEnd_6913078 := by exact prefixLift 6913078
  have htrace : WordTrace (prefixWord ++ tailWord_6913078) baseStart_6913078 baseEnd_6913078 := by
    simpa [prefixWord, tailWord_6913078, baseEnd_6913078] using wordTrace_append hprefix tailTrace_6913078
  have hstable : (prefixWord ++ tailWord_6913078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913078).length < 2 ^ (prefixWord ++ tailWord_6913078).sum := by decide
  have hdescent : baseEnd_6913078 < baseStart_6913078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913108 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_6913108 : Nat := 118140960795 + 6913108 * 2 ^ 59
def prefixEnd_6913108 : Nat := 4983230072969 + 3 ^ 40 * 6913108 * 2
def baseEnd_6913108 : Nat := 3549747220442243666857201

theorem tailTrace_6913108 : CollatzResearch.WordTrace tailWord_6913108 prefixEnd_6913108 3549747220442243666857201 := by
  unfold tailWord_6913108
  simp only [CollatzResearch.WordTrace]
  refine ⟨126070881519498927846989989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168094508692665237129319985 126070881519498927846989989)
  ·
    refine ⟨23638290284906048971310623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126070881519498927846989989 23638290284906048971310623)
    ·
      refine ⟨35457435427359073456965935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23638290284906048971310623 35457435427359073456965935)
      ·
        refine ⟨53186153141038610185448903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35457435427359073456965935 53186153141038610185448903)
        ·
          refine ⟨79779229711557915278173355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53186153141038610185448903 79779229711557915278173355)
          ·
            refine ⟨119668844567336872917260033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79779229711557915278173355 119668844567336872917260033)
            ·
              refine ⟨89751633425502654687945025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119668844567336872917260033 89751633425502654687945025)
              ·
                refine ⟨67313725069126991015958769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89751633425502654687945025 67313725069126991015958769)
                ·
                  refine ⟨50485293801845243261969077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67313725069126991015958769 50485293801845243261969077)
                  ·
                    refine ⟨4732996293922991555809601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50485293801845243261969077 4732996293922991555809601)
                    ·
                      refine ⟨3549747220442243666857201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4732996293922991555809601 3549747220442243666857201)
                      ·
                        rfl

theorem cell23_6913108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_6913108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913108 prefixEnd_6913108 := by exact prefixLift 6913108
  have htrace : WordTrace (prefixWord ++ tailWord_6913108) baseStart_6913108 baseEnd_6913108 := by
    simpa [prefixWord, tailWord_6913108, baseEnd_6913108] using wordTrace_append hprefix tailTrace_6913108
  have hstable : (prefixWord ++ tailWord_6913108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913108).length < 2 ^ (prefixWord ++ tailWord_6913108).sum := by decide
  have hdescent : baseEnd_6913108 < baseStart_6913108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913121 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_6913121 : Nat := 118140960795 + 6913121 * 2 ^ 59
def prefixEnd_6913121 : Nat := 4983230072969 + 3 ^ 40 * 6913121 * 2
def baseEnd_6913121 : Nat := 3549753895690752115994641

theorem tailTrace_6913121 : CollatzResearch.WordTrace tailWord_6913121 prefixEnd_6913121 3549753895690752115994641 := by
  unfold tailWord_6913121
  simp only [CollatzResearch.WordTrace]
  refine ⟨252142237187950758914203217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168094824791967172609468811 252142237187950758914203217)
  ·
    refine ⟨189106677890963069185652413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252142237187950758914203217 189106677890963069185652413)
    ·
      refine ⟨70915004209111150944619655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189106677890963069185652413 70915004209111150944619655)
      ·
        refine ⟨106372506313666726416929483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70915004209111150944619655 106372506313666726416929483)
        ·
          refine ⟨159558759470500089625394225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106372506313666726416929483 159558759470500089625394225)
          ·
            refine ⟨119669069602875067219045669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159558759470500089625394225 119669069602875067219045669)
            ·
              refine ⟨22437950550539075103571063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119669069602875067219045669 22437950550539075103571063)
              ·
                refine ⟨33656925825808612655356595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22437950550539075103571063 33656925825808612655356595)
                ·
                  refine ⟨50485388738712918983034893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33656925825808612655356595 50485388738712918983034893)
                  ·
                    refine ⟨18932020777017344618638085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50485388738712918983034893 18932020777017344618638085)
                    ·
                      refine ⟨3549753895690752115994641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18932020777017344618638085 3549753895690752115994641)
                      ·
                        rfl

theorem cell23_6913121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_6913121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913121 prefixEnd_6913121 := by exact prefixLift 6913121
  have htrace : WordTrace (prefixWord ++ tailWord_6913121) baseStart_6913121 baseEnd_6913121 := by
    simpa [prefixWord, tailWord_6913121, baseEnd_6913121] using wordTrace_append hprefix tailTrace_6913121
  have hstable : (prefixWord ++ tailWord_6913121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913121).length < 2 ^ (prefixWord ++ tailWord_6913121).sum := by decide
  have hdescent : baseEnd_6913121 < baseStart_6913121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913122 : List Nat := [3, 3, 2, 2, 1, 3, 1, 3, 5]
def baseStart_6913122 : Nat := 118140960795 + 6913122 * 2 ^ 59
def prefixEnd_6913122 : Nat := 4983230072969 + 3 ^ 40 * 6913122 * 2
def baseEnd_6913122 : Nat := 394417156574600734675793

theorem tailTrace_6913122 : CollatzResearch.WordTrace tailWord_6913122 prefixEnd_6913122 394417156574600734675793 := by
  unfold tailWord_6913122
  simp only [CollatzResearch.WordTrace]
  refine ⟨63035568415236784021247405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168094849107298090723326413 63035568415236784021247405)
  ·
    refine ⟨23638338155713794007967777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63035568415236784021247405 23638338155713794007967777)
    ·
      refine ⟨17728753616785345505975833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23638338155713794007967777 17728753616785345505975833)
      ·
        refine ⟨13296565212589009129481875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17728753616785345505975833 13296565212589009129481875)
        ·
          refine ⟨19944847818883513694222813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13296565212589009129481875 19944847818883513694222813)
          ·
            refine ⟨7479317932081317635333555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19944847818883513694222813 7479317932081317635333555)
            ·
              refine ⟨11218976898121976453000333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7479317932081317635333555 11218976898121976453000333)
              ·
                refine ⟨4207116336795741169875125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11218976898121976453000333 4207116336795741169875125)
                ·
                  refine ⟨394417156574600734675793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4207116336795741169875125 394417156574600734675793)
                  ·
                    rfl

theorem cell23_6913122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_6913122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913122 prefixEnd_6913122 := by exact prefixLift 6913122
  have htrace : WordTrace (prefixWord ++ tailWord_6913122) baseStart_6913122 baseEnd_6913122 := by
    simpa [prefixWord, tailWord_6913122, baseEnd_6913122] using wordTrace_append hprefix tailTrace_6913122
  have hstable : (prefixWord ++ tailWord_6913122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913122).length < 2 ^ (prefixWord ++ tailWord_6913122).sum := by decide
  have hdescent : baseEnd_6913122 < baseStart_6913122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913138 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_6913138 : Nat := 118140960795 + 6913138 * 2 ^ 59
def prefixEnd_6913138 : Nat := 4983230072969 + 3 ^ 40 * 6913138 * 2
def baseEnd_6913138 : Nat := 3549762624861878549482063

theorem tailTrace_6913138 : CollatzResearch.WordTrace tailWord_6913138 prefixEnd_6913138 3549762624861878549482063 := by
  unfold tailWord_6913138
  simp only [CollatzResearch.WordTrace]
  refine ⟨63035714307222292704393017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168095238152592780545048045 63035714307222292704393017)
  ·
    refine ⟨47276785730416719528294763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63035714307222292704393017 47276785730416719528294763)
    ·
      refine ⟨70915178595625079292442145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47276785730416719528294763 70915178595625079292442145)
      ·
        refine ⟨53186383946718809469331609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70915178595625079292442145 53186383946718809469331609)
        ·
          refine ⟨39889787960039107101998707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53186383946718809469331609 39889787960039107101998707)
          ·
            refine ⟨59834681940058660652998061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39889787960039107101998707 59834681940058660652998061)
            ·
              refine ⟨22438005727521997744874273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59834681940058660652998061 22438005727521997744874273)
              ·
                refine ⟨16828504295641498308655705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22438005727521997744874273 16828504295641498308655705)
                ·
                  refine ⟨12621378221731123731491779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16828504295641498308655705 12621378221731123731491779)
                  ·
                    refine ⟨18932067332596685597237669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12621378221731123731491779 18932067332596685597237669)
                    ·
                      refine ⟨3549762624861878549482063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18932067332596685597237669 3549762624861878549482063)
                      ·
                        rfl

theorem cell23_6913138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_6913138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913138 prefixEnd_6913138 := by exact prefixLift 6913138
  have htrace : WordTrace (prefixWord ++ tailWord_6913138) baseStart_6913138 baseEnd_6913138 := by
    simpa [prefixWord, tailWord_6913138, baseEnd_6913138] using wordTrace_append hprefix tailTrace_6913138
  have hstable : (prefixWord ++ tailWord_6913138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913138).length < 2 ^ (prefixWord ++ tailWord_6913138).sum := by decide
  have hdescent : baseEnd_6913138 < baseStart_6913138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913150 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6913150 : Nat := 118140960795 + 6913150 * 2 ^ 59
def prefixEnd_6913150 : Nat := 4983230072969 + 3 ^ 40 * 6913150 * 2
def baseEnd_6913150 : Nat := 3549768786629732502532009

theorem tailTrace_6913150 : CollatzResearch.WordTrace tailWord_6913150 prefixEnd_6913150 3549768786629732502532009 := by
  unfold tailWord_6913150
  simp only [CollatzResearch.WordTrace]
  refine ⟨31517911863105712108376113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168095529936563797911339269 31517911863105712108376113)
  ·
    refine ⟨23638433897329284081282085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31517911863105712108376113 23638433897329284081282085)
    ·
      refine ⟨4432206355749240765240391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23638433897329284081282085 4432206355749240765240391)
      ·
        refine ⟨6648309533623861147860587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4432206355749240765240391 6648309533623861147860587)
        ·
          refine ⟨9972464300435791721790881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6648309533623861147860587 9972464300435791721790881)
          ·
            refine ⟨7479348225326843791343161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9972464300435791721790881 7479348225326843791343161)
            ·
              refine ⟨5609511168995132843507371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7479348225326843791343161 5609511168995132843507371)
              ·
                refine ⟨8414266753492699265261057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609511168995132843507371 8414266753492699265261057)
                ·
                  refine ⟨6310700065119524448945793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8414266753492699265261057 6310700065119524448945793)
                  ·
                    refine ⟨4733025048839643336709345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6310700065119524448945793 4733025048839643336709345)
                    ·
                      refine ⟨3549768786629732502532009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733025048839643336709345 3549768786629732502532009)
                      ·
                        rfl

theorem cell23_6913150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6913150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913150 prefixEnd_6913150 := by exact prefixLift 6913150
  have htrace : WordTrace (prefixWord ++ tailWord_6913150) baseStart_6913150 baseEnd_6913150 := by
    simpa [prefixWord, tailWord_6913150, baseEnd_6913150] using wordTrace_append hprefix tailTrace_6913150
  have hstable : (prefixWord ++ tailWord_6913150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913150).length < 2 ^ (prefixWord ++ tailWord_6913150).sum := by decide
  have hdescent : baseEnd_6913150 < baseStart_6913150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913171 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 3]
def baseStart_6913171 : Nat := 118140960795 + 6913171 * 2 ^ 59
def prefixEnd_6913171 : Nat := 4983230072969 + 3 ^ 40 * 6913171 * 2
def baseEnd_6913171 : Nat := 3549779569723476920369411

theorem tailTrace_6913171 : CollatzResearch.WordTrace tailWord_6913171 prefixEnd_6913171 3549779569723476920369411 := by
  unfold tailWord_6913171
  simp only [CollatzResearch.WordTrace]
  refine ⟨252144060837769617453523367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168096040558513078302348911 252144060837769617453523367)
  ·
    refine ⟨378216091256654426180285051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252144060837769617453523367 378216091256654426180285051)
    ·
      refine ⟨567324136884981639270427577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378216091256654426180285051 567324136884981639270427577)
      ·
        refine ⟨425493102663736229452820683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567324136884981639270427577 425493102663736229452820683)
        ·
          refine ⟨638239653995604344179231025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425493102663736229452820683 638239653995604344179231025)
          ·
            refine ⟨478679740496703258134423269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638239653995604344179231025 478679740496703258134423269)
            ·
              refine ⟨89752451343131860900204363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 478679740496703258134423269 89752451343131860900204363)
              ·
                refine ⟨134628677014697791350306545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89752451343131860900204363 134628677014697791350306545)
                ·
                  refine ⟨100971507761023343512729909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134628677014697791350306545 100971507761023343512729909)
                  ·
                    refine ⟨9466078852595938454318429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100971507761023343512729909 9466078852595938454318429)
                    ·
                      refine ⟨3549779569723476920369411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9466078852595938454318429 3549779569723476920369411)
                      ·
                        rfl

theorem cell23_6913171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_6913171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913171 prefixEnd_6913171 := by exact prefixLift 6913171
  have htrace : WordTrace (prefixWord ++ tailWord_6913171) baseStart_6913171 baseEnd_6913171 := by
    simpa [prefixWord, tailWord_6913171, baseEnd_6913171] using wordTrace_append hprefix tailTrace_6913171
  have hstable : (prefixWord ++ tailWord_6913171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913171).length < 2 ^ (prefixWord ++ tailWord_6913171).sum := by decide
  have hdescent : baseEnd_6913171 < baseStart_6913171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913175 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_6913175 : Nat := 118140960795 + 6913175 * 2 ^ 59
def prefixEnd_6913175 : Nat := 4983230072969 + 3 ^ 40 * 6913175 * 2
def baseEnd_6913175 : Nat := 3549781623646094904719393

theorem tailTrace_6913175 : CollatzResearch.WordTrace tailWord_6913175 prefixEnd_6913175 3549781623646094904719393 := by
  unfold tailWord_6913175
  simp only [CollatzResearch.WordTrace]
  refine ⟨252144206729755126136668979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168096137819836750757779319 252144206729755126136668979)
  ·
    refine ⟨378216310094632689205003469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252144206729755126136668979 378216310094632689205003469)
    ·
      refine ⟨141831116285487258451876301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378216310094632689205003469 141831116285487258451876301)
      ·
        refine ⟨53186668607057721919453613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141831116285487258451876301 53186668607057721919453613)
        ·
          refine ⟨19945000727646645719795105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53186668607057721919453613 19945000727646645719795105)
          ·
            refine ⟨14958750545734984289846329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19945000727646645719795105 14958750545734984289846329)
            ·
              refine ⟨11219062909301238217384747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14958750545734984289846329 11219062909301238217384747)
              ·
                refine ⟨16828594363951857326077121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11219062909301238217384747 16828594363951857326077121)
                ·
                  refine ⟨12621445772963892994557841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16828594363951857326077121 12621445772963892994557841)
                  ·
                    refine ⟨9466084329722919745918381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12621445772963892994557841 9466084329722919745918381)
                    ·
                      refine ⟨3549781623646094904719393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9466084329722919745918381 3549781623646094904719393)
                      ·
                        rfl

theorem cell23_6913175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_6913175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913175 prefixEnd_6913175 := by exact prefixLift 6913175
  have htrace : WordTrace (prefixWord ++ tailWord_6913175) baseStart_6913175 baseEnd_6913175 := by
    simpa [prefixWord, tailWord_6913175, baseEnd_6913175] using wordTrace_append hprefix tailTrace_6913175
  have hstable : (prefixWord ++ tailWord_6913175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913175).length < 2 ^ (prefixWord ++ tailWord_6913175).sum := by decide
  have hdescent : baseEnd_6913175 < baseStart_6913175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913231 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_6913231 : Nat := 118140960795 + 6913231 * 2 ^ 59
def prefixEnd_6913231 : Nat := 4983230072969 + 3 ^ 40 * 6913231 * 2
def baseEnd_6913231 : Nat := 3549810378562746685619135

theorem tailTrace_6913231 : CollatzResearch.WordTrace tailWord_6913231 prefixEnd_6913231 3549810378562746685619135 := by
  unfold tailWord_6913231
  simp only [CollatzResearch.WordTrace]
  refine ⟨252146249217552247700707547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168097499478368165133805031 252146249217552247700707547)
  ·
    refine ⟨378219373826328371551061321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252146249217552247700707547 378219373826328371551061321)
    ·
      refine ⟨283664530369746278663295991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378219373826328371551061321 283664530369746278663295991)
      ·
        refine ⟨425496795554619417994943987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283664530369746278663295991 425496795554619417994943987)
        ·
          refine ⟨638245193331929126992415981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425496795554619417994943987 638245193331929126992415981)
          ·
            refine ⟨239341947499473422622155993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 638245193331929126992415981 239341947499473422622155993)
            ·
              refine ⟨179506460624605066966616995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239341947499473422622155993 179506460624605066966616995)
              ·
                refine ⟨269259690936907600449925493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179506460624605066966616995 269259690936907600449925493)
                ·
                  refine ⟨25243096025335087542180515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269259690936907600449925493 25243096025335087542180515)
                  ·
                    refine ⟨37864644038002631313270773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25243096025335087542180515 37864644038002631313270773)
                    ·
                      refine ⟨3549810378562746685619135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37864644038002631313270773 3549810378562746685619135)
                      ·
                        rfl

theorem cell23_6913231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_6913231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913231 prefixEnd_6913231 := by exact prefixLift 6913231
  have htrace : WordTrace (prefixWord ++ tailWord_6913231) baseStart_6913231 baseEnd_6913231 := by
    simpa [prefixWord, tailWord_6913231, baseEnd_6913231] using wordTrace_append hprefix tailTrace_6913231
  have hstable : (prefixWord ++ tailWord_6913231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913231).length < 2 ^ (prefixWord ++ tailWord_6913231).sum := by decide
  have hdescent : baseEnd_6913231 < baseStart_6913231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913241 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_6913241 : Nat := 118140960795 + 6913241 * 2 ^ 59
def prefixEnd_6913241 : Nat := 4983230072969 + 3 ^ 40 * 6913241 * 2
def baseEnd_6913241 : Nat := 3549815513369291646494089

theorem tailTrace_6913241 : CollatzResearch.WordTrace tailWord_6913241 prefixEnd_6913241 3549815513369291646494089 := by
  unfold tailWord_6913241
  simp only [CollatzResearch.WordTrace]
  refine ⟨252146613947516019408571577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168097742631677346272381051 252146613947516019408571577)
  ·
    refine ⟨189109960460637014556428683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252146613947516019408571577 189109960460637014556428683)
    ·
      refine ⟨283664940690955521834643025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189109960460637014556428683 283664940690955521834643025)
      ·
        refine ⟨212748705518216641375982269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283664940690955521834643025 212748705518216641375982269)
        ·
          refine ⟨79780764569331240515993351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212748705518216641375982269 79780764569331240515993351)
          ·
            refine ⟨119671146853996860773990027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79780764569331240515993351 119671146853996860773990027)
            ·
              refine ⟨179506720280995291160985041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119671146853996860773990027 179506720280995291160985041)
              ·
                refine ⟨134630040210746468370738781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179506720280995291160985041 134630040210746468370738781)
                ·
                  refine ⟨50486265079029925639027043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134630040210746468370738781 50486265079029925639027043)
                  ·
                    refine ⟨75729397618544888458540565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50486265079029925639027043 75729397618544888458540565)
                    ·
                      refine ⟨3549815513369291646494089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75729397618544888458540565 3549815513369291646494089)
                      ·
                        rfl

theorem cell23_6913241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_6913241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913241 prefixEnd_6913241 := by exact prefixLift 6913241
  have htrace : WordTrace (prefixWord ++ tailWord_6913241) baseStart_6913241 baseEnd_6913241 := by
    simpa [prefixWord, tailWord_6913241, baseEnd_6913241] using wordTrace_append hprefix tailTrace_6913241
  have hstable : (prefixWord ++ tailWord_6913241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913241).length < 2 ^ (prefixWord ++ tailWord_6913241).sum := by decide
  have hdescent : baseEnd_6913241 < baseStart_6913241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913262 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_6913262 : Nat := 118140960795 + 6913262 * 2 ^ 59
def prefixEnd_6913262 : Nat := 4983230072969 + 3 ^ 40 * 6913262 * 2
def baseEnd_6913262 : Nat := 3549826296463036064331493

theorem tailTrace_6913262 : CollatzResearch.WordTrace tailWord_6913262 prefixEnd_6913262 3549826296463036064331493 := by
  unfold tailWord_6913262
  simp only [CollatzResearch.WordTrace]
  refine ⟨31518422485054992499385755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168098253253626626663390693 31518422485054992499385755)
  ·
    refine ⟨47277633727582488749078633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31518422485054992499385755 47277633727582488749078633)
    ·
      refine ⟨35458225295686866561808975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47277633727582488749078633 35458225295686866561808975)
      ·
        refine ⟨53187337943530299842713463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35458225295686866561808975 53187337943530299842713463)
        ·
          refine ⟨79781006915295449764070195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53187337943530299842713463 79781006915295449764070195)
          ·
            refine ⟨119671510372943174646105293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79781006915295449764070195 119671510372943174646105293)
            ·
              refine ⟨44876816389853690492289485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119671510372943174646105293 44876816389853690492289485)
              ·
                refine ⟨16828806146195133934608557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44876816389853690492289485 16828806146195133934608557)
                ·
                  refine ⟨6310802304823175225478209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16828806146195133934608557 6310802304823175225478209)
                  ·
                    refine ⟨4733101728617381419108657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6310802304823175225478209 4733101728617381419108657)
                    ·
                      refine ⟨3549826296463036064331493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733101728617381419108657 3549826296463036064331493)
                      ·
                        rfl

theorem cell23_6913262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_6913262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913262 prefixEnd_6913262 := by exact prefixLift 6913262
  have htrace : WordTrace (prefixWord ++ tailWord_6913262) baseStart_6913262 baseEnd_6913262 := by
    simpa [prefixWord, tailWord_6913262, baseEnd_6913262] using wordTrace_append hprefix tailTrace_6913262
  have hstable : (prefixWord ++ tailWord_6913262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913262).length < 2 ^ (prefixWord ++ tailWord_6913262).sum := by decide
  have hdescent : baseEnd_6913262 < baseStart_6913262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913271 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_6913271 : Nat := 118140960795 + 6913271 * 2 ^ 59
def prefixEnd_6913271 : Nat := 4983230072969 + 3 ^ 40 * 6913271 * 2
def baseEnd_6913271 : Nat := 3549830917788926529118951

theorem tailTrace_6913271 : CollatzResearch.WordTrace tailWord_6913271 prefixEnd_6913271 3549830917788926529118951 := by
  unfold tailWord_6913271
  simp only [CollatzResearch.WordTrace]
  refine ⟨252147708137407334532163667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168098472091604889688109111 252147708137407334532163667)
  ·
    refine ⟨378221562206111001798245501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252147708137407334532163667 378221562206111001798245501)
    ·
      refine ⟨141833085827291625674342063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378221562206111001798245501 141833085827291625674342063)
      ·
        refine ⟨212749628740937438511513095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141833085827291625674342063 212749628740937438511513095)
        ·
          refine ⟨319124443111406157767269643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212749628740937438511513095 319124443111406157767269643)
          ·
            refine ⟨478686664667109236650904465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319124443111406157767269643 478686664667109236650904465)
            ·
              refine ⟨359014998500331927488178349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478686664667109236650904465 359014998500331927488178349)
              ·
                refine ⟨134630624437624472808066881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359014998500331927488178349 134630624437624472808066881)
                ·
                  refine ⟨100972968328218354606050161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134630624437624472808066881 100972968328218354606050161)
                  ·
                    refine ⟨75729726246163765954537621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100972968328218354606050161 75729726246163765954537621)
                    ·
                      refine ⟨3549830917788926529118951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75729726246163765954537621 3549830917788926529118951)
                      ·
                        rfl

theorem cell23_6913271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_6913271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913271 prefixEnd_6913271 := by exact prefixLift 6913271
  have htrace : WordTrace (prefixWord ++ tailWord_6913271) baseStart_6913271 baseEnd_6913271 := by
    simpa [prefixWord, tailWord_6913271, baseEnd_6913271] using wordTrace_append hprefix tailTrace_6913271
  have hstable : (prefixWord ++ tailWord_6913271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913271).length < 2 ^ (prefixWord ++ tailWord_6913271).sum := by decide
  have hdescent : baseEnd_6913271 < baseStart_6913271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913329 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 2, 1, 3]
def baseStart_6913329 : Nat := 118140960795 + 6913329 * 2 ^ 59
def prefixEnd_6913329 : Nat := 4983230072969 + 3 ^ 40 * 6913329 * 2
def baseEnd_6913329 : Nat := 3549860699666887302193685

theorem tailTrace_6913329 : CollatzResearch.WordTrace tailWord_6913329 prefixEnd_6913329 3549860699666887302193685 := by
  unfold tailWord_6913329
  simp only [CollatzResearch.WordTrace]
  refine ⟨252149823571197210437775041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168099882380798140291850027 252149823571197210437775041)
  ·
    refine ⟨189112367678397907828331281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252149823571197210437775041 189112367678397907828331281)
    ·
      refine ⟨141834275758798430871248461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189112367678397907828331281 141834275758798430871248461)
      ·
        refine ⟨53187853409549411576718173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141834275758798430871248461 53187853409549411576718173)
        ·
          refine ⟨19945445028581029341269315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53187853409549411576718173 19945445028581029341269315)
          ·
            refine ⟨29918167542871544011903973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19945445028581029341269315 29918167542871544011903973)
            ·
              refine ⟨5609656414288414502231995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29918167542871544011903973 5609656414288414502231995)
              ·
                refine ⟨8414484621432621753347993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609656414288414502231995 8414484621432621753347993)
                ·
                  refine ⟨6310863466074466315010995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8414484621432621753347993 6310863466074466315010995)
                  ·
                    refine ⟨9466295199111699472516493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6310863466074466315010995 9466295199111699472516493)
                    ·
                      refine ⟨3549860699666887302193685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9466295199111699472516493 3549860699666887302193685)
                      ·
                        rfl

theorem cell23_6913329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_6913329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913329 prefixEnd_6913329 := by exact prefixLift 6913329
  have htrace : WordTrace (prefixWord ++ tailWord_6913329) baseStart_6913329 baseEnd_6913329 := by
    simpa [prefixWord, tailWord_6913329, baseEnd_6913329] using wordTrace_append hprefix tailTrace_6913329
  have hstable : (prefixWord ++ tailWord_6913329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913329).length < 2 ^ (prefixWord ++ tailWord_6913329).sum := by decide
  have hdescent : baseEnd_6913329 < baseStart_6913329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913338 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_6913338 : Nat := 118140960795 + 6913338 * 2 ^ 59
def prefixEnd_6913338 : Nat := 4983230072969 + 3 ^ 40 * 6913338 * 2
def baseEnd_6913338 : Nat := 3549865320992777766981143

theorem tailTrace_6913338 : CollatzResearch.WordTrace tailWord_6913338 prefixEnd_6913338 3549865320992777766981143 := by
  unfold tailWord_6913338
  simp only [CollatzResearch.WordTrace]
  refine ⟨63037537957041151243713167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168100101218776403316568445 63037537957041151243713167)
  ·
    refine ⟨94556306935561726865569751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63037537957041151243713167 94556306935561726865569751)
    ·
      refine ⟨141834460403342590298354627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94556306935561726865569751 141834460403342590298354627)
      ·
        refine ⟨212751690605013885447531941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141834460403342590298354627 212751690605013885447531941)
        ·
          refine ⟨39890941988440103521412239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212751690605013885447531941 39890941988440103521412239)
          ·
            refine ⟨59836412982660155282118359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39890941988440103521412239 59836412982660155282118359)
            ·
              refine ⟨89754619473990232923177539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59836412982660155282118359 89754619473990232923177539)
              ·
                refine ⟨134631929210985349384766309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89754619473990232923177539 134631929210985349384766309)
                ·
                  refine ⟨25243486727059753009643683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134631929210985349384766309 25243486727059753009643683)
                  ·
                    refine ⟨37865230090589629514465525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25243486727059753009643683 37865230090589629514465525)
                    ·
                      refine ⟨3549865320992777766981143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37865230090589629514465525 3549865320992777766981143)
                      ·
                        rfl

theorem cell23_6913338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_6913338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913338 prefixEnd_6913338 := by exact prefixLift 6913338
  have htrace : WordTrace (prefixWord ++ tailWord_6913338) baseStart_6913338 baseEnd_6913338 := by
    simpa [prefixWord, tailWord_6913338, baseEnd_6913338] using wordTrace_append hprefix tailTrace_6913338
  have hstable : (prefixWord ++ tailWord_6913338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913338).length < 2 ^ (prefixWord ++ tailWord_6913338).sum := by decide
  have hdescent : baseEnd_6913338 < baseStart_6913338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913409 : List Nat := [1, 2, 4, 3, 2, 1, 2, 3, 5]
def baseStart_6913409 : Nat := 118140960795 + 6913409 * 2 ^ 59
def prefixEnd_6913409 : Nat := 4983230072969 + 3 ^ 40 * 6913409 * 2
def baseEnd_6913409 : Nat := 394433530902138554354813

theorem tailTrace_6913409 : CollatzResearch.WordTrace tailWord_6913409 prefixEnd_6913409 394433530902138554354813 := by
  unfold tailWord_6913409
  simp only [CollatzResearch.WordTrace]
  refine ⟨252152741410907384100687281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168101827607271589400458187 252152741410907384100687281)
  ·
    refine ⟨189114556058180538075515461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252152741410907384100687281 189114556058180538075515461)
    ·
      refine ⟨35458979260908850889159149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189114556058180538075515461 35458979260908850889159149)
      ·
        refine ⟨13297117222840819083434681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35458979260908850889159149 13297117222840819083434681)
        ·
          refine ⟨9972837917130614312576011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13297117222840819083434681 9972837917130614312576011)
          ·
            refine ⟨14959256875695921468864017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972837917130614312576011 14959256875695921468864017)
            ·
              refine ⟨11219442656771941101648013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14959256875695921468864017 11219442656771941101648013)
              ·
                refine ⟨4207290996289477913118005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11219442656771941101648013 4207290996289477913118005)
                ·
                  refine ⟨394433530902138554354813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4207290996289477913118005 394433530902138554354813)
                  ·
                    rfl

theorem cell23_6913409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 5].length) (baseStart_6913409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913409 prefixEnd_6913409 := by exact prefixLift 6913409
  have htrace : WordTrace (prefixWord ++ tailWord_6913409) baseStart_6913409 baseEnd_6913409 := by
    simpa [prefixWord, tailWord_6913409, baseEnd_6913409] using wordTrace_append hprefix tailTrace_6913409
  have hstable : (prefixWord ++ tailWord_6913409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913409).length < 2 ^ (prefixWord ++ tailWord_6913409).sum := by decide
  have hdescent : baseEnd_6913409 < baseStart_6913409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913425 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 3, 6, 2]
def baseStart_6913425 : Nat := 118140960795 + 6913425 * 2 ^ 59
def prefixEnd_6913425 : Nat := 4983230072969 + 3 ^ 40 * 6913425 * 2
def baseEnd_6913425 : Nat := 3549909993809718926593243

theorem tailTrace_6913425 : CollatzResearch.WordTrace tailWord_6913425 prefixEnd_6913425 3549909993809718926593243 := by
  unfold tailWord_6913425
  simp only [CollatzResearch.WordTrace]
  refine ⟨252153324978849418833269729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168102216652566279222179819 252153324978849418833269729)
  ·
    refine ⟨189114993734137064124952297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252153324978849418833269729 189114993734137064124952297)
    ·
      refine ⟨141836245300602798093714223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189114993734137064124952297 141836245300602798093714223)
      ·
        refine ⟨212754367950904197140571335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141836245300602798093714223 212754367950904197140571335)
        ·
          refine ⟨319131551926356295710857003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212754367950904197140571335 319131551926356295710857003)
          ·
            refine ⟨478697327889534443566285505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319131551926356295710857003 478697327889534443566285505)
            ·
              refine ⟨359022995917150832674714129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478697327889534443566285505 359022995917150832674714129)
              ·
                refine ⟨269267246937863124506035597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359022995917150832674714129 269267246937863124506035597)
                ·
                  refine ⟨100975217601698671689763349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269267246937863124506035597 100975217601698671689763349)
                  ·
                    refine ⟨4733213325079625235457657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100975217601698671689763349 4733213325079625235457657)
                    ·
                      refine ⟨3549909993809718926593243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733213325079625235457657 3549909993809718926593243)
                      ·
                        rfl

theorem cell23_6913425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_6913425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913425 prefixEnd_6913425 := by exact prefixLift 6913425
  have htrace : WordTrace (prefixWord ++ tailWord_6913425) baseStart_6913425 baseEnd_6913425 := by
    simpa [prefixWord, tailWord_6913425, baseEnd_6913425] using wordTrace_append hprefix tailTrace_6913425
  have hstable : (prefixWord ++ tailWord_6913425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913425).length < 2 ^ (prefixWord ++ tailWord_6913425).sum := by decide
  have hdescent : baseEnd_6913425 < baseStart_6913425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913445 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_6913445 : Nat := 118140960795 + 6913445 * 2 ^ 59
def prefixEnd_6913445 : Nat := 4983230072969 + 3 ^ 40 * 6913445 * 2
def baseEnd_6913445 : Nat := 3549920263422808848343151

theorem tailTrace_6913445 : CollatzResearch.WordTrace tailWord_6913445 prefixEnd_6913445 3549920263422808848343151 := by
  unfold tailWord_6913445
  simp only [CollatzResearch.WordTrace]
  refine ⟨252154054438776962248997789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168102702959184641499331859 252154054438776962248997789)
  ·
    refine ⟨94557770414541360843374171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252154054438776962248997789 94557770414541360843374171)
    ·
      refine ⟨141836655621812041265061257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94557770414541360843374171 141836655621812041265061257)
      ·
        refine ⟨106377491716359030948795943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141836655621812041265061257 106377491716359030948795943)
        ·
          refine ⟨159566237574538546423193915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106377491716359030948795943 159566237574538546423193915)
          ·
            refine ⟨239349356361807819634790873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159566237574538546423193915 239349356361807819634790873)
            ·
              refine ⟨179512017271355864726093155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239349356361807819634790873 179512017271355864726093155)
              ·
                refine ⟨269268025907033797089139733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179512017271355864726093155 269268025907033797089139733)
                ·
                  refine ⟨12621938714392209238553425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269268025907033797089139733 12621938714392209238553425)
                  ·
                    refine ⟨9466454035794156928915069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12621938714392209238553425 9466454035794156928915069)
                    ·
                      refine ⟨3549920263422808848343151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9466454035794156928915069 3549920263422808848343151)
                      ·
                        rfl

theorem cell23_6913445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_6913445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913445 prefixEnd_6913445 := by exact prefixLift 6913445
  have htrace : WordTrace (prefixWord ++ tailWord_6913445) baseStart_6913445 baseEnd_6913445 := by
    simpa [prefixWord, tailWord_6913445, baseEnd_6913445] using wordTrace_append hprefix tailTrace_6913445
  have hstable : (prefixWord ++ tailWord_6913445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913445).length < 2 ^ (prefixWord ++ tailWord_6913445).sum := by decide
  have hdescent : baseEnd_6913445 < baseStart_6913445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913532 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_6913532 : Nat := 118140960795 + 6913532 * 2 ^ 59
def prefixEnd_6913532 : Nat := 4983230072969 + 3 ^ 40 * 6913532 * 2
def baseEnd_6913532 : Nat := 3549964936239750007955251

theorem tailTrace_6913532 : CollatzResearch.WordTrace tailWord_6913532 prefixEnd_6913532 3549964936239750007955251 := by
  unfold tailWord_6913532
  simp only [CollatzResearch.WordTrace]
  refine ⟨126078613794730888053707425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168104818392974517404943233 126078613794730888053707425)
  ·
    refine ⟨94558960346048166040280569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126078613794730888053707425 94558960346048166040280569)
    ·
      refine ⟨70919220259536124530210427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94558960346048166040280569 70919220259536124530210427)
      ·
        refine ⟨106378830389304186795315641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70919220259536124530210427 106378830389304186795315641)
        ·
          refine ⟨79784122791978140096486731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106378830389304186795315641 79784122791978140096486731)
          ·
            refine ⟨119676184187967210144730097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79784122791978140096486731 119676184187967210144730097)
            ·
              refine ⟨89757138140975407608547573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119676184187967210144730097 89757138140975407608547573)
              ·
                refine ⟨8414731700716444463301335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89757138140975407608547573 8414731700716444463301335)
                ·
                  refine ⟨12622097551074666694952003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8414731700716444463301335 12622097551074666694952003)
                  ·
                    refine ⟨18933146326612000042428005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12622097551074666694952003 18933146326612000042428005)
                    ·
                      refine ⟨3549964936239750007955251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18933146326612000042428005 3549964936239750007955251)
                      ·
                        rfl

theorem cell23_6913532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_6913532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913532 prefixEnd_6913532 := by exact prefixLift 6913532
  have htrace : WordTrace (prefixWord ++ tailWord_6913532) baseStart_6913532 baseEnd_6913532 := by
    simpa [prefixWord, tailWord_6913532, baseEnd_6913532] using wordTrace_append hprefix tailTrace_6913532
  have hstable : (prefixWord ++ tailWord_6913532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913532).length < 2 ^ (prefixWord ++ tailWord_6913532).sum := by decide
  have hdescent : baseEnd_6913532 < baseStart_6913532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913535 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_6913535 : Nat := 118140960795 + 6913535 * 2 ^ 59
def prefixEnd_6913535 : Nat := 4983230072969 + 3 ^ 40 * 6913535 * 2
def baseEnd_6913535 : Nat := 3549966476681713496217737

theorem tailTrace_6913535 : CollatzResearch.WordTrace tailWord_6913535 prefixEnd_6913535 3549966476681713496217737 := by
  unfold tailWord_6913535
  simp only [CollatzResearch.WordTrace]
  refine ⟨252157337008450907619774059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168104891338967271746516039 252157337008450907619774059)
  ·
    refine ⟨378236005512676361429661089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252157337008450907619774059 378236005512676361429661089)
    ·
      refine ⟨283677004134507271072245817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378236005512676361429661089 283677004134507271072245817)
      ·
        refine ⟨212757753100880453304184363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283677004134507271072245817 212757753100880453304184363)
        ·
          refine ⟨319136629651320679956276545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212757753100880453304184363 319136629651320679956276545)
          ·
            refine ⟨239352472238490509967207409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319136629651320679956276545 239352472238490509967207409)
            ·
              refine ⟨179514354178867882475405557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239352472238490509967207409 179514354178867882475405557)
              ·
                refine ⟨16829470704268863982069271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179514354178867882475405557 16829470704268863982069271)
                ·
                  refine ⟨25244206056403295973103907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16829470704268863982069271 25244206056403295973103907)
                  ·
                    refine ⟨37866309084604943959655861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25244206056403295973103907 37866309084604943959655861)
                    ·
                      refine ⟨3549966476681713496217737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37866309084604943959655861 3549966476681713496217737)
                      ·
                        rfl

theorem cell23_6913535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_6913535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913535 prefixEnd_6913535 := by exact prefixLift 6913535
  have htrace : WordTrace (prefixWord ++ tailWord_6913535) baseStart_6913535 baseEnd_6913535 := by
    simpa [prefixWord, tailWord_6913535, baseEnd_6913535] using wordTrace_append hprefix tailTrace_6913535
  have hstable : (prefixWord ++ tailWord_6913535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913535).length < 2 ^ (prefixWord ++ tailWord_6913535).sum := by decide
  have hdescent : baseEnd_6913535 < baseStart_6913535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913543 : List Nat := [1, 1, 4, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_6913543 : Nat := 118140960795 + 6913543 * 2 ^ 59
def prefixEnd_6913543 : Nat := 4983230072969 + 3 ^ 40 * 6913543 * 2
def baseEnd_6913543 : Nat := 3549970584526949464917701

theorem tailTrace_6913543 : CollatzResearch.WordTrace tailWord_6913543 prefixEnd_6913543 3549970584526949464917701 := by
  unfold tailWord_6913543
  simp only [CollatzResearch.WordTrace]
  refine ⟨252157628792421924986065283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168105085861614616657376855 252157628792421924986065283)
  ·
    refine ⟨378236443188632887479097925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252157628792421924986065283 378236443188632887479097925)
    ·
      refine ⟨70919333097868666402330861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 378236443188632887479097925 70919333097868666402330861)
      ·
        refine ⟨26594749911700749900874073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70919333097868666402330861 26594749911700749900874073)
        ·
          refine ⟨19946062433775562425655555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26594749911700749900874073 19946062433775562425655555)
          ·
            refine ⟨29919093650663343638483333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19946062433775562425655555 29919093650663343638483333)
            ·
              refine ⟨5609830059499376932215625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29919093650663343638483333 5609830059499376932215625)
              ·
                refine ⟨4207372544624532699161719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5609830059499376932215625 4207372544624532699161719)
                ·
                  refine ⟨6311058816936799048742579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207372544624532699161719 6311058816936799048742579)
                  ·
                    refine ⟨9466588225405198573113869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6311058816936799048742579 9466588225405198573113869)
                    ·
                      refine ⟨3549970584526949464917701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9466588225405198573113869 3549970584526949464917701)
                      ·
                        rfl

theorem cell23_6913543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_6913543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913543 prefixEnd_6913543 := by exact prefixLift 6913543
  have htrace : WordTrace (prefixWord ++ tailWord_6913543) baseStart_6913543 baseEnd_6913543 := by
    simpa [prefixWord, tailWord_6913543, baseEnd_6913543] using wordTrace_append hprefix tailTrace_6913543
  have hstable : (prefixWord ++ tailWord_6913543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913543).length < 2 ^ (prefixWord ++ tailWord_6913543).sum := by decide
  have hdescent : baseEnd_6913543 < baseStart_6913543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913545 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_6913545 : Nat := 118140960795 + 6913545 * 2 ^ 59
def prefixEnd_6913545 : Nat := 4983230072969 + 3 ^ 40 * 6913545 * 2
def baseEnd_6913545 : Nat := 3549971611488258457092691

theorem tailTrace_6913545 : CollatzResearch.WordTrace tailWord_6913545 prefixEnd_6913545 3549971611488258457092691 := by
  unfold tailWord_6913545
  simp only [CollatzResearch.WordTrace]
  refine ⟨252157701738414679327638089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168105134492276452885092059 252157701738414679327638089)
  ·
    refine ⟨189118276303811009495728567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252157701738414679327638089 189118276303811009495728567)
    ·
      refine ⟨283677414455716514243592851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189118276303811009495728567 283677414455716514243592851)
      ·
        refine ⟨425516121683574771365389277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283677414455716514243592851 425516121683574771365389277)
        ·
          refine ⟨159568545631340539262020979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425516121683574771365389277 159568545631340539262020979)
          ·
            refine ⟨239352818447010808893031469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159568545631340539262020979 239352818447010808893031469)
            ·
              refine ⟨89757306917629053334886801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239352818447010808893031469 89757306917629053334886801)
              ·
                refine ⟨67317980188221790001165101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89757306917629053334886801 67317980188221790001165101)
                ·
                  refine ⟨25244242570583171250436913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67317980188221790001165101 25244242570583171250436913)
                  ·
                    refine ⟨18933181927937378437827685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25244242570583171250436913 18933181927937378437827685)
                    ·
                      refine ⟨3549971611488258457092691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18933181927937378437827685 3549971611488258457092691)
                      ·
                        rfl

theorem cell23_6913545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_6913545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913545 prefixEnd_6913545 := by exact prefixLift 6913545
  have htrace : WordTrace (prefixWord ++ tailWord_6913545) baseStart_6913545 baseEnd_6913545 := by
    simpa [prefixWord, tailWord_6913545, baseEnd_6913545] using wordTrace_append hprefix tailTrace_6913545
  have hstable : (prefixWord ++ tailWord_6913545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913545).length < 2 ^ (prefixWord ++ tailWord_6913545).sum := by decide
  have hdescent : baseEnd_6913545 < baseStart_6913545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913555 : List Nat := [1, 1, 1, 2, 1, 6, 3, 8]
def baseStart_6913555 : Nat := 118140960795 + 6913555 * 2 ^ 59
def prefixEnd_6913555 : Nat := 4983230072969 + 3 ^ 40 * 6913555 * 2
def baseEnd_6913555 : Nat := 131480620233140867332135

theorem tailTrace_6913555 : CollatzResearch.WordTrace tailWord_6913555 prefixEnd_6913555 131480620233140867332135 := by
  unfold tailWord_6913555
  simp only [CollatzResearch.WordTrace]
  refine ⟨252158066468378451035502119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168105377645585634023668079 252158066468378451035502119)
  ·
    refine ⟨378237099702567676553253179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252158066468378451035502119 378237099702567676553253179)
    ·
      refine ⟨567355649553851514829879769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378237099702567676553253179 567355649553851514829879769)
      ·
        refine ⟨425516737165388636122409827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567355649553851514829879769 425516737165388636122409827)
        ·
          refine ⟨638275105748082954183614741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425516737165388636122409827 638275105748082954183614741)
          ·
            refine ⟨29919145581941388477356941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 638275105748082954183614741 29919145581941388477356941)
            ·
              refine ⟨11219679593228020679008853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29919145581941388477356941 11219679593228020679008853)
              ·
                refine ⟨131480620233140867332135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11219679593228020679008853 131480620233140867332135)
                ·
                  rfl

theorem cell23_6913555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 8].length) (baseStart_6913555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913555 prefixEnd_6913555 := by exact prefixLift 6913555
  have htrace : WordTrace (prefixWord ++ tailWord_6913555) baseStart_6913555 baseEnd_6913555 := by
    simpa [prefixWord, tailWord_6913555, baseEnd_6913555] using wordTrace_append hprefix tailTrace_6913555
  have hstable : (prefixWord ++ tailWord_6913555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913555).length < 2 ^ (prefixWord ++ tailWord_6913555).sum := by decide
  have hdescent : baseEnd_6913555 < baseStart_6913555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913599 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 3]
def baseStart_6913599 : Nat := 118140960795 + 6913599 * 2 ^ 59
def prefixEnd_6913599 : Nat := 4983230072969 + 3 ^ 40 * 6913599 * 2
def baseEnd_6913599 : Nat := 3549999339443601245817443

theorem tailTrace_6913599 : CollatzResearch.WordTrace tailWord_6913599 prefixEnd_6913599 3549999339443601245817443 := by
  unfold tailWord_6913599
  simp only [CollatzResearch.WordTrace]
  refine ⟨252159671280219046550103851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168106447520146031033402567 252159671280219046550103851)
  ·
    refine ⟨378239506920328569825155777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252159671280219046550103851 378239506920328569825155777)
    ·
      refine ⟨283679630190246427368866833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378239506920328569825155777 283679630190246427368866833)
      ·
        refine ⟨212759722642684820526650125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283679630190246427368866833 212759722642684820526650125)
        ·
          refine ⟨79784895991006807697493797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212759722642684820526650125 79784895991006807697493797)
          ·
            refine ⟨14959667998313776443280087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79784895991006807697493797 14959667998313776443280087)
            ·
              refine ⟨22439501997470664664920131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14959667998313776443280087 22439501997470664664920131)
              ·
                refine ⟨33659252996205996997380197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22439501997470664664920131 33659252996205996997380197)
                ·
                  refine ⟨6311109936788624437008787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33659252996205996997380197 6311109936788624437008787)
                  ·
                    refine ⟨9466664905182936655513181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6311109936788624437008787 9466664905182936655513181)
                    ·
                      refine ⟨3549999339443601245817443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9466664905182936655513181 3549999339443601245817443)
                      ·
                        rfl

theorem cell23_6913599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_6913599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913599 prefixEnd_6913599 := by exact prefixLift 6913599
  have htrace : WordTrace (prefixWord ++ tailWord_6913599) baseStart_6913599 baseEnd_6913599 := by
    simpa [prefixWord, tailWord_6913599, baseEnd_6913599] using wordTrace_append hprefix tailTrace_6913599
  have hstable : (prefixWord ++ tailWord_6913599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913599).length < 2 ^ (prefixWord ++ tailWord_6913599).sum := by decide
  have hdescent : baseEnd_6913599 < baseStart_6913599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913613 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_6913613 : Nat := 118140960795 + 6913613 * 2 ^ 59
def prefixEnd_6913613 : Nat := 4983230072969 + 3 ^ 40 * 6913613 * 2
def baseEnd_6913613 : Nat := 3550006528172764191042379

theorem tailTrace_6913613 : CollatzResearch.WordTrace tailWord_6913613 prefixEnd_6913613 3550006528172764191042379 := by
  unfold tailWord_6913613
  simp only [CollatzResearch.WordTrace]
  refine ⟨252160181902168326941113493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168106787934778884627408995 252160181902168326941113493)
  ·
    refine ⟨11820008526664140325364695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252160181902168326941113493 11820008526664140325364695)
    ·
      refine ⟨17730012789996210488047043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11820008526664140325364695 17730012789996210488047043)
      ·
        refine ⟨26595019184994315732070565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17730012789996210488047043 26595019184994315732070565)
        ·
          refine ⟨4986566097186434199763231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26595019184994315732070565 4986566097186434199763231)
          ·
            refine ⟨7479849145779651299644847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4986566097186434199763231 7479849145779651299644847)
            ·
              refine ⟨11219773718669476949467271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7479849145779651299644847 11219773718669476949467271)
              ·
                refine ⟨16829660578004215424200907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11219773718669476949467271 16829660578004215424200907)
                ·
                  refine ⟨25244490867006323136301361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16829660578004215424200907 25244490867006323136301361)
                  ·
                    refine ⟨18933368150254742352226021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25244490867006323136301361 18933368150254742352226021)
                    ·
                      refine ⟨3550006528172764191042379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18933368150254742352226021 3550006528172764191042379)
                      ·
                        rfl

theorem cell23_6913613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_6913613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913613 prefixEnd_6913613 := by exact prefixLift 6913613
  have htrace : WordTrace (prefixWord ++ tailWord_6913613) baseStart_6913613 baseEnd_6913613 := by
    simpa [prefixWord, tailWord_6913613, baseEnd_6913613] using wordTrace_append hprefix tailTrace_6913613
  have hstable : (prefixWord ++ tailWord_6913613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913613).length < 2 ^ (prefixWord ++ tailWord_6913613).sum := by decide
  have hdescent : baseEnd_6913613 < baseStart_6913613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913616 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 2, 1, 3]
def baseStart_6913616 : Nat := 118140960795 + 6913616 * 2 ^ 59
def prefixEnd_6913616 : Nat := 4983230072969 + 3 ^ 40 * 6913616 * 2
def baseEnd_6913616 : Nat := 3550008068614727679304865

theorem tailTrace_6913616 : CollatzResearch.WordTrace tailWord_6913616 prefixEnd_6913616 3550008068614727679304865 := by
  unfold tailWord_6913616
  simp only [CollatzResearch.WordTrace]
  refine ⟨126080145660578729226736351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168106860880771638968981801 126080145660578729226736351)
  ·
    refine ⟨189120218490868093840104527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126080145660578729226736351 189120218490868093840104527)
    ·
      refine ⟨283680327736302140760156791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189120218490868093840104527 283680327736302140760156791)
      ·
        refine ⟨425520491604453211140235187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283680327736302140760156791 425520491604453211140235187)
        ·
          refine ⟨638280737406679816710352781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425520491604453211140235187 638280737406679816710352781)
          ·
            refine ⟨239355276527504931266382293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 638280737406679816710352781 239355276527504931266382293)
            ·
              refine ⟨5609889293613396826555835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239355276527504931266382293 5609889293613396826555835)
              ·
                refine ⟨8414833940420095239833753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609889293613396826555835 8414833940420095239833753)
                ·
                  refine ⟨6311125455315071429875315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8414833940420095239833753 6311125455315071429875315)
                  ·
                    refine ⟨9466688182972607144812973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6311125455315071429875315 9466688182972607144812973)
                    ·
                      refine ⟨3550008068614727679304865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9466688182972607144812973 3550008068614727679304865)
                      ·
                        rfl

theorem cell23_6913616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 1, 3].length) (baseStart_6913616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913616 prefixEnd_6913616 := by exact prefixLift 6913616
  have htrace : WordTrace (prefixWord ++ tailWord_6913616) baseStart_6913616 baseEnd_6913616 := by
    simpa [prefixWord, tailWord_6913616, baseEnd_6913616] using wordTrace_append hprefix tailTrace_6913616
  have hstable : (prefixWord ++ tailWord_6913616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913616).length < 2 ^ (prefixWord ++ tailWord_6913616).sum := by decide
  have hdescent : baseEnd_6913616 < baseStart_6913616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913625 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_6913625 : Nat := 118140960795 + 6913625 * 2 ^ 59
def prefixEnd_6913625 : Nat := 4983230072969 + 3 ^ 40 * 6913625 * 2
def baseEnd_6913625 : Nat := 3550012689940618144092323

theorem tailTrace_6913625 : CollatzResearch.WordTrace tailWord_6913625 prefixEnd_6913625 3550012689940618144092323 := by
  unfold tailWord_6913625
  simp only [CollatzResearch.WordTrace]
  refine ⟨252160619578124852990550329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168107079718749901993700219 252160619578124852990550329)
  ·
    refine ⟨189120464683593639742912747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252160619578124852990550329 189120464683593639742912747)
    ·
      refine ⟨283680697025390459614369121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189120464683593639742912747 283680697025390459614369121)
      ·
        refine ⟨212760522769042844710776841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283680697025390459614369121 212760522769042844710776841)
        ·
          refine ⟨159570392076782133533082631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212760522769042844710776841 159570392076782133533082631)
          ·
            refine ⟨239355588115173200299623947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159570392076782133533082631 239355588115173200299623947)
            ·
              refine ⟨359033382172759800449435921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239355588115173200299623947 359033382172759800449435921)
              ·
                refine ⟨269275036629569850337076941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359033382172759800449435921 269275036629569850337076941)
                ·
                  refine ⟨100978138736088693876403853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269275036629569850337076941 100978138736088693876403853)
                  ·
                    refine ⟨37866802026033260203651445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100978138736088693876403853 37866802026033260203651445)
                    ·
                      refine ⟨3550012689940618144092323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37866802026033260203651445 3550012689940618144092323)
                      ·
                        rfl

theorem cell23_6913625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_6913625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913625 prefixEnd_6913625 := by exact prefixLift 6913625
  have htrace : WordTrace (prefixWord ++ tailWord_6913625) baseStart_6913625 baseEnd_6913625 := by
    simpa [prefixWord, tailWord_6913625, baseEnd_6913625] using wordTrace_append hprefix tailTrace_6913625
  have hstable : (prefixWord ++ tailWord_6913625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913625).length < 2 ^ (prefixWord ++ tailWord_6913625).sum := by decide
  have hdescent : baseEnd_6913625 < baseStart_6913625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913639 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_6913639 : Nat := 118140960795 + 6913639 * 2 ^ 59
def prefixEnd_6913639 : Nat := 4983230072969 + 3 ^ 40 * 6913639 * 2
def baseEnd_6913639 : Nat := 3550019878669781089317259

theorem tailTrace_6913639 : CollatzResearch.WordTrace tailWord_6913639 prefixEnd_6913639 3550019878669781089317259 := by
  unfold tailWord_6913639
  simp only [CollatzResearch.WordTrace]
  refine ⟨252161130200074133381559971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168107420133382755587706647 252161130200074133381559971)
  ·
    refine ⟨378241695300111200072339957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252161130200074133381559971 378241695300111200072339957)
    ·
      refine ⟨35460158934385425006781871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 378241695300111200072339957 35460158934385425006781871)
      ·
        refine ⟨53190238401578137510172807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35460158934385425006781871 53190238401578137510172807)
        ·
          refine ⟨79785357602367206265259211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53190238401578137510172807 79785357602367206265259211)
          ·
            refine ⟨119678036403550809397888817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79785357602367206265259211 119678036403550809397888817)
            ·
              refine ⟨89758527302663107048416613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119678036403550809397888817 89758527302663107048416613)
              ·
                refine ⟨16829723869249332571578115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89758527302663107048416613 16829723869249332571578115)
                ·
                  refine ⟨25244585803873998857367173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16829723869249332571578115 25244585803873998857367173)
                  ·
                    refine ⟨4733359838226374785756345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25244585803873998857367173 4733359838226374785756345)
                    ·
                      refine ⟨3550019878669781089317259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4733359838226374785756345 3550019878669781089317259)
                      ·
                        rfl

theorem cell23_6913639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_6913639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913639 prefixEnd_6913639 := by exact prefixLift 6913639
  have htrace : WordTrace (prefixWord ++ tailWord_6913639) baseStart_6913639 baseEnd_6913639 := by
    simpa [prefixWord, tailWord_6913639, baseEnd_6913639] using wordTrace_append hprefix tailTrace_6913639
  have hstable : (prefixWord ++ tailWord_6913639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913639).length < 2 ^ (prefixWord ++ tailWord_6913639).sum := by decide
  have hdescent : baseEnd_6913639 < baseStart_6913639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6913642 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6913642 : Nat := 118140960795 + 6913642 * 2 ^ 59
def prefixEnd_6913642 : Nat := 4983230072969 + 3 ^ 40 * 6913642 * 2
def baseEnd_6913642 : Nat := 3550021419111744577579745

theorem tailTrace_6913642 : CollatzResearch.WordTrace tailWord_6913642 prefixEnd_6913642 3550021419111744577579745 := by
  unfold tailWord_6913642
  simp only [CollatzResearch.WordTrace]
  refine ⟨63040309904765816223479795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168107493079375509929279453 63040309904765816223479795)
  ·
    refine ⟨94560464857148724335219693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63040309904765816223479795 94560464857148724335219693)
    ·
      refine ⟨35460174321430771625707385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94560464857148724335219693 35460174321430771625707385)
      ·
        refine ⟨26595130741073078719280539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35460174321430771625707385 26595130741073078719280539)
        ·
          refine ⟨39892696111609618078920809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26595130741073078719280539 39892696111609618078920809)
          ·
            refine ⟨29919522083707213559190607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39892696111609618078920809 29919522083707213559190607)
            ·
              refine ⟨44879283125560820338785911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29919522083707213559190607 44879283125560820338785911)
              ·
                refine ⟨67318924688341230508178867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44879283125560820338785911 67318924688341230508178867)
                ·
                  refine ⟨100978387032511845762268301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67318924688341230508178867 100978387032511845762268301)
                  ·
                    refine ⟨37866895137191942160850613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100978387032511845762268301 37866895137191942160850613)
                    ·
                      refine ⟨3550021419111744577579745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37866895137191942160850613 3550021419111744577579745)
                      ·
                        rfl

theorem cell23_6913642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6913642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6913642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6913642 prefixEnd_6913642 := by exact prefixLift 6913642
  have htrace : WordTrace (prefixWord ++ tailWord_6913642) baseStart_6913642 baseEnd_6913642 := by
    simpa [prefixWord, tailWord_6913642, baseEnd_6913642] using wordTrace_append hprefix tailTrace_6913642
  have hstable : (prefixWord ++ tailWord_6913642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6913642).length < 2 ^ (prefixWord ++ tailWord_6913642).sum := by decide
  have hdescent : baseEnd_6913642 < baseStart_6913642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6913642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
